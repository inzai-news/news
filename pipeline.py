"""印西ニュース 統合パイプライン

サブコマンド:
  collect        ソース収集。ルールベースで判定できるものは news.json に直接反映し、
                 重複グレーゾーン(70-79%)・カテゴリ未確定の記事は review_queue.json に書き出す。
  apply-review   review_queue.json (decision/category を記入済み) を反映して news.json を確定する。
  build          news.json から index.html を生成する。
  publish        変更を git add/commit/push する。
  store-pending  開店閉店.txt の未処理店舗一覧を表示する(6か月経過店舗は自動削除)。
  store-add      調査済みの開店閉店情報を1件 news.json に登録する。
  store-star     開店閉店.txt の店舗に★(調査不能スキップ)を付与する。

実行方法: python pipeline.py <サブコマンド> [オプション]
"""
import argparse
import calendar
import difflib
import html
import json
import os
import re
import subprocess
import sys
import time
import unicodedata
import xml.etree.ElementTree as ET
from datetime import date, datetime, timedelta, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path
from urllib.parse import urljoin, urlparse
from collections import defaultdict

import requests
from bs4 import BeautifulSoup

sys.stdout.reconfigure(encoding="utf-8", line_buffering=True)
sys.stderr.reconfigure(encoding="utf-8", line_buffering=True)

BASE_DIR = Path(__file__).parent
SOURCES_PATH = BASE_DIR / "sources.json"
NEWS_PATH = BASE_DIR / "news.json"
REVIEW_QUEUE_PATH = BASE_DIR / "review_queue.json"
AI_LOG_PATH = BASE_DIR / "ai_check_log.json"
NEW_BADGE_PATH = BASE_DIR / "new_badge.json"
STORE_LIST_PATH = BASE_DIR / "開店閉店.txt"
INDEX_HTML_PATH = BASE_DIR / "index.html"
SITEMAP_PATH = BASE_DIR / "sitemap.xml"
ROBOTS_PATH = BASE_DIR / "robots.txt"
TOKEN_PATH = BASE_DIR / ".gh_token"
GITHUB_REPO = "inzai-news/news"
SITE_URL = "https://inzai-news.github.io/news/"

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
        "(KHTML, like Gecko) Chrome/120.0 Safari/537.36"
    )
}
TIMEOUT = 15
JST = timezone(timedelta(hours=9))

CATEGORY_ORDER = ["市政・行政", "話題・その他", "イベント・文化", "開発・暮らし", "開店・閉店", "鎌ヶ谷・白井", "ジョイフル本田千葉ニュータウン店", "イオンモール千葉ニュータウン", "牧の原モア"]
KAITEN_KEYWORDS = ["開店", "閉店", "オープン", "クローズ", "NEW OPEN", "new open"]

REGULAR_RETENTION_MONTHS = 3
STORE_EVENT_RETENTION_MONTHS = 6
STORE_EVENT_TITLE_PATTERN = re.compile(r"^【(\d{4})年(\d{1,2})月(\d{1,2})日\s+(開店|閉店|リニューアル)】")
EVENT_END_GRACE_DAYS = 3

DUP_AUTO_EXCLUDE_THRESHOLD = 0.8
DUP_REVIEW_THRESHOLD = 0.7
DUP_COMPARE_WINDOW_DAYS = 30

RENEWAL_CATEGORY_LABELS = {"新店": "開店", "閉店": "閉店", "リニューアル": "リニューアル"}

# 印西市の天気予報(ウェザーニューズ)
WEATHER_SITE_URL = "https://weathernews.jp/onebox/tenki/chiba/12231/?tab=3"
WEATHER_FETCH_URL = "https://weathernews.jp/onebox/tenki/chiba/12231/week.html?tab=4"

# カテゴリ未確定の記事(主にGoogle News経由)に対する、タイトルからの機械的カテゴリ推定。
# ここで判定できないものだけをAI判断(review_queue)に回し、AIへの負荷を抑える。
CATEGORY_KEYWORD_RULES = [
    ("開店・閉店", ["開店", "閉店", "オープン", "OPEN", "open", "クローズ", "close", "移転", "新規出店", "リニューアルオープン"]),
    ("鎌ヶ谷・白井", ["鎌ケ谷", "鎌ヶ谷", "白井市", "白井駅"]),
    ("イオンモール千葉ニュータウン", ["イオンモール", "AEON MALL", "aeonmall", "チバニュータウン", "千葉ニュータウン中央"]),
    ("市政・行政", ["市議会", "市役所", "市政", "市長", "条例", "予算案", "補正予算", "選挙", "行政", "助成金", "補助金", "住民票", "議案"]),
    ("イベント・文化", ["まつり", "祭り", "フェス", "フェスタ", "展示会", "展覧会", "コンサート", "ワークショップ", "講座", "教室", "花火", "マルシェ", "イベント"]),
    ("開発・暮らし", ["データセンター", "再開発", "宅地", "分譲", "駅前", "都市計画", "道路", "子育て", "保育", "ごみ", "防災", "交通"]),
]


def guess_category_from_title(title: str):
    for category, keywords in CATEGORY_KEYWORD_RULES:
        if any(kw in title for kw in keywords):
            return category
    return None


# Google Newsのキーワード検索は関連度が緩く、印西と無関係な記事(他地域のチェーン店開店情報や
# 全く関係ないニュース)が混ざる。タイトルにこれらの地域キーワードが1つも無い記事は対象外として除外する。
LOCAL_AREA_KEYWORDS = [
    "印西", "牧の原", "千葉ニュータウン", "チバニュータウン", "鎌ケ谷", "鎌ヶ谷",
    "白井市", "白井駅", "印旛", "木下駅", "小林駅", "大森駅",
]


def is_locally_relevant(title: str) -> bool:
    return any(kw in title for kw in LOCAL_AREA_KEYWORDS)


# ============================================================
# 共通ユーティリティ
# ============================================================

def to_pub_str(year, month, day) -> str:
    return f"{int(year)}年{int(month)}月{int(day)}日"


def parse_pub_str(pub_str: str):
    m = re.match(r"(\d{4})年(\d{1,2})月(\d{1,2})日", pub_str or "")
    if not m:
        return None
    y, mo, d = map(int, m.groups())
    return date(y, mo, d)


def months_ago(base: date, months: int) -> date:
    month = base.month - months
    year = base.year
    while month <= 0:
        month += 12
        year -= 1
    day = min(base.day, calendar.monthrange(year, month)[1])
    return date(year, month, day)


def is_store_event_title(title: str) -> bool:
    return bool(STORE_EVENT_TITLE_PATTERN.match(title or ""))


def extract_store_event_name(title: str):
    """開店・閉店店舗の定型タイトル「【YYYY年M月D日 種別】店名」から店名部分だけを取り出す。
    定型タイトルでなければNoneを返す。collect時、通常収集された自然文タイトルの記事が
    既存のstore-add登録(store_event)と同一店舗の話かどうかを、タイトル類似度とは別に
    店名の部分一致で判定するために使う(店名を含むだけの定型タイトルは自然文タイトルとの
    類似度が低く出るため、通常のtitle_similarityだけでは同一店舗の記事を見つけられない)。
    """
    m = STORE_EVENT_TITLE_PATTERN.match(title or "")
    return title[m.end():].strip() if m else None


def compute_retention_type(item: dict) -> str:
    return "store_event" if is_store_event_title(item.get("title", "")) else "regular"


def is_expired(item: dict, today=None) -> bool:
    """通常記事は3か月、開店閉店情報(retention_type=store_event)は6か月より古ければTrue。
    通常記事が未来日付になっているのはパースミスとみなして除外対象とする
    (開店閉店情報は開店/閉店の予定日を使うため未来日付でも正常なので対象外)。
    event_end_date(イベント開催終了日)を持つ記事は、そこから3日経過したら
    上記のリテンション期間によらず期限切れとする(掲載期限より優先)。
    """
    if today is None:
        today = date.today()
    event_end = item.get("event_end_date")
    if event_end:
        try:
            if today > date.fromisoformat(event_end) + timedelta(days=EVENT_END_GRACE_DAYS):
                return True
        except ValueError:
            pass
    pub_date = parse_pub_str(item.get("pub_str", ""))
    if pub_date is None:
        return False
    is_store_event = item.get("retention_type") == "store_event"
    if not is_store_event and pub_date > today:
        return True
    retention_months = STORE_EVENT_RETENTION_MONTHS if is_store_event else REGULAR_RETENTION_MONTHS
    cutoff = months_ago(today, retention_months)
    return pub_date < cutoff


def title_similarity(a: str, b: str) -> float:
    return difflib.SequenceMatcher(None, a or "", b or "").ratio()


def save_json_atomic(path: Path, data) -> None:
    """一時ファイル経由でアトミックに書き込み、直後に読み直して破損がないか検証する"""
    path.parent.mkdir(parents=True, exist_ok=True)
    body = json.dumps(data, ensure_ascii=False, indent=2)
    tmp_path = path.with_name(path.name + ".tmp")
    with tmp_path.open("w", encoding="utf-8") as f:
        f.write(body)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp_path, path)
    with path.open(encoding="utf-8") as f:
        json.load(f)


def load_json(path: Path, default):
    if not path.exists():
        return default
    with path.open(encoding="utf-8") as f:
        return json.load(f)


def load_news() -> list:
    return load_json(NEWS_PATH, [])


def load_sources() -> dict:
    return load_json(SOURCES_PATH, {"html_scrapers": [], "rss_sources": [], "blocked_publishers": []})


def append_ai_log(entries: list) -> None:
    if not entries:
        return
    log = load_json(AI_LOG_PATH, [])
    log.extend(entries)
    save_json_atomic(AI_LOG_PATH, log)


def load_excluded_links() -> set:
    """過去にルールベース/AI判断で除外(exclude)されたリンクの集合。
    HTMLスクレイパー等、同じ記事が毎回トップページに載り続けるソース向けに、
    一度除外判定した記事を次回collect以降も再度重複判定・AIレビューにかけないための記憶。
    """
    log = load_json(AI_LOG_PATH, [])
    return {e["link"] for e in log if e.get("ai_decision") in ("auto_exclude", "exclude")}


NEW_BADGE_WINDOW_HOURS = 3


def load_new_badge_data() -> dict:
    """「新着」バッジの状態を読み込む。形式は
    {"links": {リンク: 追加日時(JST ISO文字列)}, "last_eligible": {"link":.., "ts":..} or None}。
    "links"がNEW_BADGE_WINDOW_HOURS(3時間)以内の通常バッジ、"last_eligible"は
    印西市役所等の新着除外対象を除いた直近1件を3時間を過ぎても保持するフォールバック枠
    (「最後の更新が新着で分かるようにする」という本来の目的を、除外対象しか
    追加されなかった更新回でも満たすための仕組み)。
    旧形式(フラットな{link:ts}辞書、またはリストのみ)が残っていた場合は
    linksとして引き継ぎ、last_eligibleは次回更新で自然に設定されるまでNoneとする。
    """
    data = load_json(NEW_BADGE_PATH, {})
    if isinstance(data, list):
        return {"links": {}, "last_eligible": None}
    if "links" not in data:
        return {"links": data, "last_eligible": None}
    return data


def save_new_badge_data(data: dict) -> None:
    save_json_atomic(NEW_BADGE_PATH, data)


def mark_new_badge_links(new_links) -> None:
    """指定リンクを「新着」バッジ対象として現在時刻付きで追加する(union、既存は消さない)。
    NEW_BADGE_WINDOW_HOURS(3時間)を過ぎた既存エントリはこのタイミングで併せて削除する
    (どのみちbuild時に期限切れとして描画されなくなるため、ファイル肥大化を防ぐための掃除)。
    連続更新で直前に付いたばかりのバッジが次の更新で即座に消えてしまう問題を避けるため、
    「今回追加されたものは全部差し替え」ではなく「追加日時が3時間以内のものは維持」という
    形に2026-08-01に変更した。
    """
    now = datetime.now(JST)
    cutoff = now - timedelta(hours=NEW_BADGE_WINDOW_HOURS)
    data = load_new_badge_data()
    links = {
        link: ts for link, ts in data["links"].items()
        if datetime.fromisoformat(ts) >= cutoff
    }
    now_iso = now.isoformat()
    for link in new_links:
        links[link] = now_iso
    data["links"] = links

    publisher_by_link = {a.get("link"): a.get("publisher") for a in load_news()}
    eligible_new = [
        link for link in new_links
        if publisher_by_link.get(link) not in NEW_ARRIVALS_EXCLUDE_PUBLISHERS
    ]
    if eligible_new:
        data["last_eligible"] = {"link": eligible_new[-1], "ts": now_iso}

    save_new_badge_data(data)


def active_new_badge_links() -> set:
    """現在時刻からNEW_BADGE_WINDOW_HOURS以内に追加されたリンクの集合を返す(バッジ描画用)。"""
    now = datetime.now(JST)
    cutoff = now - timedelta(hours=NEW_BADGE_WINDOW_HOURS)
    return {
        link for link, ts in load_new_badge_data()["links"].items()
        if datetime.fromisoformat(ts) >= cutoff
    }


def fallback_new_badge_link():
    """新着除外対象(印西市役所等)を除いた直近1件のリンクを返す(3時間ウィンドウ無視)。
    通常のnew_links(3時間以内)が空の場合の最終手段として使う。未設定ならNone。
    """
    last_eligible = load_new_badge_data().get("last_eligible")
    return last_eligible["link"] if last_eligible else None


# ============================================================
# HTML直接スクレイピング(RSSが無いサイト)
# ============================================================

def fetch_soup(url: str) -> BeautifulSoup:
    res = requests.get(url, headers=HEADERS, timeout=TIMEOUT)
    res.raise_for_status()
    return BeautifulSoup(res.text, "html.parser")


WEATHER_LATE_NIGHT_HOUR = 22


WEATHER_ICON_DIR = BASE_DIR / "weather_icons"


WEATHER_ICON_CDN = "https://weathernews.jp/s/topics/img/wxicon/"

# ウェザーニューズ公式アイコン一覧(https://weathernews.jp/ip/help5/tab_icon.html)から採取したコード→天気名。
# 同じコードでも「のち時々」「のち一時」のように接続詞が重複する表記揺れや、「一時」/「時々」の揺れがあるため、
# normalize_weather_label()適用後の形(「のち」+「一時」は「一時」を省いて「のち」のみ、単独の「一時」は「時々」)で統一して保持する。
# 明後日分(#flick_list_week)は天気文言を持たないため、既知コードであればここから補完する。
WEATHER_ICON_LABELS = {
    "100": "晴れ", "550": "猛暑", "552": "猛暑時々曇り", "101": "晴れ時々くもり", "102": "晴れ時々雨",
    "104": "晴れ時々雪", "110": "晴れのちくもり", "112": "晴れのち雨",
    "115": "晴れのち雪", "200": "くもり", "201": "くもり時々晴れ",
    "202": "くもり時々雨", "204": "くもり時々雪", "210": "くもりのち晴れ",
    "212": "くもりのち雨", "215": "くもりのち雪", "650": "小雨", "300": "雨",
    "850": "大雨・嵐", "301": "雨時々晴れ", "302": "雨時々止む", "303": "雨時々雪",
    "311": "雨のち晴れ", "313": "雨のちくもり", "314": "雨のち雪", "430": "みぞれ",
    "400": "雪", "950": "大雪・吹雪", "401": "雪時々晴れ", "402": "雪時々止む",
    "403": "雪時々雨", "411": "雪のち晴れ", "413": "雪のちくもり", "414": "雪のち雨",
    "562": "猛暑のち曇り", "111": "晴れのちくもり", "572": "曇り時々猛暑",
}


NEW_WEATHER_ICONS_THIS_RUN = []


def normalize_weather_label(text: str) -> str:
    """天気名称を正規化する。同一アイコンに対し「晴れのち時々雨」「晴れのち一時雨」「晴れのち雨」のように
    表記が複数存在するため、次の2段階で統一する。
    1. 「のち」+「時々」/「一時」が連続する場合は後続の接続詞を省き「のち」のみ残す(例: 晴れのち時々雨→晴れのち雨)
    2. 残った単独の「一時」は「時々」に統一する(例: 晴れ一時雨→晴れ時々雨)
    これによりコード番号1つに対して名称が1つに定まり、キャッシュファイル名が表記揺れで増殖するのを防ぐ。
    """
    if not text:
        return text
    text = re.sub(r"のち(時々|一時)", "のち", text)
    return text.replace("一時", "時々")


def ensure_weather_icon_cached(icon_src: str, label: str = "") -> str:
    """ウェザーニューズのアイコン画像をweather_icons/にキャッシュし、index.htmlからの相対パスを返す。
    ファイル名は「{コード}_{天気名}.png」形式(天気名が取れない場合は「{コード}.png」)。
    同名ファイルが既にあれば再取得しない。
    実際にスクレイピングされたsrc(onebox配下、8bitパレットPNG)ではなく、
    同一コード体系で同じ152x112pxかつRGBAでより高画質なtopics配下のCDNから取得する
    (2026-07-20に画質比較の上で切り替え)。
    新規ダウンロードが発生した場合はNEW_WEATHER_ICONS_THIS_RUNに記録し、
    build実行時にどのアイコンが新規に増えたかを報告できるようにする。
    """
    src_url = "https:" + icon_src if icon_src.startswith("//") else icon_src
    code = re.sub(r"\.png$", "", src_url.split("/")[-1].split("?")[0])
    url = f"{WEATHER_ICON_CDN}{code}.png"
    label = normalize_weather_label(label)
    safe_label = re.sub(r"[^\w一-龥ぁ-んァ-ヶー]", "", label) if label else ""
    filename = f"{code}_{safe_label}.png" if safe_label else f"{code}.png"
    local_path = WEATHER_ICON_DIR / filename
    if not local_path.exists():
        WEATHER_ICON_DIR.mkdir(exist_ok=True)
        res = requests.get(url, headers=HEADERS, timeout=TIMEOUT)
        res.raise_for_status()
        local_path.write_bytes(res.content)
        NEW_WEATHER_ICONS_THIS_RUN.append(filename)
    return f"weather_icons/{filename}"


def weather_day_label(d: date) -> str:
    return f"{d.month}/{d.day}"


def resolve_weather_date(month: int, day_num: int, now_jst: datetime) -> date:
    year = now_jst.year
    if month < now_jst.month - 6:
        year += 1
    return date(year, month, day_num)


def weekday_daytype_fallback(d: date):
    """曜日のみからのdaytypeフォールバック(祝日は考慮できない)。
    #flick_list_week側の分類(祝日を含む)が取れればそちらで上書きされる。
    """
    if d.weekday() == 5:
        return "sat"
    if d.weekday() == 6:
        return "sun"
    return None


def parse_weather_card(card, now_jst: datetime):
    """#flick_list_today内の1日分カード(今日・明日)を解析する。天気文言・降水確率まで取れる。"""
    date_span = card.select_one("h3 span")
    status_tag = card.select_one(".status.pc")
    high_tag = card.select_one(".temp .high dd")
    low_tag = card.select_one(".temp .low dd")
    icon_tag = card.select_one("img.wx__icon")
    if not (date_span and status_tag and high_tag and low_tag and icon_tag):
        return None
    m = re.search(r"(\d+)月(\d+)日", date_span.get_text())
    high_m = re.search(r"(-?\d+)℃", high_tag.get_text())
    low_m = re.search(r"(-?\d+)℃", low_tag.get_text())
    if not (m and high_m and low_m):
        return None
    d = resolve_weather_date(int(m.group(1)), int(m.group(2)), now_jst)
    status = normalize_weather_label(status_tag.get_text(strip=True))
    pop_values = []
    for cell in card.select("table.precipitation tbody td span"):
        txt = cell.get_text(strip=True).replace("%", "")
        if txt.isdigit():
            pop_values.append(int(txt))
    return {
        "_day": d.day,
        "label": weather_day_label(d),
        "weekday": d.weekday(),
        "daytype": weekday_daytype_fallback(d),
        "icon": ensure_weather_icon_cached(icon_tag["src"], status),
        "weather_label": status,
        "temp_max": int(high_m.group(1)),
        "temp_min": int(low_m.group(1)),
        "pop": max(pop_values) if pop_values else None,
    }


def parse_weather_week_row(row, d: date):
    """#flick_list_week内の1日分の行(明後日以降)を解析する。天気文言は無い。
    降水確率は当日以降の行なら%表示(pop_by_day経由で別途上書きされる想定)。
    天気名はアイコンコードがWEATHER_ICON_LABELSの既知コードであれば補完し、
    未知コードなら空のままにする(このセクションはそもそも天気文言を持たないため)。
    """
    high_tag = row.select_one(".high p")
    low_tag = row.select_one(".low p")
    icon_tag = row.select_one("img.wx__icon")
    if not (high_tag and low_tag and icon_tag):
        return None
    high_m = re.search(r"(-?\d+)", high_tag.get_text())
    low_m = re.search(r"(-?\d+)", low_tag.get_text())
    if not (high_m and low_m):
        return None
    icon_src = icon_tag["src"]
    code = re.sub(r"\.png$", "", icon_src.split("/")[-1].split("?")[0])
    weather_label = WEATHER_ICON_LABELS.get(code, "")
    return {
        "_day": d.day,
        "label": weather_day_label(d),
        "weekday": d.weekday(),
        "daytype": weekday_daytype_fallback(d),
        "icon": ensure_weather_icon_cached(icon_src, weather_label),
        "weather_label": weather_label,
        "temp_max": int(high_m.group(1)),
        "temp_min": int(low_m.group(1)),
        "pop": None,
    }


def parse_weather_week_pop(week_container) -> dict:
    """#flick_list_week内の各日の降水確率(%)を{day(int): pop(int)}で返す。
    過去日は「Xミリ」(実績降水量)、当日以降は「X%」(予報)で表示されるため、%表記の行のみ拾う。
    """
    pop_by_day = {}
    for row in week_container.select("ul.wxweek_content"):
        day_tag = row.select_one(".date .day")
        rain_tag = row.select_one(".rain p")
        if not (day_tag and rain_tag):
            continue
        text = rain_tag.get_text(strip=True)
        if not text.endswith("%"):
            continue
        m = re.match(r"(\d+)%", text)
        day_m = re.match(r"\d+", day_tag.get_text(strip=True))
        if m and day_m:
            pop_by_day[int(day_m.group())] = int(m.group(1))
    return pop_by_day


def parse_weather_week_daytype(week_container) -> dict:
    """#flick_list_week内の各日の曜日色種別を{day(int): "sat"|"sun"|None}で返す。
    ウェザーニューズ側は祝日もsunクラスとして扱っている(=日曜と同色)ため、
    自前の祝日判定を持たずサイト側の分類をそのまま使う。
    """
    daytype_by_day = {}
    for row in week_container.select("ul.wxweek_content"):
        date_li = row.select_one(".date")
        day_tag = row.select_one(".date .day")
        if not (date_li and day_tag):
            continue
        day_m = re.match(r"\d+", day_tag.get_text(strip=True))
        if not day_m:
            continue
        classes = date_li.get("class", [])
        if "sun" in classes:
            daytype_by_day[int(day_m.group())] = "sun"
        elif "sat" in classes:
            daytype_by_day[int(day_m.group())] = "sat"
        else:
            daytype_by_day[int(day_m.group())] = None
    return daytype_by_day


def fetch_weather():
    """印西市の天気予報を今日・明日・明後日の3日分取得し、時刻に応じて2日分を返す。失敗時はNoneを返す。
    22時以降に実行された場合は「今日・明日」ではなく「明日・明後日」を表示する
    (深夜近くに今日の天気を出しても実用性が低いため)。
    このページはVue.jsで描画されるが、初期HTMLに実データがサーバーサイドレンダリング
    済みで埋め込まれているため、JS実行なしのスクレイピングで取得できる。
    天気文言・気温は#flick_list_today(今日・明日分)/#flick_list_week(明後日分)から取得し、
    降水確率は表記ゆれが無い#flick_list_week側の値で統一する。
    アイコン画像はweather_icons/にキャッシュして使い回す。
    """
    now_jst = datetime.now(JST)
    try:
        soup = fetch_soup(WEATHER_FETCH_URL)
        days = []

        today_container = soup.select_one("#flick_list_today")
        if today_container is not None:
            cards = today_container.select("div.card")
            idx = next((i for i, c in enumerate(cards) if c.get("id") == "now__day"), None)
            if idx is not None:
                for card in cards[idx:idx + 2]:
                    day = parse_weather_card(card, now_jst)
                    if day:
                        days.append(day)

        week_container = soup.select_one("#flick_list_week")
        if week_container is not None:
            target = now_jst.date() + timedelta(days=2)
            for row in week_container.select("ul.wxweek_content"):
                day_tag = row.select_one(".date .day")
                if day_tag and day_tag.get_text(strip=True) == str(target.day):
                    day = parse_weather_week_row(row, target)
                    if day:
                        days.append(day)
                    break

            pop_by_day = parse_weather_week_pop(week_container)
            daytype_by_day = parse_weather_week_daytype(week_container)
            for day in days:
                if day["_day"] in pop_by_day:
                    day["pop"] = pop_by_day[day["_day"]]
                if day["_day"] in daytype_by_day:
                    day["daytype"] = daytype_by_day[day["_day"]]

        for day in days:
            day.pop("_day", None)

        selected = days[1:3] if now_jst.hour >= WEATHER_LATE_NIGHT_HOUR else days[0:2]
        return selected if selected else None
    except Exception as e:
        print(f"[WARN] 天気予報取得エラー: {e}", file=sys.stderr)
        return None


# ============================================================
# 電車時刻表(印西牧の原・千葉ニュータウン中央 上り / 浅草橋・新鎌ヶ谷 下り)
# ============================================================

TRAIN_TIMETABLE_URL = "https://hokuso.ekitan.com/jp/pc/T5"
EKITAN_TIMETABLE_URL = "https://ekitan.com/timetable/railway/line-station/{code}/d2"

# 電車時刻表ウィジェットの循環グループ(ボタンを押すたびにこの順で切り替わり、末尾の次は先頭に戻る)。
# up: 印西牧の原・千葉ニュータウン中央 → 京成高砂・日本橋方面(hokuso.ekitan.com, d=1)
# down_*: いずれも印西牧の原・成田空港方面(下り)の駅を追加したもの。浅草橋・新橋・東銀座・東日本橋は
# 都営浅草線、品川は京急本線に属し、いずれもhokuso.ekitan.comの対象外(北総線に属さない)のため
# 一般のekitan.com「駅探」(line-station/{路線コード}/d2)を使用する。table_indexは、そのページに並ぶ
# 2つの方面テーブルのうち印西牧の原方面が何番目か(0始まり)を表す。新鎌ヶ谷のみ北総線内のためhokuso側
# (d=2:印旛日本医大方面)を使用。
TRAIN_GROUPS = [
    {
        "key": "up",
        "stations": {
            "inzaimakinohara": {"name": "印西牧の原", "site": "hokuso", "sl_code": "200-13", "d": "1"},
            "chibanewtownchuo": {"name": "千葉ニュータウン中央", "site": "hokuso", "sl_code": "200-12", "d": "1"},
        },
        "direction_label": "京成高砂・日本橋方面",
        "own_toggle_label": "上り印西牧の原、千葉ニュータウン発切り替え",
    },
    {
        "key": "down_asakusabashi",
        "stations": {
            "asakusabashi": {"name": "浅草橋", "site": "ekitan", "line_code": "222-15", "table_index": 1, "include_dests": "narita"},
            "shinkamagaya": {"name": "新鎌ヶ谷", "site": "hokuso", "sl_code": "200-8", "d": "2", "exclude_types": {"ス"}},  # 「ス」=スカイライナー
        },
        "direction_label": "印西牧の原・成田空港方面 ：印西へ向かう電車のみ表示",
        "own_toggle_label": "下り浅草橋、新鎌ヶ谷発切り替え",
    },
    {
        "key": "down_shinagawa",
        "stations": {
            "shinagawa": {"name": "品川", "site": "ekitan", "line_code": "250-1", "table_index": 0, "include_dests": "narita"},
            "shimbashi": {"name": "新橋", "site": "ekitan", "line_code": "222-9", "table_index": 1, "include_dests": "narita"},
        },
        "direction_label": "印西牧の原・成田空港方面 ：印西へ向かう電車のみ表示",
        "own_toggle_label": "下り品川、新橋発切り替え",
    },
    {
        "key": "down_ginza",
        "stations": {
            "higashiginza": {"name": "東銀座", "site": "ekitan", "line_code": "222-10", "table_index": 1, "include_dests": "narita"},
            "higashinihombashi": {"name": "東日本橋", "site": "ekitan", "line_code": "222-14", "table_index": 1, "include_dests": "narita"},
        },
        "direction_label": "印西牧の原・成田空港方面 ：印西へ向かう電車のみ表示",
        "own_toggle_label": "下り東銀座、東日本橋発切り替え",
    },
    {
        # 印旛日本医大は北総線内の駅だがhokuso.ekitan.com側では上り(d=1)しか時刻表が存在しない
        # (下り(成田空港方面)はエラーになる。おそらく北総鉄道自社線としての運行区間がここまでで、
        # 先は成田空港線(成田高速鉄道アクセス)の管轄区間になるため)。上下とも一般のekitan.com
        # (路線コード682-4、成田スカイアクセス線扱い)から取得する。このページはd=1/d=2どちらの
        # URLでも同じ2テーブルが出力され、1つ目(table_index0)が京成高砂方面(上り)、2つ目
        # (table_index1)が成田空港方面(下り)。上りは印旛日本医大始発の電車を幅広く含むため
        # 行き先フィルタは不要(include_dests無し)。下りは他の下りグループと同じくnarita行き先
        # フィルタを適用する。
        "key": "inba_nihon_idai",
        "stations": {
            "inbanihonidai_up": {"name": "印旛日本医大(上り)", "site": "ekitan", "line_code": "682-4", "table_index": 0},
            "inbanihonidai_down": {"name": "印旛日本医大(下り)", "site": "ekitan", "line_code": "682-4", "table_index": 1, "include_dests": "narita"},
        },
        "direction_label": "左：京成高砂方面(上り) ／ 右：成田空港方面(下り)",
        "own_toggle_label": "印旛日本医大発切り替え",
    },
]

# 一般のekitan.com側は種別がフル表記のため、hokuso.ekitan.com側の略称表記に揃える
EKITAN_TYPE_ABBREV = {
    "アクセス特急": "ア特",
    "通勤特急": "通特",
    "エアポート快特": "エ快",
    "エアポート快特:成田スカイアクセス線経由": "エ快",
    "モーニング・ウィング": "モ特",
    "イブニング・ウィング": "イ特",
}

# ekitan.com(駅探)から取得する下り駅(浅草橋・品川・新橋・東銀座・東日本橋)共通の行き先フィルタ。
# 新鎌ヶ谷以遠(成田スカイアクセス線・北総線経由で印西牧の原・成田空港方面)へ向かう行き先のみを残す
# (泉岳寺止まり・押上止まり・京成高砂止まりや、京成本線経由で新鎌ヶ谷を通らない京成成田/京成佐倉/
# 宗吾参道/芝山千代田行きなどは除外する)。スカイライナーは駅探側の路線(都営浅草線・京急本線)を
# 経由しないため元々出現しないが、念のためfetch_train_timetable_ekitan側でも種別名から除外する。
NARITA_DIRECTION_INCLUDE_DESTS = {"新鎌ヶ谷", "印西牧の原", "印旛日本医大", "成田湯川", "空港第2ビル", "成田空港"}

# 印西牧の原駅に実際に停車する種別(この駅自体のd=1/d=2両方向の発車データを実地確認して判明。
# 「快速」「快特」「通勤特急」「アクセス特急」「エアポート快特」等はいずれもこの駅を通過する)。
# 種別名に「特」が含まれるかどうかでは正しく判定できない(「特急」は停車するが「アクセス特急」等は通過するため)。
INZAI_MAKINOHARA_STOP_TYPES = {"普通", "特急"}

HOLIDAY_CSV_URL = "https://www8.cao.go.jp/chosei/shukujitsu/syukujitsu.csv"


def fetch_train_timetable(sl_code: str, dw: str, d: str = "1", exclude_types: set = None) -> list:
    """北総鉄道(hokuso.ekitan.com)の指定駅・ダイヤ区分(dw=0:平日 / dw=1:土曜・休日)・
    方面(d=1:京成高砂・日本橋方面 / d=2:印旛日本医大方面)の時刻表を取得する。行き先の略字
    (例:「羽」)はページ内の凡例(「羽−羽田空港」等)から都度読み取って正式名称に変換するため、
    行き先が増減しても追従できる。exclude_typesに含まれる種別(略字。例:スカイライナー=「ス」)は除外する。
    取得失敗時は空リストを返す。
    """
    exclude_types = exclude_types or set()
    params = {"USR": "PC", "dw": dw, "slCode": sl_code, "d": d}
    res = requests.get(TRAIN_TIMETABLE_URL, params=params, headers=HEADERS, timeout=TIMEOUT)
    res.raise_for_status()
    soup = BeautifulSoup(res.text, "html.parser")

    dest_map = {}
    for m in re.finditer(r"([一-龥])[−\-]([一-龥ぁ-んァ-ヶー]+)", soup.get_text()):
        dest_map[m.group(1)] = m.group(2)

    trains = []
    for tr in soup.select("table tr"):
        hour_tag = tr.select_one("th.side01, th.side02")
        if not hour_tag:
            continue
        hour_text = hour_tag.get_text(strip=True)
        if not hour_text.isdigit():
            continue
        hour = int(hour_text)
        for box in tr.select("div.syasyubox"):
            text = box.get_text("|", strip=True).replace("\xa0", " ")
            parts = [p for p in text.split("|") if p]
            if len(parts) < 2:
                continue
            m = re.match(r"(\S+)\s+(\S)$", parts[0])
            if not m:
                continue
            train_type, dest_abbr = m.group(1), m.group(2)
            if train_type in exclude_types:
                continue
            minute_m = re.search(r"\d+", parts[1])
            if not minute_m:
                continue
            # ページ内の凡例に「下線＝当駅始発」とあり、分の数字が<span class="underline">の場合は
            # その駅から走り始める電車(通過・途中駅発ではない)を示す。
            is_origin = box.select_one("span.underline") is not None
            trains.append({
                "time": f"{hour:02d}:{int(minute_m.group()):02d}",
                "type": train_type,
                "dest": dest_map.get(dest_abbr, dest_abbr),
                "origin": is_origin,
            })
    trains.sort(key=lambda t: t["time"])
    return trains


def fetch_train_timetable_ekitan(line_code: str, dw: str, table_index: int = 1, include_dests: set = None) -> list:
    """一般のekitan.com(駅探)から指定路線コード(例:浅草橋=222-15)の時刻表を取得する。
    hokuso.ekitan.comの対象外の駅(北総線に属さない駅)用。
    ダイヤ区分はdw=0:平日 / dw=2:休日(土曜・休日をまとめて代表させるため休日側を採用)。
    ページには方面ごとに<table class="search-result-data ek-search-result">が2つ並んでおり、
    駅によって印西牧の原方面が何番目のテーブルかが異なるため(通常は2つ目=index1だが、品川のみ
    1つ目=index0)、table_indexで指定する。各電車は<li data-tr-type=種別 data-dest=行き先
    data-start=当駅始発の場合のみ非空>属性を持ち、行き先は既に正式名称なので変換不要。
    include_destsを指定した場合はそこに含まれる行き先のみを残す(新鎌ヶ谷以遠へ向かう電車のみに絞る用途)。
    """
    url = EKITAN_TIMETABLE_URL.format(code=line_code)
    res = requests.get(url, params={"dw": dw}, headers=HEADERS, timeout=TIMEOUT)
    res.raise_for_status()
    soup = BeautifulSoup(res.text, "html.parser")

    tables = soup.select("table.search-result-data.ek-search-result")
    if len(tables) <= table_index:
        return []
    table = tables[table_index]

    trains = []
    for tr in table.select("tr.ek-hour_line"):
        hour_tag = tr.select_one("td")
        if not hour_tag:
            continue
        hour_text = hour_tag.get_text(strip=True)
        if not hour_text.isdigit():
            continue
        hour = int(hour_text)
        for li in tr.select("li.ek-train-tooltip"):
            dest = li.get("data-dest", "").strip()
            if not dest or (include_dests is not None and dest not in include_dests):
                continue
            train_type = li.get("data-tr-type", "").strip()
            if "スカイライナー" in train_type:
                continue
            # 未知の種別名(辞書に無いもの)は表示崩れを防ぐため先頭2文字に切り詰める
            train_type = EKITAN_TYPE_ABBREV.get(train_type, train_type[:2])
            minute_tag = li.select_one("span.time-min")
            if not minute_tag:
                continue
            minute_text = minute_tag.get_text(strip=True)
            if not minute_text.isdigit():
                continue
            trains.append({
                "time": f"{hour:02d}:{int(minute_text):02d}",
                "type": train_type,
                "dest": dest,
                "origin": bool(li.get("data-start", "").strip()),
            })
    trains.sort(key=lambda t: t["time"])
    return trains


def all_train_stations() -> dict:
    """TRAIN_GROUPS全体の駅定義をキー衝突なく1つの辞書にまとめて返す。"""
    stations = {}
    for group in TRAIN_GROUPS:
        stations.update(group["stations"])
    return stations


def fetch_train_data() -> dict:
    """全グループの全駅の平日/土曜・休日の時刻表をまとめて取得する。
    駅ごとに取得失敗しても他の駅の結果は返す(失敗した駅は空リストのまま)。
    """
    data = {}
    for key, st in all_train_stations().items():
        entry = {"name": st["name"], "weekday": [], "weekend": []}
        if st["site"] == "hokuso":
            for dw, daytype in (("0", "weekday"), ("1", "weekend")):
                try:
                    entry[daytype] = fetch_train_timetable(st["sl_code"], dw, st.get("d", "1"), st.get("exclude_types"))
                except Exception as e:
                    print(f"[WARN] 電車時刻表取得エラー({st['name']}/{daytype}): {e}", file=sys.stderr)
        else:  # ekitan
            include_dests = NARITA_DIRECTION_INCLUDE_DESTS if st.get("include_dests") == "narita" else None
            for dw, daytype in (("0", "weekday"), ("2", "weekend")):
                try:
                    entry[daytype] = fetch_train_timetable_ekitan(
                        st["line_code"], dw, st.get("table_index", 1), include_dests
                    )
                except Exception as e:
                    print(f"[WARN] 電車時刻表取得エラー({st['name']}/{daytype}): {e}", file=sys.stderr)
        data[key] = entry
    return data


def fetch_japanese_holidays() -> list:
    """内閣府の祝日データ(CSV)から祝日一覧(ISO日付文字列)を取得する。
    ページ全体のサイズを抑えるため前年以降の日付のみ返す。取得失敗時は空リストを返す。
    """
    try:
        res = requests.get(HOLIDAY_CSV_URL, headers=HEADERS, timeout=TIMEOUT)
        res.raise_for_status()
        text = res.content.decode("shift_jis")
        cutoff_year = date.today().year - 1
        holidays = []
        for line in text.splitlines()[1:]:
            cell = line.split(",")[0].strip()
            try:
                d = datetime.strptime(cell, "%Y/%m/%d").date()
            except ValueError:
                continue
            if d.year >= cutoff_year:
                holidays.append(d.isoformat())
        return holidays
    except Exception as e:
        print(f"[WARN] 祝日データ取得エラー: {e}", file=sys.stderr)
        return []


TRAIN_CACHE_PATH = BASE_DIR / "train_timetable_cache.json"
TRAIN_CACHE_MAX_AGE_DAYS = 30
TRAIN_TIMETABLE_CHANGED = False


def load_or_fetch_train_data():
    """電車時刻表・祝日データをキャッシュ(train_timetable_cache.json)から読む。
    ダイヤ改正は年に数回程度しかなく、buildのたびに北総鉄道サイトへ問い合わせるのは
    過剰なので、TRAIN_CACHE_MAX_AGE_DAYS以内ならキャッシュをそのまま使い、
    古い/存在しない場合のみ再取得してキャッシュを更新する。
    再取得が全滅した場合(サイト障害等)は、多少古くてもキャッシュがあればそれを使い続ける
    (真っ白になるより古い時刻表の方がまし)。
    再取得した結果が前回キャッシュの内容と異なる場合はダイヤ改正とみなし、
    TRAIN_TIMETABLE_CHANGEDを立ててbuild実行時に報告できるようにする。
    """
    global TRAIN_TIMETABLE_CHANGED
    expected_keys = set(all_train_stations())
    cache = load_json(TRAIN_CACHE_PATH, None)
    cache_has_all_stations = bool(cache) and expected_keys <= set(cache["train_data"].keys())
    if cache and cache_has_all_stations:
        fetched_at = datetime.fromisoformat(cache["fetched_at"])
        age_days = (datetime.now(JST) - fetched_at).days
        if age_days < TRAIN_CACHE_MAX_AGE_DAYS:
            return cache["train_data"], cache["holidays"]

    train_data = fetch_train_data()
    holidays = fetch_japanese_holidays()
    has_any_train = any(entry["weekday"] or entry["weekend"] for entry in train_data.values())

    if has_any_train:
        # 駅構成を変更した直後(旧キャッシュに新駅が無い)は差分比較の対象外とし、
        # ダイヤ改正の誤検知を防ぐ
        if cache and cache_has_all_stations and cache["train_data"] != train_data:
            TRAIN_TIMETABLE_CHANGED = True
        save_json_atomic(TRAIN_CACHE_PATH, {
            "fetched_at": datetime.now(JST).isoformat(),
            "train_data": train_data,
            "holidays": holidays,
        })
        return train_data, holidays

    if cache:
        print("[WARN] 電車時刻表の再取得に失敗したため、古いキャッシュを使用します", file=sys.stderr)
        return cache["train_data"], cache["holidays"]
    return train_data, holidays


def extract_date_groups(text: str):
    normalized = unicodedata.normalize("NFKC", text)
    m = re.search(r"(\d{4})年(\d{1,2})月(\d{1,2})日", normalized)
    if m:
        return m.groups()
    m = re.search(r"(\d{4})/(\d{1,2})/(\d{1,2})", normalized)
    if m:
        return m.groups()
    return None


def scrape_makinohara(cfg, existing_by_link):
    url = cfg["url"]
    soup = fetch_soup(url)
    panel = soup.select_one(".p-home-sec-event-topics-in__panels .js-panel")
    items = []
    if panel is None:
        return items
    for card in panel.select(".p-home-sec-event-topics-in-card"):
        a = card.select_one("a[href]")
        title_tag = card.select_one("h3")
        time_tag = card.select_one("time")
        if not (a and title_tag and time_tag):
            continue
        m = re.search(r"(\d{4})/(\d{1,2})/(\d{1,2})", time_tag.get_text())
        if not m:
            continue
        items.append({
            "title": title_tag.get_text(strip=True),
            "link": a["href"].strip(),
            "pub_str": to_pub_str(*m.groups()),
            "publisher": cfg.get("publisher", cfg["name"]),
            "source": cfg["id"],
            "category": cfg.get("category"),
        })
    return items


def scrape_aeonmall_renewal(cfg, existing_by_link):
    url = cfg["url"]
    soup = fetch_soup(url)
    items = []
    for li in soup.select("li.result-box"):
        a = li.select_one("a[href]")
        title_tag = li.select_one("p.name")
        info_tag = li.select_one("p.info")
        if not (a and title_tag and info_tag):
            continue
        raw_title = title_tag.get_text(strip=True)
        date_groups = extract_date_groups(raw_title) or extract_date_groups(info_tag.get_text())
        if not date_groups:
            continue
        badge_tag = li.select_one(".result-box-badge")
        category_badge = badge_tag.get_text(strip=True) if badge_tag else ""
        label = RENEWAL_CATEGORY_LABELS.get(category_badge, category_badge or "情報")
        tenant_tag = li.select_one("p.tenant")
        tenant_name_node = tenant_tag.find(string=True, recursive=False) if tenant_tag else None
        if tenant_name_node:
            store_name = tenant_name_node.strip()
        else:
            store_name = re.sub(rf"\s*{re.escape(category_badge)}?\s*のお知らせ\s*$", "", raw_title).strip()
        items.append({
            "title": f"【{to_pub_str(*date_groups)} {label}】{store_name}",
            "link": urljoin(url, a["href"].strip()),
            "pub_str": to_pub_str(*date_groups),
            "publisher": cfg.get("publisher", cfg["name"]),
            "source": cfg["id"],
            "category": cfg.get("category"),
        })
    return items


def scrape_aeonmall_event(cfg, existing_by_link):
    url = cfg["url"]
    soup = fetch_soup(url)
    items = []
    skipped = 0
    for li in soup.select("li.result-box"):
        a = li.select_one("a[href]")
        title_tag = li.select_one("p.name")
        if not (a and title_tag):
            continue
        link = urljoin(url, a["href"].strip())
        title = title_tag.get_text(strip=True)
        existing = existing_by_link.get(link)
        if existing and existing.get("title") == title:
            items.append(existing)
            skipped += 1
            continue
        try:
            detail_soup = fetch_soup(link)
        except requests.RequestException as e:
            print(f"[WARN] イベント詳細取得失敗 {link}: {e}", file=sys.stderr)
            continue
        update_tag = detail_soup.select_one("p.update")
        if not update_tag:
            continue
        m = re.search(r"(\d{4})/(\d{1,2})/(\d{1,2})", update_tag.get_text())
        if not m:
            continue
        items.append({
            "title": title,
            "link": link,
            "pub_str": to_pub_str(*m.groups()),
            "publisher": cfg.get("publisher", cfg["name"]),
            "source": cfg["id"],
            "category": cfg.get("category"),
        })
    if skipped:
        print(f"  (うち{skipped}件は前回と同一タイトルのため詳細取得をスキップ)")
    return items


def scrape_goguynet(cfg, existing_by_link):
    url = cfg["url"]
    soup = fetch_soup(url)
    items = []
    for box in soup.select("div.centerMdBox01"):
        a = box.select_one("a.itemTitle01[href]")
        title_tag = box.select_one("h1.itemTitle01In span")
        date_tag = box.select_one("div.listDate01 span")
        if not (a and title_tag and date_tag):
            continue
        m = re.search(r"(\d{4})/(\d{1,2})/(\d{1,2})", date_tag.get_text())
        if not m:
            continue
        title = title_tag.get_text(strip=True)
        category = cfg.get("category")
        if any(kw in title for kw in KAITEN_KEYWORDS):
            category = "開店・閉店"
        elif category == "鎌ヶ谷・白井" and not any(kw in title for kw in ["鎌ケ谷", "鎌ヶ谷", "白井"]):
            # 号外NETは鎌ケ谷・白井・印西の3市をカバーするため、印西市単独の記事は
            # 「鎌ヶ谷・白井」に固定せずタイトルからの推定/AI判断(review_queue)に委ねる
            category = None
        items.append({
            "title": title,
            "link": a["href"].strip(),
            "pub_str": to_pub_str(*m.groups()),
            "publisher": cfg.get("publisher", cfg["name"]),
            "source": cfg["id"],
            "category": category,
        })
    return items


def scrape_inzainet_event(cfg, existing_by_link):
    """いんざいネット.comのイベント一覧。北総地域全体(我孫子・取手・成田等)を扱うため、
    地域タグに「印西市(class=inzai)」が付いているイベントのみ対象とする。
    掲載日(pub_str)は初回検知日を使う(開催日は未来日付になり得るため流用しない)。
    """
    url = cfg["url"]
    soup = fetch_soup(url)
    items = []
    today_str = to_pub_str(date.today().year, date.today().month, date.today().day)
    for li in soup.select("ul.event_list > li"):
        if li.find("span", class_="inzai") is None:
            continue
        a = li.select_one("a[href]")
        title_tag = li.select_one("h2")
        day_tag = li.select_one(".event_day time")
        if not (a and title_tag):
            continue
        link = a["href"].strip()
        title = title_tag.get_text(strip=True)
        day_text = day_tag.get_text(strip=True) if day_tag else ""
        full_title = f"{title}（{day_text}）" if day_text else title
        existing = existing_by_link.get(link)
        pub_str = existing["pub_str"] if existing and existing.get("pub_str") else today_str
        items.append({
            "title": full_title,
            "link": link,
            "pub_str": pub_str,
            "publisher": cfg.get("publisher", cfg["name"]),
            "source": cfg["id"],
            "category": cfg.get("category"),
        })
    return items


def scrape_inzaiparque(cfg, existing_by_link):
    """千葉ほくそうパルケ(旧いんざいパルケ)。北総地域全体(茨城県南部含む)を扱うため、
    RSSのcategoryタグに「印西市」が付いている記事のみ対象とする。
    """
    url = cfg["url"]
    res = requests.get(url, headers=HEADERS, timeout=TIMEOUT)
    res.raise_for_status()
    root = ET.fromstring(res.content)
    items = []
    for item in root.iter():
        if _local_tag(item.tag) != "item":
            continue
        title = link = pub_raw = ""
        categories = []
        for child in item:
            name = _local_tag(child.tag)
            if name == "title":
                title = child.text or ""
            elif name == "link":
                link = child.text or ""
            elif name == "pubDate":
                pub_raw = child.text or ""
            elif name == "category":
                categories.append((child.text or "").strip())
        if "印西市" not in categories:
            continue
        title = html.unescape(title)
        try:
            pub_dt = parsedate_to_datetime(pub_raw).astimezone(JST)
        except Exception:
            pub_dt = datetime.now(JST)
        items.append({
            "title": title,
            "link": link.strip(),
            "pub_str": to_pub_str(pub_dt.year, pub_dt.month, pub_dt.day),
            "publisher": cfg.get("publisher", cfg["name"]),
            "source": cfg["id"],
            "category": cfg.get("category"),
        })
    return items


def scrape_joyfulhonda_chibant(cfg, existing_by_link):
    """ジョイフル本田 千葉ニュータウン店のイベント情報。
    サイトに「掲載日」はなく「開催日」しかないため、掲載日(pub_str)は初回検知日を使い、
    タイトルに開催日を併記する(開催日をそのままpub_strにすると未来日として自動除外されるため)。
    日付範囲は今日から30日先までを毎回動的に指定する。
    """
    today = date.today()
    to_d = today + timedelta(days=30)
    params = {
        "search_element_0[]": "chibant",
        "fromDate_disp": today.strftime("%Y/%m/%d"),
        "cf_limit_keyword_1": today.strftime("%Y%m%d"),
        "toDate_disp": to_d.strftime("%Y/%m/%d"),
        "cf_limit_keyword_2": to_d.strftime("%Y%m%d"),
        "search_element_3": "",
        "s_keyword_4": "",
        "and_or": "and",
        "searchbutton": "検 索",
        "csp": "search_add",
        "feadvns_max_line_0": "5",
        "fe_form_no": "0",
    }
    res = requests.get(cfg["url"], params=params, headers=HEADERS, timeout=TIMEOUT)
    res.raise_for_status()
    soup = BeautifulSoup(res.text, "html.parser")
    items = []
    today_str = to_pub_str(today.year, today.month, today.day)
    for box in soup.select("div.list-Item"):
        a = box.select_one("a.link[href]")
        title_tag = box.select_one(".ttl")
        date_tag = box.select_one(".date")
        if not (a and title_tag):
            continue
        link = urljoin(cfg["url"], a["href"].strip())
        title = title_tag.get_text(strip=True)
        day_text = date_tag.get_text(strip=True) if date_tag else ""
        full_title = f"{title}（{day_text}）" if day_text else title
        existing = existing_by_link.get(link)
        pub_str = existing["pub_str"] if existing and existing.get("pub_str") else today_str
        # 開催終了日: 「A～B」形式なら最後の日付、単日なら1つだけの日付を終了日とする。
        # 見つからない場合はNone(通常の掲載期限ロジックにフォールバック)。
        end_matches = re.findall(r"(\d{4})年(\d{1,2})月(\d{1,2})日", day_text)
        event_end_date = date(*map(int, end_matches[-1])).isoformat() if end_matches else None
        items.append({
            "title": full_title,
            "link": link,
            "pub_str": pub_str,
            "event_end_date": event_end_date,
            "publisher": cfg.get("publisher", cfg["name"]),
            "source": cfg["id"],
            "category": cfg.get("category"),
        })
    return items


HTML_SCRAPER_FUNCS = {
    "makinohara-more": scrape_makinohara,
    "aeonmall-chibanewtown-renewal": scrape_aeonmall_renewal,
    "aeonmall-chibanewtown-event": scrape_aeonmall_event,
    "goguynet-kamagaya-shiroi-inzai": scrape_goguynet,
    "inzainet-event": scrape_inzainet_event,
    "joyfulhonda-chibant": scrape_joyfulhonda_chibant,
    "inzaiparque": scrape_inzaiparque,
}


# ============================================================
# RSS収集
# ============================================================

def _local_tag(tag):
    return tag.split("}")[-1] if "}" in tag else tag


def fetch_rss(cfg, blocked_publishers):
    url = cfg["url"]
    fixed_publisher = cfg.get("publisher")
    category = cfg.get("category")
    require_local_keyword = cfg["id"].startswith("google-news-")
    items = []
    filtered_out = 0
    try:
        res = requests.get(url, headers=HEADERS, timeout=TIMEOUT)
        res.raise_for_status()
        root = ET.fromstring(res.content)
        item_elements = [el for el in root.iter() if _local_tag(el.tag) == "item"]
        for item in item_elements:
            title = link = desc = pub_raw = ""
            for child in item:
                name = _local_tag(child.tag)
                if name == "title":
                    title = child.text or ""
                elif name == "link":
                    link = child.text or ""
                elif name == "description":
                    desc = child.text or ""
                elif name in ("pubDate", "date"):
                    pub_raw = child.text or ""

            title = html.unescape(title)
            desc = html.unescape(re.sub(r"<[^>]+>", "", desc))

            if fixed_publisher is None:
                publisher_match = re.search(r"\s*-\s*([^-]+)$", title)
                publisher = publisher_match.group(1).strip() if publisher_match else ""
                title = re.sub(r"\s*-\s*[^-]+$", "", title).strip()
            else:
                publisher = fixed_publisher

            try:
                pub_dt = parsedate_to_datetime(pub_raw).astimezone(JST)
            except Exception:
                try:
                    pub_dt = datetime.fromisoformat(pub_raw).astimezone(JST)
                except Exception:
                    pub_dt = datetime.now(JST)

            if title and link:
                if publisher in blocked_publishers:
                    continue
                if require_local_keyword and not is_locally_relevant(title):
                    filtered_out += 1
                    continue
                link = link.replace("news.google.com/rss/articles/", "news.google.com/articles/")
                items.append({
                    "title": title,
                    "link": link,
                    "desc": desc[:200] if len(desc) > 200 else desc,
                    "pub_iso": pub_dt.isoformat(),
                    "pub_str": to_pub_str(pub_dt.year, pub_dt.month, pub_dt.day),
                    "publisher": publisher,
                    "source": cfg["id"],
                    "category": category,
                })
    except Exception as e:
        print(f"[WARN] RSS取得エラー ({url}): {e}", file=sys.stderr)
    if filtered_out:
        print(f"  ({filtered_out}件は印西と無関係と判定し除外)")
    return items


# ============================================================
# collect: 収集 + ルールベース重複排除/カテゴリ分類
# ============================================================

def collect_candidates(existing_by_link, sources):
    candidates = []
    for cfg in sources.get("html_scrapers", []):
        func = HTML_SCRAPER_FUNCS.get(cfg["id"])
        if func is None:
            print(f"[WARN] 未対応のスクレイパーID: {cfg['id']}", file=sys.stderr)
            continue
        step_start = time.monotonic()
        try:
            items = func(cfg, existing_by_link)
        except Exception as e:
            print(f"[WARN] {cfg['name']} 取得失敗: {e}", file=sys.stderr)
            continue
        print(f"{cfg['name']}: {len(items)}件取得 [{time.monotonic() - step_start:.1f}秒]")
        candidates.extend(items)

    blocked_publishers = set(sources.get("blocked_publishers", []))
    for cfg in sources.get("rss_sources", []):
        step_start = time.monotonic()
        items = fetch_rss(cfg, blocked_publishers)
        print(f"{cfg['label']}: {len(items)}件取得 [{time.monotonic() - step_start:.1f}秒]")
        candidates.extend(items)
    return candidates


def find_best_match(title, pool):
    """poolの中からtitleに最も似ているものを探す。(similarity, item) を返す"""
    best_ratio = 0.0
    best_item = None
    for other in pool:
        ratio = title_similarity(title, other.get("title", ""))
        if ratio > best_ratio:
            best_ratio = ratio
            best_item = other
    return best_ratio, best_item


def cmd_collect(args):
    sources = load_sources()
    existing_items = load_news()
    by_link = {item["link"]: item for item in existing_items}
    today = date.today()

    candidates = collect_candidates(by_link, sources)
    total_fetched = len(candidates)

    # 完全一致タイトルの事前重複排除(同一記事がGoogle Newsの複数クエリでヒットするケース対応)
    seen_titles = set()
    deduped_candidates = []
    exact_dup_count = 0
    for item in candidates:
        key = item["title"].strip()
        if key in seen_titles:
            exact_dup_count += 1
            continue
        seen_titles.add(key)
        deduped_candidates.append(item)
    candidates = deduped_candidates
    if exact_dup_count:
        print(f"(タイトル完全一致の重複{exact_dup_count}件を事前に除外)")

    recent_cutoff = today - timedelta(days=DUP_COMPARE_WINDOW_DAYS)
    recent_pool = [
        it for it in existing_items
        if (parse_pub_str(it.get("pub_str", "")) or today) >= recent_cutoff
    ]
    # store_eventは保存期間が180日と長く、PR TIMES等での再配信がpub_str上の発表日から
    # 大きく遅れて(1か月以上後に)Google Newsに出てくることがあるため、店名部分一致チェックは
    # recent_pool(30日窓)に限定せず、保持期間中の全store_eventを対象にする(2026-08-15追加。
    # 「関東80店舗目！...グランドオープン」というPR TIMES記事が、pub_str上は既存store_event
    # (7/6開店)より46日遅れて収集されたため30日窓から外れており、重複検出をすり抜けた実例あり)。
    store_event_pool = [it for it in existing_items if it.get("retention_type") == "store_event"]

    existing_queue = load_json(REVIEW_QUEUE_PATH, [])
    pending_review_links = {e["item"]["link"] for e in existing_queue}
    excluded_links = load_excluded_links()

    new_count = updated_count = unchanged_count = auto_excluded_count = skipped_pending = skipped_excluded = expired_new_count = publisher_excluded_count = 0
    new_links_this_run = []
    review_items = []
    auto_log_entries = []
    run_ts = datetime.now(JST).strftime("%Y%m%d-%H%M")
    collected_at_iso = datetime.now(JST).isoformat()

    for item in candidates:
        link = item["link"]
        prev = by_link.get(link)

        if link in pending_review_links:
            # 前回のcollectで既にreview_queueに入っており、まだ判断されていない
            skipped_pending += 1
            continue

        if prev is None and link in excluded_links:
            # 過去に除外判定済み(ルールベース/AI判断)のリンク。同じ記事がソース側に
            # 載り続けているだけなので、再度重複判定・AIレビューにはかけない
            skipped_excluded += 1
            continue

        if prev is not None:
            if prev.get("retention_type") == "store_event":
                # store-addで手動登録した開店閉店情報は、後から同じリンクが別ソース
                # (一般のグルメRSS等)で再取得されても一切上書きしない(タイトル・カテゴリ・
                # 保存期間(6か月)を含め、手動登録の内容を常に正とする)
                unchanged_count += 1
                continue
            # 既存記事の更新(タイトル/日付の反映など)。重複判定は不要
            merged = {**prev, **item}
            # カテゴリは一度確定(ルールベース/AI判断)したら保持する。
            # ソース側のcategoryがnull(Google News等)/未確定のitemで上書きして消さないようにする
            if item.get("category") is None and prev.get("category") is not None:
                merged["category"] = prev["category"]
            merged["retention_type"] = compute_retention_type(merged)
            if merged == prev:
                unchanged_count += 1
            else:
                updated_count += 1
            by_link[link] = merged
            continue

        if item.get("publisher") in COLLECT_EXCLUDE_PUBLISHERS:
            # 千葉日報等、有料記事・過去記事再配信が多いpublisherは審査にすら回さず除外
            publisher_excluded_count += 1
            auto_log_entries.append({
                "run_ts": run_ts,
                "date": today.isoformat(),
                "ai_decision": "auto_exclude",
                "similarity": None,
                "title": item["title"],
                "link": link,
                "similar_to": "",
                "ai_reason": f"ルールベース: publisher({item.get('publisher')})が収集除外対象のため",
            })
            continue

        if WEATHER_ALERT_TITLE_PATTERN.search(item["title"]):
            publisher_excluded_count += 1
            auto_log_entries.append({
                "run_ts": run_ts,
                "date": today.isoformat(),
                "ai_decision": "auto_exclude",
                "similarity": None,
                "title": item["title"],
                "link": link,
                "similar_to": "",
                "ai_reason": "ルールベース: 気象警報の発表を伝えるだけの当日限りの速報記事のため",
            })
            continue

        if PROTECTED_TITLE_PATTERN.match(item["title"]):
            publisher_excluded_count += 1
            auto_log_entries.append({
                "run_ts": run_ts,
                "date": today.isoformat(),
                "ai_decision": "auto_exclude",
                "similarity": None,
                "title": item["title"],
                "link": link,
                "similar_to": "",
                "ai_reason": "ルールベース: WordPressのパスワード保護ページ(本文閲覧不可)のため",
            })
            continue

        if item.get("publisher") in POLITICAL_PARTY_PUBLISHERS:
            publisher_excluded_count += 1
            auto_log_entries.append({
                "run_ts": run_ts,
                "date": today.isoformat(),
                "ai_decision": "auto_exclude",
                "similarity": None,
                "title": item["title"],
                "link": link,
                "similar_to": "",
                "ai_reason": f"ルールベース: publisher({item.get('publisher')})が政党アカウントのため",
            })
            continue

        if (item.get("publisher") or "").startswith(CAMPFIRE_PUBLISHER_PREFIX):
            publisher_excluded_count += 1
            auto_log_entries.append({
                "run_ts": run_ts,
                "date": today.isoformat(),
                "ai_decision": "auto_exclude",
                "similarity": None,
                "title": item["title"],
                "link": link,
                "similar_to": "",
                "ai_reason": f"ルールベース: publisher({item.get('publisher')})がCAMPFIRE(クラウドファンディング)のため",
            })
            continue

        item["collected_at"] = collected_at_iso
        category = item.get("category") or guess_category_from_title(item["title"])
        item["category"] = category
        item["retention_type"] = compute_retention_type(item)

        if is_expired(item, today):
            # 掲載期限(3か月/6か月、またはイベント開催終了日)を超えた記事。追加してもすぐ除去
            # されるだけなので除外済みとして記録し、次回以降のcollectで再度処理
            # (重複判定・AI判断)しないようにする
            expired_new_count += 1
            event_end = item.get("event_end_date")
            reason = (
                f"ルールベース: イベント開催終了日({event_end})から{EVENT_END_GRACE_DAYS}日を超えた記事のため対象外"
                if event_end else "ルールベース: 掲載期限(3か月/6か月)を超えた記事のため対象外"
            )
            auto_log_entries.append({
                "run_ts": run_ts,
                "date": today.isoformat(),
                "ai_decision": "exclude",
                "similarity": None,
                "title": item["title"],
                "link": link,
                "similar_to": "",
                "ai_reason": reason,
            })
            continue

        similarity, similar_item = find_best_match(item["title"], recent_pool)

        if similarity >= DUP_AUTO_EXCLUDE_THRESHOLD:
            auto_excluded_count += 1
            auto_log_entries.append({
                "run_ts": run_ts,
                "date": today.isoformat(),
                "ai_decision": "auto_exclude",
                "similarity": round(similarity, 2),
                "title": item["title"],
                "link": link,
                "similar_to": similar_item.get("title", "") if similar_item else "",
                "ai_reason": "ルールベース: 類似度80%以上のため自動除外",
            })
            continue

        # タイトル類似度だけでは、store-add登録済みの定型タイトル(「【日付 種別】店名」)と
        # 通常収集された自然文タイトルの記事が同一店舗の話でも類似度が低く出て見逃してしまう
        # (例: 「【7月31日 閉店】くるまやラーメン印西木下東店」 vs 「くるまやラーメン印西木下東店が...閉店します」)。
        # そのため、既存のstore_eventエントリの店名がタイトルに部分一致する場合は
        # 類似度に関わらず要確認(needs_dedup_review)に回す(自動除外はしない。強盗事件等
        # 別の話題の可能性もあるため、必ず人手/AIで内容を確認させる)。
        store_match_item = None
        # 店名・記事タイトルとも空白の有無や括弧の有無で表記揺れがある
        # (例:「くるまやラーメン 印西木下東店」、「魁力屋「ジョイフル本田千葉ニュータウン店」」)ため、
        # 空白と主要な括弧・引用符を除去してから部分一致を見る
        def _normalize_for_match(s):
            return re.sub(r"[\s「」『』()（）\"'　]+", "", s)
        candidate_title_norm = _normalize_for_match(item["title"])
        for other in store_event_pool:
            store_name = extract_store_event_name(other.get("title", ""))
            if not store_name:
                continue
            if _normalize_for_match(store_name) in candidate_title_norm:
                store_match_item = other
                break
        if store_match_item is not None:
            similar_item = store_match_item

        needs_dedup_review = (DUP_REVIEW_THRESHOLD <= similarity < DUP_AUTO_EXCLUDE_THRESHOLD) or store_match_item is not None
        needs_category = category is None

        if not needs_dedup_review and not needs_category:
            by_link[link] = item
            recent_pool.append(item)
            new_count += 1
            new_links_this_run.append(link)
            continue

        review_items.append({
            "review_id": f"{run_ts}-{len(review_items)+1}",
            "item": item,
            "needs_dedup_review": needs_dedup_review,
            "needs_category": needs_category,
            "similarity": round(similarity, 2) if needs_dedup_review else None,
            "similar_to": similar_item.get("title", "") if (needs_dedup_review and similar_item) else None,
            "similar_to_link": similar_item.get("link", "") if (needs_dedup_review and similar_item) else None,
            "cross_check": False,
            "decision": None,
            "category_decision": None,
            "reason": None,
        })
        # 同一記事が別クエリでも出てくることがあるので、以降の候補との類似度比較対象にも加える
        recent_pool.append(item)

    merged_all = list(by_link.values())
    final_items = [it for it in merged_all if not is_expired(it, today)]
    expired_count = len(merged_all) - len(final_items)

    save_json_atomic(NEWS_PATH, final_items)
    append_ai_log(auto_log_entries)

    if new_links_this_run:
        mark_new_badge_links(new_links_this_run)

    combined_queue = existing_queue + review_items
    if combined_queue:
        save_json_atomic(REVIEW_QUEUE_PATH, combined_queue)
    elif REVIEW_QUEUE_PATH.exists():
        REVIEW_QUEUE_PATH.unlink()

    new_article_count = total_fetched - exact_dup_count - updated_count - unchanged_count
    print(
        f"\n取得記事件数{total_fetched}件 / 新規の記事件数{new_article_count}件"
    )
    print(
        f"合算: 新規{new_count} / 更新{updated_count} / 変化なし{unchanged_count} / "
        f"期限切れ{expired_count} / 自動除外(重複80%以上){auto_excluded_count} / "
        f"自動除外(publisher){publisher_excluded_count} / "
        f"要AI判断(今回){len(review_items)}件 / 判断待ち(前回から){skipped_pending}件 / "
        f"除外済みスキップ{skipped_excluded}件 / 新規だが掲載期限切れ{expired_new_count}件"
    )
    if review_items:
        print(f"→ {REVIEW_QUEUE_PATH.name} を確認し、decision/category_decision を記入した上で "
              f"`python pipeline.py apply-review` を実行してください。")
    print(f"合計 {len(final_items)} 件を {NEWS_PATH} に保存しました")


# ============================================================
# apply-review: レビュー結果の反映
# ============================================================

def cmd_apply_review(args):
    queue = load_json(REVIEW_QUEUE_PATH, [])
    if not queue:
        print("review_queue.json が空です。反映すべき項目はありません。")
        return

    existing_items = load_news()
    by_link = {item["link"]: item for item in existing_items}
    today = date.today()
    run_ts = datetime.now(JST).strftime("%Y%m%d-%H%M")

    kept = excluded = pending = 0
    kept_links_this_run = []
    log_entries = []
    remaining_queue = []

    for entry in queue:
        decision = entry.get("decision")
        item = entry["item"]

        if decision not in ("keep", "exclude"):
            remaining_queue.append(entry)
            pending += 1
            continue

        if decision == "exclude":
            excluded += 1
            # 除外リンクの記憶(次回collectでの再判定スキップ)のため、理由の種別を問わず必ず記録する
            log_entries.append({
                "run_ts": run_ts,
                "date": today.isoformat(),
                "ai_decision": "exclude",
                "similarity": entry.get("similarity"),
                "title": item["title"],
                "link": item["link"],
                "similar_to": entry.get("similar_to", ""),
                "ai_reason": entry.get("reason") or "AI判断: 重複と判定",
            })
            continue

        # decision == "keep"
        category = entry.get("category_decision") or item.get("category")
        if entry.get("needs_category") and not category:
            print(f"[WARN] カテゴリ未指定のためスキップ: {item['title']}", file=sys.stderr)
            remaining_queue.append(entry)
            pending += 1
            continue

        item["category"] = category
        item["retention_type"] = compute_retention_type(item)
        by_link[item["link"]] = item
        kept += 1
        kept_links_this_run.append(item["link"])
        if entry.get("needs_dedup_review") or entry.get("cross_check"):
            log_entries.append({
                "run_ts": run_ts,
                "date": today.isoformat(),
                "ai_decision": "keep",
                "similarity": entry.get("similarity"),
                "title": item["title"],
                "link": item["link"],
                "similar_to": entry.get("similar_to", ""),
                "ai_reason": entry.get("reason") or "AI判断: 別記事と判定し採用",
            })

    merged_all = list(by_link.values())
    final_items = [it for it in merged_all if not is_expired(it, today)]
    expired_count = len(merged_all) - len(final_items)

    save_json_atomic(NEWS_PATH, final_items)
    append_ai_log(log_entries)

    if kept_links_this_run:
        mark_new_badge_links(set(kept_links_this_run))

    if remaining_queue:
        save_json_atomic(REVIEW_QUEUE_PATH, remaining_queue)
    elif REVIEW_QUEUE_PATH.exists():
        REVIEW_QUEUE_PATH.unlink()

    print(f"反映結果: 採用{kept} / 除外{excluded} / 未判定(据え置き){pending} / 期限切れ{expired_count}")
    print(f"合計 {len(final_items)} 件を {NEWS_PATH} に保存しました")


# ============================================================
# build: HTML生成
# ============================================================

CATEGORY_COLORS = {
    "新着":           ("#FFE3F2", "#FF3DA6", "#B5106B"),
    "話題・その他":   ("#E3E5EA", "#6B7280", "#374151"),
    "イベント・文化": ("#F3E8FF", "#9333EA", "#6B21A8"),
    "市政・行政":     ("#E8F1FF", "#2563EB", "#1E3A8A"),
    "開発・暮らし":   ("#ECFDF5", "#10B981", "#065F46"),
    "開店・閉店":     ("#FEF2F2", "#EF4444", "#991B1B"),
    "鎌ヶ谷・白井":   ("#FBDFB8", "#F97316", "#9A3412"),
    "イオンモール千葉ニュータウン": ("#ECFEFF", "#06B6D4", "#155E75"),
    "牧の原モア": ("#EDE8F8", "#6B4FA7", "#3A1F6E"),
    "ジョイフル本田千葉ニュータウン店": ("#EFE3D5", "#8B5E34", "#4A2E15"),
}
CATEGORY_ICONS = {
    "新着": "🆕",
    "話題・その他": "📰", "イベント・文化": "🎉", "市政・行政": "🏛",
    "開発・暮らし": "🌱", "開店・閉店": "🏪", "鎌ヶ谷・白井": "🗺",
    "イオンモール千葉ニュータウン": "🛍", "牧の原モア": "📍",
    "ジョイフル本田千葉ニュータウン店": "🔨",
}
SCRAPED_COLOR = ("#EDE8F8", "#6B4FA7", "#3A1F6E")
SCRAPED_ICON = "📍"
MAX_ITEMS_PER_CAT = 20
CATEGORY_MAX_ITEMS = {"ジョイフル本田千葉ニュータウン店": 40, "市政・行政": 40}
NEW_ARRIVALS_COUNT = 20
# 印西市役所(publisher「印西市」)の記事は件数が多く「新着」バッジ・「新着」カテゴリを
# 埋め尽くしてしまうため対象外とする(市政・行政カテゴリ自体には引き続き通常通り表示される)
NEW_ARRIVALS_EXCLUDE_PUBLISHERS = {"印西市"}
# 千葉日報(chibanippo.co.jp)は有料記事(paywall)の割合が高く、さらに過去記事の再配信が
# 新着として再ヒットする事例も確認されたため、2026-08-10からcollect時点で収集自体から
# 除外する(review_queue.jsonでのAI判断にすら回さない)。毎日新聞も同様の理由で2026-08-20追加。
COLLECT_EXCLUDE_PUBLISHERS = {"chibanippo.co.jp", "毎日新聞", "mainichi.jp"}
# 大雨警報・特別警報等、当日限りの気象警報の発表を伝えるだけの速報記事は採用しない(2026-08-13追加)。
# 号外NET等ソース側で最初からカテゴリ(鎌ヶ谷・白井等)が付いている記事はneeds_category=Falseとなり
# review_queueを経由せず自動採用されてしまうため、collect時点でタイトルパターンで弾く。
# 「大雨(8月13日)に係る避難所情報」のような実用情報(避難所等)は「警報」「記録的」を含まないため対象外のまま残る。
WEATHER_ALERT_TITLE_PATTERN = re.compile(r"警報|記録的.{0,5}(大)?雨")
# WordPressのパスワード保護ページはタイトルが「保護中: 」で始まり、本文が閲覧できない
# (パスワードを知らないと中身が見れない)ため、収集時点で自動除外する(2026-08-19追加。
# 千葉ほくそうパルケ(inzaiparque.com)で実例あり)
PROTECTED_TITLE_PATTERN = re.compile(r"^保護中:\s*")
# publisherが政党の公式アカウント名の記事は、行政ニュース(議会開会等)であっても発信元が
# 政治活動の宣伝を兼ねるため採用しない(2026-08-29追加。実例:「第3回印西市議会定例会開会」publisher:公明党)。
# 既存の「政治家個人の街頭演説・選挙活動系記事を除外する」運用ルールと同じ考え方を、
# 政党アカウント発信の記事にもcollect時点の自動除外として適用する。
POLITICAL_PARTY_PUBLISHERS = {
    "自由民主党", "自民党", "公明党", "立憲民主党", "日本維新の会", "維新の会",
    "国民民主党", "日本共産党", "共産党", "れいわ新選組", "社会民主党", "社民党",
    "参政党", "NHK党", "みんなでつくる党",
}
# CAMPFIRE(クラウドファンディングサイト)発信の記事は、個人・団体の資金調達ページの
# 宣伝が実質でニュース性が低いため、2026-08-29追加でcollect時点から自動除外する
# (実例:「古民家占いカフェをオープンします」という個人事業の資金調達ページ)。
CAMPFIRE_PUBLISHER_PREFIX = "CAMPFIRE"
# 上記の除外対象を主に含むカテゴリには、カテゴリ見出しに「(新着対象外)」と表示して分かりやすくする
# (実際の除外判定はpublisher単位のため、同じカテゴリ内でも除外されない記事が混在する場合はある)
NEW_ARRIVALS_EXCLUDE_CATEGORIES = {"市政・行政"}
SCRAPED_MAX_ITEMS = 20
SCRAPED_MAX_DAYS = 180
CATEGORY_CUTOFF_DAYS = {"開店・閉店": 180, "イオンモール千葉ニュータウン": 180, "鎌ヶ谷・白井": 90, "牧の原モア": 180}
DEFAULT_CUTOFF_DAYS = 90

PUBLISHER_ALIASES = {"印西市": "印西市役所"}
PUBLISHER_URL_FALLBACKS = [
    ("kamagaya-shiroi-inzai.goguynet.jp", "鎌ヶ谷白井インザイ.jp"),
    ("goguynet.jp", "goguynet"),
]

CSS = """*{box-sizing:border-box;margin:0;padding:0}
body{font-family:-apple-system,BlinkMacSystemFont,'Hiragino Sans','Hiragino Kaku Gothic ProN','Noto Sans JP',sans-serif;background:#f0f0ec;color:#1a1a18;line-height:1.6}
a{text-decoration:none;color:inherit}
.wrap{max-width:720px;margin:0 auto;padding:0 0 48px}
header{background:#fff;border-bottom:1px solid #e0e0d8;padding:14px 20px;display:flex;align-items:center;gap:20px;position:sticky;top:0;z-index:10}
.logo{font-size:20px;font-weight:600;color:#1a1a18;margin-right:auto}.logo span{color:#1D9E75}
.updated{font-size:11px;color:#888;text-align:right}
.train-dir-toggle{background:#f5f5f1;border:1px solid #d8d8d0;color:#1a1a18;font-size:11px;font-weight:700;padding:6px 12px;border-radius:16px;cursor:pointer;white-space:nowrap}
.train-dir-toggle:hover{background:#ececE6}
.hero{background:#fff;margin:0 0 16px;padding:18px 20px;border-bottom:3px solid #1D9E75;display:flex;justify-content:space-between;align-items:center;gap:6px;flex-wrap:wrap}
.today-badge{display:inline-block;font-size:8px;font-weight:700;background:#e74c3c;color:#fff;padding:0 4px;border-radius:3px;margin-left:6px;vertical-align:middle;line-height:1.5}
.new-badge{display:inline-block;font-size:8px;font-weight:700;background:#223A70;color:#fff;padding:0 4px;border-radius:3px;margin-left:6px;vertical-align:middle;line-height:1.5}
.train-widget{flex:0 0 auto}
.train-widget-title{font-size:10px;font-weight:700;color:#888;letter-spacing:.02em;margin-bottom:8px}
.train-widget-title .train-direction{font-weight:400;margin-left:2px}
.train-columns{display:flex}
.train-columns-hidden{display:none}
.train-divider{width:1px;align-self:stretch;background:#e0e0d8;margin:0 6px 0 10px}
.train-station-name{font-size:13px;font-weight:700;color:#1a1a18;margin-bottom:6px}
.train-item{font-size:12px;color:#333;padding:3px 0;display:flex;gap:5px;align-items:baseline;white-space:nowrap;font-variant-numeric:tabular-nums}
.train-time{font-weight:700;color:#1D9E75;min-width:43px}
.train-dot{display:inline-block;width:11px;color:#1D9E75;font-size:9px;position:relative;top:-1px}
.train-type{font-size:10px;color:#888;min-width:22px}
.train-type-express{color:#e07b00}
.train-dest{flex:1;overflow:hidden;text-overflow:ellipsis;max-width:82px}
.train-countdown{font-size:10px;color:#bbb;width:56px;flex-shrink:0}
.train-countdown-next{color:#555}
.train-note{font-size:9px;color:#aaa;margin-top:6px;padding-left:11px}
.weather-block{flex-shrink:0;display:flex;flex-direction:column;align-items:center;text-decoration:none;color:inherit}
.weather-widget{display:flex;gap:8px}
.weather-day{background:#f5f5f1;border-radius:8px;padding:8px 12px;text-align:center;width:70px;box-sizing:content-box}
.weather-day-label{display:block;font-size:10px;color:#888;font-weight:700;margin-bottom:2px}
.weather-day-label .wd-sun{color:#ff3000}
.weather-day-label .wd-sat{color:#0060ff}
.weather-icon{display:block;height:28px;width:auto;margin:0 auto}
.weather-name{display:block;font-size:10px;color:#888;font-weight:700;margin-top:2px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.weather-temp{display:block;font-size:12px;font-weight:700;margin-top:2px}
.weather-temp .tmax{color:#f64d00}
.weather-temp .tmin{color:#0075f3;font-weight:700}
.weather-pop{display:block;font-size:10px;color:#2563EB;margin-top:1px}
.weather-title{font-size:10px;font-weight:700;color:#888;letter-spacing:.02em;text-align:center;margin-bottom:4px}
@media(max-width:480px){
header{padding:10px 12px;flex-wrap:wrap;row-gap:6px}
.logo{font-size:16px;order:1}
.updated{font-size:9px;order:2}
.train-dir-toggle{font-size:9px;padding:4px 8px;border-radius:12px;order:3;flex-basis:100%;text-align:center}
.hero{padding:10px;gap:12px;flex-wrap:nowrap;justify-content:center}
.train-widget-title{font-size:7px;margin-bottom:3px}
.train-divider{margin:0 2px 0 6px}
.train-station-name{font-size:9px;margin-bottom:2px}
.train-item{font-size:8px;gap:1px;padding:1px 0}
.train-time{min-width:32px}
.train-dot{width:6px;font-size:6px}
.train-type{font-size:7px;min-width:13px}
.train-countdown{font-size:7px;width:20px}
.train-dest{max-width:40px}
.train-note{font-size:6px;padding-left:6px;margin-top:3px}
.weather-widget{gap:3px}
.weather-day{padding:3px 5px;width:49px;box-sizing:content-box}
.weather-icon{height:18px}
.weather-day-label,.weather-pop{font-size:7px}
.weather-name{font-size:7px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.weather-temp{font-size:9px}
.weather-title{font-size:7px;margin-bottom:2px}
}
.cat-grid{display:grid;grid-template-columns:1fr 1fr;gap:12px;padding:0 12px 4px;grid-auto-rows:270px}
.scraped-grid{display:grid;grid-template-columns:1fr 1fr;gap:12px;padding:12px 12px 4px;grid-auto-rows:200px}
.cat-section{border-radius:10px;overflow:hidden;box-shadow:0 1px 4px rgba(0,0,0,.07);display:flex;flex-direction:column}
.cat-header{display:flex;align-items:center;gap:8px;padding:10px 12px}
.cat-icon{font-size:15px}
.cat-name{font-size:12px;font-weight:700;flex:1}
.cat-count{font-size:11px;font-weight:600}
.news-item{display:flex;flex-direction:column;gap:3px;padding:9px 12px;background:#fff;border-top:1px solid #ededea;transition:background .15s}
.news-item:hover{background:#f9f9f6}
.news-item.today{background:#fffbe8}
.news-item.today:hover{background:#fff5cc}
.news-item.recent{background:#fffbe8}
.news-item.recent:hover{background:#fff5cc}
.news-title{font-size:13px;font-weight:500;color:#1a1a18;line-height:1.5}
.news-item:hover .news-title{color:#1D9E75}
.news-date{font-size:10px;color:#aaa}
.cat-items{flex:1;overflow-y:auto;min-height:0}
.cat-items::-webkit-scrollbar{width:4px}
.cat-items::-webkit-scrollbar-track{background:transparent}
.cat-items::-webkit-scrollbar-thumb{background:#d0d0cc;border-radius:2px}
.no-news{padding:20px;color:#888;font-size:14px;background:#fff;margin:12px}
@media(max-width:480px){.cat-grid,.scraped-grid{grid-template-columns:1fr;gap:20px}}
footer{text-align:center;font-size:11px;color:#aaa;padding:24px 20px 0}
"""

GA_TAG = """<!-- Google tag (gtag.js) -->
<script async src="https://www.googletagmanager.com/gtag/js?id=G-89CXHHR0XZ"></script>
<script>
  window.dataLayer = window.dataLayer || [];
  function gtag(){dataLayer.push(arguments);}
  gtag('js', new Date());
  gtag('config', 'G-89CXHHR0XZ');
</script>
"""


def normalize_publisher(pub, link=""):
    if pub in PUBLISHER_ALIASES:
        return PUBLISHER_ALIASES[pub]
    if not pub:
        for domain, name in PUBLISHER_URL_FALLBACKS:
            if domain in (link or ""):
                return name
    return pub



KAITEN_LABEL_PATTERN = re.compile(r"^【(\d{4}年\d{1,2}月\d{1,2}日\s*(?:開店|閉店|リニューアル)|(?:開店|閉店|リニューアル)日不明)】")
KAITEN_DATE_IN_TITLE_PATTERN = re.compile(r"(\d{1,2})月(\d{1,2})日")


def kaiten_label(item):
    """開店・閉店カテゴリのタイトル先頭を【YYYY年M月D日 種別】(不明なら【種別日不明】)に統一する。
    store-add由来のstore_eventは既にこの形式でtitleが確定しているため素通しする。それ以外の
    (RSS等から自動分類された)regular記事は、記事自身の見出しが「【印西市】...」等の無関係な
    括弧で始まることが多く、旧実装(先頭が「【」かどうかだけで判定)はこれを誤って
    「既にフォーマット済み」と誤認していたため、正しいラベル形式にのみマッチする正規表現に変更した
    (2026-08-29)。あわせて、タイトル中に「8月16日」のような具体的な日付があればpub_strの年と
    組み合わせて日付入りラベルを生成し、無ければ【開店日不明】等にフォールバックする。
    """
    if item.get("category") != "開店・閉店":
        return item.get("title", "")
    title = item.get("title", "")
    if KAITEN_LABEL_PATTERN.match(title):
        return title
    if "リニューアル" in title:
        kind = "リニューアル"
    elif "閉店" in title or "閉業" in title:
        kind = "閉店"
    else:
        kind = "開店"
    m = KAITEN_DATE_IN_TITLE_PATTERN.search(title)
    pub_date = parse_pub_str(item.get("pub_str", ""))
    if m and pub_date:
        month, day = int(m.group(1)), int(m.group(2))
        try:
            candidate = date(pub_date.year, month, day)
            # 記事日付より60日以上過去になる場合は、年をまたいだ翌年の予定と判断する
            if (pub_date - candidate).days > 60:
                candidate = date(pub_date.year + 1, month, day)
            return f"【{candidate.year}年{candidate.month}月{candidate.day}日 {kind}】{title}"
        except ValueError:
            pass
    return f"【{kind}日不明】{title}"


def discovery_date(item):
    """記事の「発見日」= collected_at(このパイプラインが初めて収集した日)の日付。
    collected_atが無い(2026-08-08より前からある)記事はpub_str(元記事の発表日)にフォールバックする。
    表示順・「新着」ハイライト(3日以内)・「今日」バッジの基準として使う(data-pub属性経由)。
    news-date欄に表示するテキスト自体は引き続きpub_strをそのまま使う——「いつ見つけたか」(新着性の判定)と
    「実際いつの記事か」(表示情報)を分離するため。両者を混在させる(ハイライト等はpub_str基準、並び順だけ
    collected_at基準、等)と、上位に来た記事がハイライトされない等の見た目の不整合が起きるため、
    新着性に関わる判定は必ずこの関数で統一する(2026-08-08)。
    """
    collected_at = item.get("collected_at")
    if collected_at:
        try:
            return datetime.fromisoformat(collected_at).date()
        except ValueError:
            pass
    return parse_pub_str(item.get("pub_str", ""))


def render_item(item, new_links):
    pub = normalize_publisher(item.get("publisher", ""), item.get("link", ""))
    pub_html = " · " + html.escape(pub) if pub else ""
    d = discovery_date(item)
    data_pub = (' data-pub="' + d.isoformat() + '"') if d else ""
    title = kaiten_label(item)
    new_html = '<span class="new-badge">新着</span>' if item.get("link") in new_links else ""
    # announce_str(記事発表日)があれば日付欄はそちらを優先表示する。開店・閉店情報は
    # pub_strに開店/閉店の実施日を入れる設計のため、記事が実際に発表された日を別途知りたい場合に使う
    date_text = item.get("announce_str") or item.get("pub_str", "")
    return (
        '<a class="news-item"' + data_pub + ' href="' + html.escape(item["link"]) + '" target="_blank" rel="noopener">'
        + '<span class="news-title">' + html.escape(title) + "</span>"
        + '<span class="news-date">' + html.escape(date_text) + pub_html
        + '<span class="today-badge" style="display:none">今日</span>' + new_html + "</span>"
        + "</a>"
    )


def build_html(articles):
    now = datetime.now(JST)
    now_str = f"{now.year}年{now.month}月{now.day}日 {now.strftime('%H:%M')}"
    today = now.date()
    cutoff = today - timedelta(days=SCRAPED_MAX_DAYS)
    publisher_by_link = {a.get("link"): a.get("publisher") for a in articles}
    new_links = {
        link for link in active_new_badge_links()
        if publisher_by_link.get(link) not in NEW_ARRIVALS_EXCLUDE_PUBLISHERS
    }
    if not new_links:
        # 直近3時間の新着が新着除外対象(印西市役所等)しかなかった場合、「最後の更新が
        # 新着で分かるようにする」という目的を満たすため、除外対象を除いた直近1件まで
        # 3時間ウィンドウを超えて遡って表示する
        fallback_link = fallback_new_badge_link()
        if fallback_link in publisher_by_link:
            new_links = {fallback_link}

    main_arts_all = [a for a in articles if a.get("category") in CATEGORY_ORDER]
    scraped_arts = [a for a in articles if a.get("category") not in CATEGORY_ORDER]

    def date_ok(item):
        d = parse_pub_str(item.get("pub_str", ""))
        if not d:
            return True
        days = CATEGORY_CUTOFF_DAYS.get(item.get("category", ""), DEFAULT_CUTOFF_DAYS)
        return d >= today - timedelta(days=days)

    main_arts = [a for a in main_arts_all if date_ok(a)]

    # 発見日(discovery_date)が同日の記事は、news.json内での追加順(=後から追加されたもの)が上に来るようにする
    added_order = {id(a): i for i, a in enumerate(articles)}
    main_arts.sort(key=lambda a: (discovery_date(a) or date.min, added_order[id(a)]), reverse=True)

    weather_days = fetch_weather()
    weather_html = ""
    if weather_days:
        weekday_ja = ["月", "火", "水", "木", "金", "土", "日"]
        cards = []
        for d in weather_days:
            pop_html = '<span class="weather-pop">☂' + str(d["pop"]) + "%</span>" if d["pop"] is not None else ""
            weekday_idx = d.get("weekday")
            wd_char = weekday_ja[weekday_idx] if weekday_idx is not None else ""
            daytype = d.get("daytype")
            if daytype == "sun":
                wd_html = '(<span class="wd-sun">' + wd_char + "</span>)"
            elif daytype == "sat":
                wd_html = '(<span class="wd-sat">' + wd_char + "</span>)"
            else:
                wd_html = "(" + wd_char + ")"
            day_label_html = html.escape(d["label"]) + wd_html
            weather_name_html = '<span class="weather-name">' + html.escape(d["weather_label"]) + "</span>" if d["weather_label"] else ""
            cards.append(
                '<div class="weather-day">'
                + '<span class="weather-day-label">' + day_label_html + "</span>"
                + '<img class="weather-icon" src="' + html.escape(d["icon"]) + '" alt="' + html.escape(d["weather_label"]) + '" title="' + html.escape(d["weather_label"]) + '">'
                + weather_name_html
                + '<span class="weather-temp"><span class="tmax">' + str(d["temp_max"]) + '°</span><span class="tmin">/' + str(d["temp_min"]) + "°</span></span>"
                + pop_html
                + "</div>"
            )
        weather_html = (
            '<a class="weather-block" href="' + WEATHER_SITE_URL + '" target="_blank" rel="noopener">'
            + '<div class="weather-title">印西の天気</div>'
            + '<div class="weather-widget">' + "".join(cards) + "</div>"
            + "</a>"
        )

    train_data, train_holidays = load_or_fetch_train_data()

    def build_train_columns_html(stations: dict) -> str:
        parts = []
        for i, key in enumerate(stations):
            if i > 0:
                parts.append('<div class="train-divider"></div>')
            entry = train_data.get(key, {"name": stations[key]["name"]})
            parts.append(
                '<div class="train-station">'
                + '<div class="train-station-name">' + html.escape(entry["name"]) + "</div>"
                + '<div class="train-list" id="train-list-' + key + '"></div>'
                + "</div>"
            )
        return "".join(parts)

    train_group_columns_html = ""
    for i, group in enumerate(TRAIN_GROUPS):
        hidden_cls = "" if i == 0 else " train-columns-hidden"
        train_group_columns_html += (
            '<div class="train-columns' + hidden_cls + '" id="train-columns-' + group["key"] + '">'
            + build_train_columns_html(group["stations"])
            + "</div>"
        )
    train_html = (
        '<div class="train-widget">'
        + '<div class="train-widget-title" id="train-widget-title">'
        + '<span id="train-title-name">北総鉄道</span>'
        + '<span class="train-direction" id="train-direction">(' + html.escape(TRAIN_GROUPS[0]["direction_label"]) + ")</span>"
        + "</div>"
        + train_group_columns_html
        + '<div class="train-note"><span class="train-dot">●</span>は当駅始発</div>'
        + "</div>"
    )
    top_html = '<div class="hero">' + train_html + weather_html + "</div>"

    cat_map = defaultdict(list)
    for item in main_arts:
        cat_map[item.get("category", "話題・その他")].append(item)

    active_cats = [
        (cat, cat_map.get(cat, [])[:CATEGORY_MAX_ITEMS.get(cat, MAX_ITEMS_PER_CAT)])
        for cat in CATEGORY_ORDER if cat_map.get(cat)
    ]
    grid_html = ""
    new_arrivals_pool = [a for a in main_arts if a.get("publisher") not in NEW_ARRIVALS_EXCLUDE_PUBLISHERS]
    latest_arts = new_arrivals_pool[:NEW_ARRIVALS_COUNT]
    if latest_arts:
        bg, fg, dark = CATEGORY_COLORS["新着"]
        rows = "".join(render_item(i, new_links) for i in latest_arts)
        grid_html += (
            '<div class="cat-section">'
            + '<div class="cat-header" style="background:' + bg + ';border-left:4px solid ' + fg + ';">'
            + '<span class="cat-icon">' + CATEGORY_ICONS["新着"] + "</span>"
            + '<span class="cat-name" style="color:' + dark + ';"> 新着</span>'
            + '<span class="cat-count" style="color:' + fg + ';"> ' + str(len(latest_arts)) + "件</span>"
            + "</div>"
            + '<div class="cat-items">' + rows + "</div>"
            + "</div>"
        )
    for cat, items in active_cats:
        bg, fg, dark = CATEGORY_COLORS[cat]
        rows = "".join(render_item(i, new_links) for i in items)
        cat_label = cat + "(新着対象外)" if cat in NEW_ARRIVALS_EXCLUDE_CATEGORIES else cat
        grid_html += (
            '<div class="cat-section">'
            + '<div class="cat-header" style="background:' + bg + ';border-left:4px solid ' + fg + ';">'
            + '<span class="cat-icon">' + CATEGORY_ICONS[cat] + "</span>"
            + '<span class="cat-name" style="color:' + dark + ';"> ' + html.escape(cat_label) + "</span>"
            + '<span class="cat-count" style="color:' + fg + ';"> ' + str(len(items)) + "件</span>"
            + "</div>"
            + '<div class="cat-items">' + rows + "</div>"
            + "</div>"
        )
    sections_html = '<div class="cat-grid">' + grid_html + "</div>" if grid_html else '<p class="no-news">現在ニュースを取得できませんでした。</p>'

    scraped_map = defaultdict(list)
    for item in scraped_arts:
        scraped_map[item.get("category") or "地域情報"].append(item)

    scraped_html = ""
    for site, items in scraped_map.items():
        items = sorted(items, key=lambda a: parse_pub_str(a.get("pub_str", "")) or date.min, reverse=True)
        filtered = [i for i in items if (parse_pub_str(i.get("pub_str", "")) or cutoff) >= cutoff][:SCRAPED_MAX_ITEMS]
        if not filtered:
            continue
        bg, fg, dark = SCRAPED_COLOR
        rows = "".join(render_item(i, new_links) for i in filtered)
        scraped_html += (
            '<div class="cat-section">'
            + '<div class="cat-header" style="background:' + bg + ';border-left:4px solid ' + fg + ';">'
            + '<span class="cat-icon">' + SCRAPED_ICON + "</span>"
            + '<span class="cat-name" style="color:' + dark + ';"> ' + html.escape(site) + "</span>"
            + '<span class="cat-count" style="color:' + fg + ';"> ' + str(len(filtered)) + "件</span>"
            + "</div>"
            + '<div class="cat-items">' + rows + "</div>"
            + "</div>"
        )
    if scraped_html:
        sections_html += '<div class="scraped-grid">' + scraped_html + "</div>"

    train_data_json = json.dumps(
        {k: {"weekday": v["weekday"], "weekend": v["weekend"]} for k, v in train_data.items()},
        ensure_ascii=False,
    )
    holidays_json = json.dumps(train_holidays, ensure_ascii=False)
    # ボタンのラベルは「次に切り替わる先」を表す(=次のグループ自身の自己紹介ラベル)ため、
    # 現グループiのtoggleLabelには(i+1)番目のグループのown_toggle_labelを充てる
    train_group_meta_json = json.dumps({
        TRAIN_GROUPS[i]["key"]: {
            "name": "北総鉄道",
            "direction": "(" + TRAIN_GROUPS[i]["direction_label"] + ")",
            "toggleLabel": TRAIN_GROUPS[(i + 1) % len(TRAIN_GROUPS)]["own_toggle_label"],
        }
        for i in range(len(TRAIN_GROUPS))
    }, ensure_ascii=False)
    train_group_keys_json = json.dumps([g["key"] for g in TRAIN_GROUPS], ensure_ascii=False)
    inzai_stop_types_json = json.dumps(sorted(INZAI_MAKINOHARA_STOP_TYPES), ensure_ascii=False)
    train_script = (
        "<script>\n"
        f"var TRAIN_DATA={train_data_json};\n"
        f"var JP_HOLIDAYS={holidays_json};\n"
        f"var TRAIN_GROUP_META={train_group_meta_json};\n"
        f"var TRAIN_GROUP_KEYS={train_group_keys_json};\n"
        f"var INZAI_STOP_TYPES={inzai_stop_types_json};\n"
        "(function(){\n"
        "  function pad2(n){return String(n).padStart(2,\"0\");}\n"
        "  function renderTrains(){\n"
        "    var now=new Date(new Date().toLocaleString(\"en-US\",{timeZone:\"Asia/Tokyo\"}));\n"
        "    var todayStr=now.getFullYear()+\"-\"+pad2(now.getMonth()+1)+\"-\"+pad2(now.getDate());\n"
        "    var wd=now.getDay();\n"
        "    var dayType=(JP_HOLIDAYS.indexOf(todayStr)!==-1||wd===0||wd===6)?\"weekend\":\"weekday\";\n"
        "    var nowSec=now.getHours()*3600+now.getMinutes()*60+now.getSeconds();\n"
        "    var isNarrow=window.innerWidth<=480;\n"
        "    Object.keys(TRAIN_DATA).forEach(function(key){\n"
        "      var st=TRAIN_DATA[key];\n"
        "      var container=document.getElementById(\"train-list-\"+key);\n"
        "      if(!container) return;\n"
        "      var dayList=st[dayType]||[];\n"
        "      var candidates=dayList.map(function(t){\n"
        "        var hm=t.time.split(\":\");\n"
        "        var tSec=(+hm[0])*3600+(+hm[1])*60;\n"
        "        return {t:t, remain:tSec-nowSec};\n"
        "      }).filter(function(x){return x.remain>=0;});\n"
        "      var FAR_SEC=99*60;\n"
        "      var list=candidates.slice(0,3);\n"
        "      while(list.length<3){ list.push(null); }\n"
        "      container.innerHTML=list.map(function(x,i){\n"
        "        if(x===null){\n"
        "          var emptyCd=isNarrow?\"--:--\":\"あと--分--秒\";\n"
        "          return '<div class=\"train-item\"><span class=\"train-time\"><span class=\"train-dot\"></span>--:--</span><span class=\"train-type\">--</span><span class=\"train-dest\">-----</span><span class=\"train-countdown\">'+emptyCd+'</span></div>';\n"
        "        }\n"
        "        var m=Math.floor(x.remain/60), s=x.remain%60;\n"
        "        var typeCls=INZAI_STOP_TYPES.indexOf(x.t.type)===-1?\" train-type-express\":\"\";\n"
        "        var cdCls=i===0?\" train-countdown-next\":\"\";\n"
        "        var dot=x.t.origin?\"●\":\"\";\n"
        "        var farText=isNarrow?\"--:--\":\"あと--分--秒\";\n"
        "        var cdText=x.remain>FAR_SEC?farText:(isNarrow?(pad2(m)+\":\"+pad2(s)):('あと'+pad2(m)+'分'+pad2(s)+'秒'));\n"
        "        return '<div class=\"train-item\"><span class=\"train-time\"><span class=\"train-dot\">'+dot+'</span>'+x.t.time+'</span><span class=\"train-type'+typeCls+'\">'+x.t.type+'</span><span class=\"train-dest\">'+x.t.dest+'行</span><span class=\"train-countdown'+cdCls+'\">'+cdText+'</span></div>';\n"
        "      }).join(\"\");\n"
        "    });\n"
        "  }\n"
        "  var currentGroup=\"up\";\n"
        "  function setGroup(g){\n"
        "    currentGroup=g;\n"
        "    TRAIN_GROUP_KEYS.forEach(function(k){\n"
        "      var el=document.getElementById(\"train-columns-\"+k);\n"
        "      if(el) el.classList.toggle(\"train-columns-hidden\", k!==g);\n"
        "    });\n"
        "    var meta=TRAIN_GROUP_META[g];\n"
        "    document.getElementById(\"train-title-name\").textContent=meta.name;\n"
        "    document.getElementById(\"train-direction\").textContent=meta.direction;\n"
        "    document.getElementById(\"train-dir-toggle-label\").textContent=meta.toggleLabel;\n"
        "    renderTrains();\n"
        "  }\n"
        "  var toggleBtn=document.getElementById(\"train-dir-toggle\");\n"
        "  if(toggleBtn){\n"
        "    toggleBtn.addEventListener(\"click\", function(){\n"
        "      var idx=TRAIN_GROUP_KEYS.indexOf(currentGroup);\n"
        "      setGroup(TRAIN_GROUP_KEYS[(idx+1)%TRAIN_GROUP_KEYS.length]);\n"
        "    });\n"
        "  }\n"
        "  function defaultGroup(){\n"
        "    var h=new Date(new Date().toLocaleString(\"en-US\",{timeZone:\"Asia/Tokyo\"})).getHours();\n"
        "    return h>=16?\"down_asakusabashi\":\"up\";\n"
        "  }\n"
        "  setGroup(defaultGroup());\n"
        "  setInterval(renderTrains, 1000);\n"
        "})();\n"
        "</script>\n"
    )

    parts = [
        "<!DOCTYPE html>\n<html lang=\"ja\">\n<head>\n",
        "<meta charset=\"UTF-8\">\n",
        "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n",
        "<title>印西ニュース - 千葉県印西市のニュース</title>\n",
        "<meta name=\"description\" content=\"千葉県印西市の最新ニュース・話題をお届けします。\">\n",
        "<link rel=\"canonical\" href=\"" + html.escape(SITE_URL) + "\">\n",
        "<link rel=\"icon\" type=\"image/png\" href=\"favicon.png\">\n",
        GA_TAG,
        "<style>\n", CSS, "</style>\n",
        "</head>\n<body>\n",
        "<div class=\"wrap\">\n",
        "  <header>\n",
        "    <div class=\"logo\">印西<span>ニュース</span></div>\n",
        "    <button type=\"button\" class=\"train-dir-toggle\" id=\"train-dir-toggle\"><span id=\"train-dir-toggle-label\">下り時刻表切替</span></button>\n",
        "    <div class=\"updated\">最終更新<br>" + now_str + "</div>\n",
        "  </header>\n",
        "  " + top_html + "\n",
        "  " + sections_html + "\n",
        "  <footer>\n",
        "    &copy; 印西ニュース &mdash; Google News・印西市公式サイト・地域情報より自動収集。記事の著作権は各メディアに帰属します。\n",
        "  </footer>\n",
        "</div>\n<script>\n(function(){\n  var now=new Date(new Date().toLocaleString(\"en-US\",{timeZone:\"Asia/Tokyo\"}));\n  var jstToday=now.getFullYear()+\"-\"+String(now.getMonth()+1).padStart(2,\"0\")+\"-\"+String(now.getDate()).padStart(2,\"0\");\n  var jst=new Date(jstToday);\n  document.querySelectorAll(\".news-item[data-pub]\").forEach(function(el){\n    var diff=Math.floor((jst-new Date(el.dataset.pub))/86400000);\n    if(diff>=0&&diff<=3) el.classList.add(\"recent\");if(diff===0){var b=el.querySelector(\".today-badge\");if(b)b.style.display=\"\";}\n  });\n})();\n</script>\n",
        train_script,
        "</body>\n</html>",
    ]
    return "".join(parts)


def build_sitemap_xml() -> str:
    """検索エンジン向けのsitemap.xmlを生成する。現状index.htmlのみの単一ページサイトのため
    URLは1件のみ。lastmodはbuild実行時のJST日付(記事は毎回更新されるため、常に「今日」でよい)。
    """
    lastmod = datetime.now(JST).date().isoformat()
    return (
        '<?xml version="1.0" encoding="UTF-8"?>\n'
        '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n'
        "  <url>\n"
        f"    <loc>{html.escape(SITE_URL)}</loc>\n"
        f"    <lastmod>{lastmod}</lastmod>\n"
        "    <changefreq>hourly</changefreq>\n"
        "  </url>\n"
        "</urlset>\n"
    )


def build_robots_txt() -> str:
    """検索エンジンのクローラーがsitemap.xmlを発見できるようrobots.txtを生成する。"""
    return (
        "User-agent: *\n"
        "Allow: /\n"
        "\n"
        f"Sitemap: {SITE_URL}sitemap.xml\n"
    )


def cmd_build(args):
    articles = load_news()
    print(f"{len(articles)}件の記事でHTMLを生成中...")
    content = build_html(articles)
    INDEX_HTML_PATH.write_text(content, encoding="utf-8")
    print(f"index.html を生成しました → {INDEX_HTML_PATH}")
    SITEMAP_PATH.write_text(build_sitemap_xml(), encoding="utf-8")
    ROBOTS_PATH.write_text(build_robots_txt(), encoding="utf-8")
    if NEW_WEATHER_ICONS_THIS_RUN:
        print(f"新しい天気アイコンをダウンロードしました: {', '.join(NEW_WEATHER_ICONS_THIS_RUN)}")
    if TRAIN_TIMETABLE_CHANGED:
        print("[INFO] 北総鉄道の電車時刻表が前回取得時から変更されています(ダイヤ改正の可能性)")


# ============================================================
# publish: git push
# ============================================================

def cmd_publish(args):
    if not TOKEN_PATH.exists():
        print("エラー: .gh_token が見つかりません。git pushをスキップします。", file=sys.stderr)
        sys.exit(1)
    token = TOKEN_PATH.read_text(encoding="utf-8").strip()
    repo_dir = str(BASE_DIR)
    now_str = datetime.now(JST).strftime("%Y-%m-%d %H:%M JST")

    def run(cmd, **kw):
        return subprocess.run(cmd, cwd=repo_dir, capture_output=True, text=True, **kw)

    run(["git", "config", "user.name", "claude-code-bot"])
    run(["git", "config", "user.email", "claude-code-bot@users.noreply.github.com"])
    run(["git", "add", "-A"])
    r = run(["git", "commit", "-m", f"ニュース更新: {now_str}"])
    if r.returncode != 0:
        if "nothing to commit" in (r.stdout + r.stderr):
            print("変更なし。pushをスキップします。")
            return
        print(f"エラー(commit): {r.stderr}", file=sys.stderr)
        sys.exit(1)

    push_url = f"https://{token}@github.com/{GITHUB_REPO}.git"
    plain_url = f"https://github.com/{GITHUB_REPO}.git"
    try:
        run(["git", "remote", "set-url", "origin", push_url])
        r = run(["git", "push"])
        if r.returncode != 0:
            print(f"エラー(push): {r.stderr}", file=sys.stderr)
            sys.exit(1)
    finally:
        run(["git", "remote", "set-url", "origin", plain_url])
    print("git push 完了")


# ============================================================
# 開店閉店情報の管理
# ============================================================

def load_store_lines():
    text = STORE_LIST_PATH.read_text(encoding="shift_jis")
    return [line.strip() for line in text.splitlines() if line.strip()]


def save_store_lines(lines):
    body = "\n".join(lines) + ("\n" if lines else "")
    STORE_LIST_PATH.write_text(body, encoding="shift_jis")


def latest_event_date(name, news_items):
    dates = []
    for item in news_items:
        if name not in item.get("title", ""):
            continue
        m = STORE_EVENT_TITLE_PATTERN.match(item["title"])
        if m:
            y, mo, d = int(m.group(1)), int(m.group(2)), int(m.group(3))
            dates.append(date(y, mo, d))
    return max(dates) if dates else None


def cmd_store_pending(args):
    if not STORE_LIST_PATH.exists():
        print(f"{STORE_LIST_PATH.name} が見つかりません。")
        return
    lines = load_store_lines()
    news_items = load_news()
    cutoff = months_ago(date.today(), STORE_EVENT_RETENTION_MONTHS)

    kept_lines, pending, done, starred, expired = [], [], [], [], []
    for line in lines:
        if line.startswith("★"):
            starred.append(line[1:].strip())
            kept_lines.append(line)
            continue
        event_date = latest_event_date(line, news_items)
        if event_date is None:
            pending.append(line)
            kept_lines.append(line)
        elif event_date < cutoff:
            expired.append(line)
        else:
            done.append(line)
            kept_lines.append(line)

    if expired:
        save_store_lines(kept_lines)

    print(f"未処理: {len(pending)}件")
    for name in pending:
        print(f"  - {name}")
    print(f"処理済み(スキップ): {len(done)}件")
    print(f"★スキップ対象: {len(starred)}件")
    if expired:
        print(f"6か月経過のため開店閉店.txtから削除: {len(expired)}件")
        for name in expired:
            print(f"  - {name}")


def cmd_store_add(args):
    news_items = load_news()
    by_link = {item["link"]: item for item in news_items}
    label = {"開店": "開店", "閉店": "閉店", "リニューアル": "リニューアル"}[args.type]
    title = f"【{args.date} {label}】{args.store}"
    m = re.match(r"(\d{4})年(\d{1,2})月(\d{1,2})日", args.date)
    if not m:
        print("エラー: --date は 'YYYY年M月D日' 形式で指定してください", file=sys.stderr)
        sys.exit(1)
    item = {
        "title": title,
        "link": args.link,
        "pub_str": args.date,
        "publisher": args.publisher or "",
        "source": "開店閉店情報",
        "category": "開店・閉店",
        "desc": args.desc or "",
    }
    if getattr(args, "announce_date", None):
        item["announce_str"] = args.announce_date
    # 既存登録の情報を修正するために同じlinkでstore-addを再実行するケースがあるため、
    # 既にcollected_atを持つ場合はそれを維持する(新規登録時のみ現在時刻をセットする)。
    # 毎回リセットすると、内容を修正しただけの記事が「新着」「今日」バッジ扱いになってしまう(2026-08-15)。
    prev_item = by_link.get(args.link)
    if prev_item and prev_item.get("collected_at"):
        item["collected_at"] = prev_item["collected_at"]
    else:
        item["collected_at"] = datetime.now(JST).isoformat()
    item["retention_type"] = compute_retention_type(item)
    by_link[args.link] = item
    today = date.today()
    final_items = [it for it in by_link.values() if not is_expired(it, today)]
    save_json_atomic(NEWS_PATH, final_items)
    # store-addはcollect/apply-reviewの外側で動くため、ここで明示的に「新着」バッジ対象に加えないと
    # 手動登録した開店・閉店情報にバッジが付かない(ただし既存登録の修正時は「新着」バッジを再度付けない)
    if prev_item is None:
        mark_new_badge_links({args.link})
    print(f"登録しました: {title}")


def cmd_store_star(args):
    if not STORE_LIST_PATH.exists():
        print(f"{STORE_LIST_PATH.name} が見つかりません。")
        return
    lines = load_store_lines()
    new_lines = []
    matched = False
    for line in lines:
        bare = line[1:].strip() if line.startswith("★") else line
        if bare == args.store:
            new_lines.append(f"★{bare}")
            matched = True
        else:
            new_lines.append(line)
    if not matched:
        print(f"'{args.store}' が開店閉店.txt に見つかりませんでした。", file=sys.stderr)
        sys.exit(1)
    save_store_lines(new_lines)
    print(f"★を付与しました: {args.store}")


# ============================================================
# CLI
# ============================================================

def main():
    parser = argparse.ArgumentParser(description="印西ニュース 統合パイプライン")
    sub = parser.add_subparsers(dest="command", required=True)

    sub.add_parser("collect", help="ソース収集 + ルールベース処理").set_defaults(func=cmd_collect)
    sub.add_parser("apply-review", help="review_queue.jsonの反映").set_defaults(func=cmd_apply_review)
    sub.add_parser("build", help="index.html生成").set_defaults(func=cmd_build)
    sub.add_parser("publish", help="git push").set_defaults(func=cmd_publish)
    sub.add_parser("store-pending", help="開店閉店.txtの未処理店舗一覧").set_defaults(func=cmd_store_pending)

    p_add = sub.add_parser("store-add", help="開店閉店情報を1件登録")
    p_add.add_argument("--store", required=True)
    p_add.add_argument("--date", required=True, help="YYYY年M月D日")
    p_add.add_argument("--type", required=True, choices=["開店", "閉店", "リニューアル"])
    p_add.add_argument("--link", required=True)
    p_add.add_argument("--publisher", default="")
    p_add.add_argument("--desc", default="")
    p_add.add_argument("--announce-date", default="", help="元記事の発表日(YYYY年M月D日)。見出しの日付欄はこちらを優先表示する")
    p_add.set_defaults(func=cmd_store_add)

    p_star = sub.add_parser("store-star", help="開店閉店.txtの店舗に★を付与")
    p_star.add_argument("--store", required=True)
    p_star.set_defaults(func=cmd_store_star)

    args = parser.parse_args()
    args.func(args)


if __name__ == "__main__":
    main()
