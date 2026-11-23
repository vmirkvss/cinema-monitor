#!/usr/bin/env python3
"""Мониторинг продажи билетов в кино (Алматы) с уведомлениями в Telegram.

Что делает:
  * опрашивает kino.kz и ticketon.kz (список фильмов -> страница фильма -> расписание);
  * ищет нужный фильм по ключевым словам и нужные кинотеатры по ключевым словам;
  * о каждой НОВОЙ находке (сайт + кинотеатр + дата) шлёт одно сообщение в Telegram;
  * следит за «здоровьем» сайтов и раз в сутки шлёт «работаю»;
  * состояние хранится в state.json (никаких дублей).

Запуск:
  python main.py --test        # тестовое сообщение в Telegram
  python main.py --discover    # диагностика: что видит парсер (без Telegram и state)
  python main.py --once        # один проход (для cron / GitHub Actions)
  python main.py               # бесконечный цикл, раз в ~5 минут (±30 сек)

Токен и chat_id берутся ТОЛЬКО из переменных окружения:
  TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID
"""
from __future__ import annotations

import argparse
import json
import logging
import os
import random
import re
import sys
import time
from dataclasses import dataclass, field
from datetime import date, datetime, timedelta, timezone
from html import escape
from pathlib import Path
from urllib.parse import urljoin
from zoneinfo import ZoneInfo

import requests
import yaml
from bs4 import BeautifulSoup
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

try:  # .env необязателен: можно просто экспортировать переменные
    from dotenv import load_dotenv

    load_dotenv()
except ImportError:
    pass

log = logging.getLogger("cinema-monitor")
TZ = ZoneInfo("Asia/Almaty")

# --------------------------------------------------------------------------- #
# Разбор дат и времени
# --------------------------------------------------------------------------- #
_MONTH_NAMES = [
    "january jan январь января қаңтар",
    "february feb февраль февраля ақпан",
    "march mar март марта наурыз",
    "april apr апрель апреля сәуір",
    "may май мая мамыр",
    "june jun июнь июня маусым",
    "july jul июль июля шілде",
    "august aug август августа тамыз",
    "september sep sept сентябрь сентября қыркүйек",
    "october oct октябрь октября қазан",
    "november nov ноябрь ноября қараша",
    "december dec декабрь декабря желтоқсан",
]
MONTHS = {name: i for i, names in enumerate(_MONTH_NAMES, 1) for name in names.split()}
WEEKDAYS = ["пн", "вт", "ср", "чт", "пт", "сб", "вс"]

ISO_DATE = re.compile(r"(?<!\d)(\d{4}-\d{2}-\d{2})(?!\d)")
TIME_RE = re.compile(r"(?<!\d)([01]?\d|2[0-3]):([0-5]\d)(?!\d)")


def _make_date(day: int, month: int, year: int | None, today: date) -> date | None:
    """Собирает дату; если года нет — берёт ближайший подходящий."""
    try:
        if year is not None:
            return date(year + 2000 if year < 100 else year, month, day)
        d = date(today.year, month, day)
        return d if d >= today - timedelta(days=60) else date(today.year + 1, month, day)
    except ValueError:
        return None


def parse_date_line(line: str, nxt: str | None, today: date) -> tuple[date | None, int]:
    """Пытается распознать дату в строке. Возвращает (дата, сколько доп. строк съели)."""
    low = line.casefold().strip()
    if m := ISO_DATE.search(low):
        return date.fromisoformat(m.group(1)), 0
    if m := re.fullmatch(r"(\d{1,2})\.(\d{1,2})(?:\.(\d{2,4}))?", low):
        return _make_date(int(m[1]), int(m[2]), int(m[3]) if m[3] else None, today), 0
    if m := re.fullmatch(r"(\d{1,2})\s+([^\W\d_]+)\.?", low):  # «7 января»
        if m[2] in MONTHS:
            return _make_date(int(m[1]), MONTHS[m[2]], None, today), 0
    if re.fullmatch(r"\d{1,2}", low) and nxt and nxt.casefold().strip() in MONTHS:  # «26» + «December»
        return _make_date(int(low), MONTHS[nxt.casefold().strip()], None, today), 1
    return None, 0


# --------------------------------------------------------------------------- #
# Сопоставление фильма и кинотеатров по ключевым словам
# --------------------------------------------------------------------------- #
class Matcher:
    def __init__(self, cfg: dict):
        film = cfg["film"]
        self.film_kw = [k.casefold() for k in film["keywords"]]
        self.film_ex = [k.casefold() for k in film.get("exclude_keywords", [])]
        self.cinemas = [
            (c["name"], [k.casefold() for k in c["include"]], [k.casefold() for k in c.get("exclude", [])])
            for c in cfg["cinemas"]
        ]
        self.other_venue = re.compile(cfg.get("other_venue_regex", r"cinema|кино|chaplin|чаплин|plexx|lumiera|арман|arman"), re.I)

    def film(self, text: str) -> bool:
        t = text.casefold()
        return any(k in t for k in self.film_kw) and not any(k in t for k in self.film_ex)

    def cinema(self, text: str) -> str | None:
        t = text.casefold()
        for name, include, exclude in self.cinemas:
            if any(k in t for k in include) and not any(k in t for k in exclude):
                return name
        return None


# --------------------------------------------------------------------------- #
# Модели данных
# --------------------------------------------------------------------------- #
@dataclass
class Hit:
    site: str
    cinema: str
    date: str  # ISO-дата или "" если неизвестна
    url: str
    times: set[str] = field(default_factory=set)

    @property
    def key(self) -> str:  # ключ дедупликации
        return f"{self.site}|{self.cinema}|{self.date}"


@dataclass
class SiteResult:
    site: str
    hits: list[Hit]
    healthy: bool
    note: str = ""


# --------------------------------------------------------------------------- #
# HTTP
# --------------------------------------------------------------------------- #
def make_session(cfg: dict) -> requests.Session:
    """Сессия с нормальным User-Agent и автоматическими ретраями (GET)."""
    h = cfg["http"]
    s = requests.Session()
    s.headers.update(
        {
            "User-Agent": h["user_agent"],
            "Accept": "text/html,application/json;q=0.9,*/*;q=0.8",
            "Accept-Language": "ru-RU,ru;q=0.9,en;q=0.5",
        }
    )
    retry = Retry(
        total=h.get("retries", 3),
        backoff_factor=2,  # 0, 2, 4 сек...
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=("GET",),
    )
    s.mount("https://", HTTPAdapter(max_retries=retry))
    s.mount("http://", HTTPAdapter(max_retries=retry))
    s.request_timeout = (h.get("connect_timeout", 10), h.get("read_timeout", 25))  # type: ignore[attr-defined]
    return s


def describe(exc: Exception) -> str:
    """Безопасное описание ошибки (в URL запросов к Telegram есть токен!)."""
    resp = getattr(exc, "response", None)
    return f"{type(exc).__name__}" + (f" HTTP {resp.status_code}" if resp is not None else "")


# --------------------------------------------------------------------------- #
# Парсер сайта (общий для kino.kz и ticketon.kz, поведение задаётся конфигом)
# --------------------------------------------------------------------------- #
class Site:
    def __init__(self, cfg: dict, matcher: Matcher, http: requests.Session, debug_dir: Path | None = None):
        self.cfg, self.m, self.http, self.debug_dir = cfg, matcher, http, debug_dir
        self.name = cfg["name"]

    # -- сеть --------------------------------------------------------------
    def _get(self, url: str) -> requests.Response:
        r = self.http.get(url, timeout=self.http.request_timeout)  # type: ignore[attr-defined]
        r.raise_for_status()
        if self.debug_dir:  # в режиме --discover сохраняем сырые ответы
            self.debug_dir.mkdir(exist_ok=True)
            safe = re.sub(r"[^\w.-]+", "_", url)[:120]
            (self.debug_dir / f"{self.name}_{safe}.txt").write_text(r.text, encoding="utf-8")
        return r

    # -- публичный метод ---------------------------------------------------
    def check(self) -> SiteResult:
        hits: dict[tuple[str, str], Hit] = {}
        notes: list[str] = []
        healthy_sources = 0
        film_pages: dict[str, bool] = {u: True for u in self.cfg.get("film_urls", [])}  # url -> trusted

        # 1) Списки фильмов: ищем ссылки, похожие на страницы фильмов
        links_total = 0
        for url in self.cfg.get("listing_urls", []):
            try:
                r = self._get(url)
            except requests.RequestException as e:
                notes.append(f"{url}: {describe(e)}")
                continue
            all_links, film_links = self._links(r.text, r.url)
            links_total += len(all_links)
            for link in film_links:
                film_pages.setdefault(link, False)
        if links_total >= self.cfg.get("min_listing_links", 5):
            healthy_sources += 1  # «канарейка»: структура сайта узнаётся
        elif self.cfg.get("listing_urls"):
            notes.append(f"на списках найдено лишь {links_total} ссылок (структура изменилась?)")

        # 2) JSON-эндпоинты из DevTools (если заданы)
        json_ok = True
        for url in self.cfg.get("json_urls", []):
            try:
                self._parse_response(self._get(url), url, hits, film_ok=self.cfg.get("json_film_specific", False))
            except (requests.RequestException, ValueError) as e:
                json_ok = False
                notes.append(f"{url}: {describe(e)}")
        if self.cfg.get("json_urls") and json_ok:
            healthy_sources += 1

        # 3) Страницы найденных фильмов
        pages_ok = True
        for url, trusted in film_pages.items():
            try:
                self._parse_response(self._get(url), url, hits, film_ok=trusted, trusted=trusted)
            except requests.RequestException as e:
                pages_ok = False
                notes.append(f"{url}: {describe(e)}")

        healthy = healthy_sources > 0 and pages_ok
        return SiteResult(self.name, list(hits.values()), healthy, "; ".join(notes))

    # -- разбор ссылок -----------------------------------------------------
    def _links(self, html: str, base: str) -> tuple[set[str], list[str]]:
        pattern = re.compile(self.cfg.get("link_pattern", r"/event/"))
        soup = BeautifulSoup(html, "html.parser")
        all_links: set[str] = set()
        film_links: list[str] = []
        for a in soup.find_all("a", href=True):
            href = urljoin(base, a["href"])
            if not pattern.search(href):
                continue
            all_links.add(href)
            text = " ".join([a.get_text(" ", strip=True), a.get("title", ""), href] + [i.get("alt", "") for i in a.find_all("img")])
            if self.m.film(text):
                film_links.append(href)
        return all_links, film_links

    # -- разбор страницы/JSON ----------------------------------------------
    def _parse_response(self, resp: requests.Response, url: str, hits: dict, film_ok: bool, trusted: bool = False) -> None:
        body = resp.text
        if "json" in resp.headers.get("content-type", "") or body.lstrip()[:1] in "{[":
            self._walk_json(resp.json(), film_ok, None, url, hits)
            return

        soup = BeautifulSoup(body, "html.parser")
        title = " ".join(filter(None, [soup.h1.get_text(" ", strip=True) if soup.h1 else "", soup.title.get_text(strip=True) if soup.title else ""]))
        if not trusted and not self.m.film(f"{title} {url}"):
            return  # защита: страница не про наш фильм

        # встроенный JSON (Next.js, ld+json и т.п.)
        for s in soup.find_all("script"):
            if s.get("type") in ("application/json", "application/ld+json") or s.get("id") == "__NEXT_DATA__":
                try:
                    self._walk_json(json.loads(s.string or ""), True, None, url, hits)
                except ValueError:
                    pass
        for s in soup(["script", "style", "noscript"]):
            s.decompose()
        lines = [ln for ln in soup.get_text("\n", strip=True).split("\n") if ln]
        self._parse_lines(lines, url, hits)

    def _add(self, hits: dict, cinema: str, d: date | str | None, url: str, times=()) -> None:
        iso = d.isoformat() if isinstance(d, date) else (d or "")
        if iso and iso < (datetime.now(TZ).date() - timedelta(days=1)).isoformat():
            return  # старые сеансы не интересуют
        hit = hits.setdefault((cinema, iso), Hit(self.name, cinema, iso, url))
        hit.times.update(times)

    def _parse_lines(self, lines: list[str], url: str, hits: dict) -> None:
        """Конечный автомат по строкам текста: дата -> кинотеатр -> времена сеансов."""
        today = datetime.now(TZ).date()
        require_date = self.cfg.get("require_date", True)
        cur_date: date | None = None
        cur_cinema: str | None = None
        i = 0
        while i < len(lines):
            line, nxt = lines[i], (lines[i + 1] if i + 1 < len(lines) else None)
            d, used = parse_date_line(line, nxt, today)
            if d:
                cur_date, cur_cinema = d, None
                i += 1 + used
                continue
            if len(line) <= 120:
                if cinema := self.m.cinema(line):
                    cur_cinema = cinema
                    if cur_date or not require_date:
                        self._add(hits, cinema, cur_date, url)
                elif self.m.other_venue.search(line):
                    cur_cinema = None  # начался блок чужого кинотеатра
                elif cur_cinema and (cur_date or not require_date):
                    times = [f"{int(h):02d}:{mm}" for h, mm in TIME_RE.findall(line)]
                    if times:
                        self._add(hits, cur_cinema, cur_date, url, times)
            i += 1

    def _walk_json(self, node, film_ok: bool, ctx_date: str | None, url: str, hits: dict) -> None:
        """Best-effort обход JSON: ищем объекты, где упомянут наш кинотеатр (и фильм)."""
        if isinstance(node, list):
            for v in node:
                self._walk_json(v, film_ok, ctx_date, url, hits)
        elif isinstance(node, dict):
            direct = [v for v in node.values() if isinstance(v, str)]
            if not film_ok and any(self.m.film(s) for s in direct):
                film_ok = True
            ctx_date = next((m.group(1) for s in direct if (m := ISO_DATE.search(s))), ctx_date)
            if film_ok:
                near = direct + [v for ch in node.values() if isinstance(ch, dict) for v in ch.values() if isinstance(v, str)]
                cinema = next((c for s in near if len(s) <= 120 and (c := self.m.cinema(s))), None)
                if cinema:
                    strings = list(_iter_strings(node))
                    dates = {d for s in strings for d in ISO_DATE.findall(s)} or ({ctx_date} if ctx_date else {""})
                    times = {f"{int(h):02d}:{mm}" for s in strings for h, mm in TIME_RE.findall(s)}
                    for d in dates:
                        self._add(hits, cinema, d, url, times)
            for v in node.values():
                if isinstance(v, (dict, list)):
                    self._walk_json(v, film_ok, ctx_date, url, hits)


def _iter_strings(node):
    if isinstance(node, str):
        yield node
    elif isinstance(node, dict):
        for v in node.values():
            yield from _iter_strings(v)
    elif isinstance(node, list):
        for v in node:
            yield from _iter_strings(v)


# --------------------------------------------------------------------------- #
# Telegram
# --------------------------------------------------------------------------- #
class Telegram:
    def __init__(self, token: str, chat_id: str):
        self.url = f"https://api.telegram.org/bot{token}/sendMessage"
        self.chat_id = chat_id

    def send(self, text: str) -> bool:
        """Отправка с 3 попытками. Возвращает True при успехе."""
        payload = {
            "chat_id": self.chat_id,
            "text": text[:4000],  # лимит Telegram — 4096
            "parse_mode": "HTML",
            "disable_web_page_preview": True,
        }
        for attempt in range(1, 4):
            wait = 2 * attempt
            try:
                r = requests.post(self.url, json=payload, timeout=(10, 20))
                if r.ok:
                    return True
                log.error("Telegram ответил HTTP %s: %s", r.status_code, r.text[:200])
                if r.status_code == 429:
                    # Telegram сам говорит, сколько ждать: уважаем это, иначе лимит только продлится
                    try:
                        wait = int(r.json()["parameters"]["retry_after"]) + 2
                    except (ValueError, KeyError, TypeError):
                        wait = 30
                    log.info("Лимит Telegram, жду %d сек...", wait)
                elif r.status_code < 500:
                    return False  # ошибка конфигурации — ретраить бессмысленно
            except requests.RequestException as e:
                log.error("Telegram недоступен (%s), попытка %d/3", describe(e), attempt)  # без URL: там токен
            if attempt < 3:
                time.sleep(wait)
        return False


# --------------------------------------------------------------------------- #
# Состояние
# --------------------------------------------------------------------------- #
def load_state(path: Path) -> dict:
    default = {"seen": {}, "sites": {}, "last_heartbeat": None}
    try:
        return {**default, **json.loads(path.read_text(encoding="utf-8"))}
    except (FileNotFoundError, ValueError):
        return default


def save_state(path: Path, state: dict) -> None:
    tmp = path.with_suffix(".tmp")  # атомарная запись, чтобы не побить файл при сбое
    tmp.write_text(json.dumps(state, ensure_ascii=False, indent=2), encoding="utf-8")
    tmp.replace(path)


# --------------------------------------------------------------------------- #
# Сообщения
# --------------------------------------------------------------------------- #
def fmt_date(iso: str) -> str:
    if not iso:
        return "дата не указана"
    d = date.fromisoformat(iso)
    return f"{d:%d.%m.%Y} ({WEEKDAYS[d.weekday()]})"


def build_message(film_title: str, site: str, cinema: str, hits: list[Hit]) -> str:
    lines = [f"🎬 <b>{escape(film_title)}</b> — появились сеансы!", "", f"🌐 Сайт: {escape(site)}", f"🏛 Кинотеатр: {escape(cinema)}", "📅 Сеансы:"]
    for h in sorted(hits, key=lambda x: x.date):
        times = ", ".join(sorted(h.times)) if h.times else "время смотрите на сайте"
        lines.append(f"  • {fmt_date(h.date)} — {times}")
    lines += ["", f'🎟 <a href="{escape(hits[0].url, quote=True)}">Купить билет</a>']
    return "\n".join(lines)


# --------------------------------------------------------------------------- #
# Один цикл проверки
# --------------------------------------------------------------------------- #
def run_cycle(cfg: dict, state: dict, sites: list[Site], tg: Telegram) -> None:
    film_title = cfg["film"]["title"]
    threshold = cfg["alerts"].get("failure_threshold", 3)
    now = datetime.now(timezone.utc)

    for site in sites:
        try:
            result = site.check()
        except Exception as e:  # парсер не должен ронять весь цикл
            log.exception("Необработанная ошибка парсера %s", site.name)
            result = SiteResult(site.name, [], False, f"{type(e).__name__}")

        # --- здоровье сайта ------------------------------------------------
        st = state["sites"].setdefault(site.name, {"fails": 0, "warned": False})
        if result.healthy:
            if st["warned"]:
                tg.send(f"✅ {escape(site.name)} снова отвечает и парсится нормально.")
            st.update(fails=0, warned=False)
        else:
            st["fails"] += 1
            log.warning("%s: проблема #%d (%s)", site.name, st["fails"], result.note)
            if st["fails"] >= threshold and not st["warned"]:
                text = (
                    f"⚠️ <b>{escape(site.name)}</b>: {st['fails']} проверок подряд без нормального ответа "
                    f"или структура страниц изменилась.\n{escape(result.note[:600])}"
                )
                if tg.send(text):
                    st["warned"] = True

        # --- новые находки -------------------------------------------------
        new = [h for h in result.hits if h.key not in state["seen"]]
        groups: dict[str, list[Hit]] = {}
        for h in new:
            groups.setdefault(h.cinema, []).append(h)
        for cinema, group in groups.items():
            if tg.send(build_message(film_title, site.name, cinema, group)):
                for h in group:  # помечаем «увиденным» только после успешной отправки
                    state["seen"][h.key] = now.isoformat(timespec="seconds")
                log.info("Отправлено уведомление: %s / %s (%d дат)", site.name, cinema, len(group))

    # --- ежедневный «пульс» -----------------------------------------------
    last = state.get("last_heartbeat")
    interval = timedelta(hours=cfg["alerts"].get("heartbeat_hours", 24))
    if last is None or now - datetime.fromisoformat(last) >= interval:
        status = "билеты уже найдены, слежу за новыми датами" if state["seen"] else "билетов пока нет"
        if tg.send(f"👋 Работаю, {status}. ({datetime.now(TZ):%d.%m %H:%M}, Алматы)"):
            state["last_heartbeat"] = now.isoformat(timespec="seconds")


# --------------------------------------------------------------------------- #
# Точка входа
# --------------------------------------------------------------------------- #
def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--config", default="config.yaml")
    ap.add_argument("--state", default=None, help="путь к state.json (по умолчанию из конфига)")
    ap.add_argument("--test", action="store_true", help="отправить тестовое сообщение в Telegram и выйти")
    ap.add_argument("--once", action="store_true", help="один проход и выход (cron / GitHub Actions)")
    ap.add_argument("--discover", action="store_true", help="диагностика парсеров, без Telegram и state")
    ap.add_argument("-v", "--verbose", action="store_true")
    args = ap.parse_args()

    logging.basicConfig(level=logging.DEBUG if args.verbose else logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
    logging.getLogger("urllib3").setLevel(logging.WARNING)

    cfg = yaml.safe_load(Path(args.config).read_text(encoding="utf-8"))
    matcher = Matcher(cfg)
    http = make_session(cfg)

    # --- диагностика ------------------------------------------------------
    if args.discover:
        debug = Path("debug")
        for sc in cfg["sites"]:
            if not sc.get("enabled", True):
                continue
            res = Site(sc, matcher, http, debug).check()
            print(f"\n=== {res.site}: healthy={res.healthy}  {res.note}")
            for h in res.hits:
                print(f"  НАЙДЕНО: {h.cinema} | {h.date or '?'} | {sorted(h.times)} | {h.url}")
            if not res.hits:
                print("  совпадений нет (для ещё не открытых продаж это нормально)")
        print(f"\nСырые ответы сайтов сохранены в {debug}/ — их можно прислать для доработки парсера.")
        return 0

    token, chat_id = os.environ.get("TELEGRAM_BOT_TOKEN"), os.environ.get("TELEGRAM_CHAT_ID")
    if not token or not chat_id:
        log.error("Не заданы TELEGRAM_BOT_TOKEN / TELEGRAM_CHAT_ID")
        return 2
    tg = Telegram(token, chat_id)

    if args.test:
        ok = tg.send("✅ Тест: мониторинг билетов подключён к Telegram.")
        print("Отправлено" if ok else "Не удалось отправить (см. лог)")
        return 0 if ok else 1

    state_path = Path(args.state or cfg.get("state_file", "state.json"))
    state = load_state(state_path)
    sites = [Site(sc, matcher, http) for sc in cfg["sites"] if sc.get("enabled", True)]
    poll = cfg["poll"]
    log.info("Старт. Сайтов: %d, интервал %ss ±%ss", len(sites), poll["interval_seconds"], poll["jitter_seconds"])

    while True:
        try:
            run_cycle(cfg, state, sites, tg)
        except Exception:
            log.exception("Сбой цикла (продолжаю работу)")
        finally:
            save_state(state_path, state)
        if args.once:
            return 0
        delay = poll["interval_seconds"] + random.uniform(-poll["jitter_seconds"], poll["jitter_seconds"])
        log.debug("Сплю %.0f сек", delay)
        time.sleep(delay)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(0)
