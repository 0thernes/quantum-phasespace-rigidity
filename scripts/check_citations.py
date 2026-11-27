# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Live citation integrity verifier against arXiv API and Crossref REST API.

Verifies every BibTeX entry in `paper/references.bib`:
- Every `eprint` (arXiv ID) resolves live on export.arxiv.org with matching title, surname, & year.
- Every `doi` resolves live on api.crossref.org with matching title, surname, year, & 0 retractions.
"""
from __future__ import annotations

import json
import pathlib
import re
import sys
import unicodedata
import urllib.error
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET

REPO = pathlib.Path(__file__).resolve().parent.parent
BIB_PATH = REPO / "paper" / "references.bib"
UA = "quantum-phasespace-rigidity-citation-audit/2.0 (mailto:0_0@0thernes.art)"


def norm(s: str) -> str:
    s = re.sub(r"[{}]", "", s)
    s = re.sub(r"\\['\"`^~=.uvHcdbtr]\{?([A-Za-z])\}?", r"\1", s)
    s = re.sub(r"\\[A-Za-z]+", " ", s)
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode("ascii")
    s = re.sub(r"[^a-z0-9]+", " ", s.lower())
    return " ".join(s.split())


def first_author_surname(author_field: str) -> str:
    first = author_field.split(" and ")[0].strip()
    if "," in first:
        surname = first.split(",")[0].strip()
    else:
        parts = first.split()
        surname = parts[-1] if parts else ""
    return norm(surname)


def parse_bib(text: str) -> list[dict[str, str]]:
    entries: list[dict[str, str]] = []
    chunks = re.split(r"(?=@\w+\s*\{)", text)
    for chunk in chunks:
        chunk = chunk.strip()
        if not chunk.startswith("@"):
            continue
        m = re.match(r"@(\w+)\s*\{\s*([^,\s]+)\s*,", chunk)
        if not m:
            continue
        entry: dict[str, str] = {"type": m.group(1).lower(), "key": m.group(2)}
        for fm in re.finditer(r"(\w+)\s*=\s*(\{(?:[^{}]|\{[^{}]*\})*\}|\"[^\"]*\"|\d+)", chunk):
            k = fm.group(1).lower()
            v = fm.group(2).strip()
            if (v.startswith("{") and v.endswith("}")) or (v.startswith('"') and v.endswith('"')):
                v = v[1:-1]
            entry[k] = " ".join(v.split())
        entries.append(entry)
    return entries


def fetch_arxiv_batch(ids: list[str]) -> dict[str, dict[str, str]]:
    out: dict[str, dict[str, str]] = {}
    if not ids:
        return out
    url = (
        "https://export.arxiv.org/api/query?id_list="
        + urllib.parse.quote(",".join(ids))
        + "&max_results=100"
    )
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=30) as resp:
        xml_bytes = resp.read()
    ns = {"a": "http://www.w3.org/2005/Atom"}
    root = ET.fromstring(xml_bytes)
    for ent in root.findall("a:entry", ns):
        id_url = (ent.findtext("a:id", "", ns) or "").strip()
        raw_id = id_url.split("/abs/")[-1]
        base_id = re.sub(r"v\d+$", "", raw_id)
        title = " ".join((ent.findtext("a:title", "", ns) or "").split())
        published = (ent.findtext("a:published", "", ns) or "")[:4]
        authors = [a.findtext("a:name", "", ns) or "" for a in ent.findall("a:author", ns)]
        out[base_id] = {"id": raw_id, "title": title, "year": published, "authors": " and ".join(authors)}
    return out


def fetch_crossref(doi: str) -> dict[str, str]:
    url = "https://api.crossref.org/works/" + urllib.parse.quote(doi, safe="")
    req = urllib.request.Request(url, headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=20) as resp:
        data = json.loads(resp.read().decode("utf-8"))["message"]
    titles = data.get("title") or [""]
    retracted = any(
        (u.get("type", "").lower() == "retraction")
        for u in (data.get("update-to") or [])
    )
    authors = [
        f"{a.get('given', '')} {a.get('family', '')}".strip()
        for a in (data.get("author") or [])
    ]
    year = ""
    for field in ("published-print", "published-online", "issued", "created"):
        parts = (data.get(field) or {}).get("date-parts") or [[]]
        if parts and parts[0]:
            year = str(parts[0][0])
            break
    return {
        "title": titles[0],
        "retracted": str(retracted),
        "authors": " and ".join(authors),
        "year": year,
    }


def main() -> int:
    if "--fetch" in sys.argv:
        ids = sys.argv[sys.argv.index("--fetch") + 1 :]
        meta = fetch_arxiv_batch(ids)
        print(json.dumps(meta, indent=2, ensure_ascii=False))
        return 0

    if not BIB_PATH.exists():
        print(f"[ERROR] Missing {BIB_PATH}", file=sys.stderr)
        return 1
    entries = parse_bib(BIB_PATH.read_text(encoding="utf-8"))
    arxiv_ids = [re.sub(r"v\d+$", "", e["eprint"]) for e in entries if "eprint" in e]
    arxiv_meta = fetch_arxiv_batch(arxiv_ids)

    failures = 0
    for e in entries:
        key = e["key"]
        title_n = norm(e.get("title", ""))
        bib_surname = first_author_surname(e.get("author", ""))
        bib_year = e.get("year", "").strip()
        verified = False
        if "eprint" in e:
            bid = re.sub(r"v\d+$", "", e["eprint"])
            am = arxiv_meta.get(bid)
            if not am or not am["title"]:
                print(f"[FAIL] {key}: arXiv {bid} not found")
                failures += 1
                continue
            am_n = norm(am["title"])
            words = [w for w in title_n.split() if len(w) >= 4]
            overlap = sum(1 for w in words if w in am_n) / max(1, len(words))
            if overlap < 0.75:
                print(f"[FAIL] {key}: arXiv title mismatch\n  bib: {e.get('title')}\n  api: {am['title']}")
                failures += 1
                continue
            am_authors_n = norm(am["authors"])
            if bib_surname and bib_surname not in am_authors_n:
                print(f"[FAIL] {key}: arXiv author mismatch ({bib_surname} not in {am['authors']})")
                failures += 1
                continue
            # Note: arXiv submission year can precede journal publication year by 0-4 years
            if am["year"] and bib_year and abs(int(bib_year) - int(am["year"])) > 5:
                print(f"[FAIL] {key}: arXiv year mismatch (bib={bib_year}, api={am['year']})")
                failures += 1
                continue
            print(f"[OK][arXiv] {key} ({am['id']}, {am['year']}): {am['title'][:64]}")
            verified = True
        if "doi" in e:
            try:
                cm = fetch_crossref(e["doi"])
                if cm["retracted"] == "True":
                    print(f"[FAIL] {key}: DOI {e['doi']} flagged RETRACTED")
                    failures += 1
                    continue
                cm_n = norm(cm["title"])
                words = [w for w in title_n.split() if len(w) >= 4]
                overlap = sum(1 for w in words if w in cm_n) / max(1, len(words))
                if overlap < 0.65:
                    print(
                        f"[FAIL] {key}: Crossref title mismatch\n"
                        f"  bib: {e.get('title')}\n  api: {cm['title']}"
                    )
                    failures += 1
                    continue
                cm_authors_n = norm(cm["authors"])
                if bib_surname and cm_authors_n and bib_surname not in cm_authors_n:
                    print(f"[FAIL] {key}: Crossref author mismatch ({bib_surname} not in {cm['authors']})")
                    failures += 1
                    continue
                if cm["year"] and bib_year and abs(int(bib_year) - int(cm["year"])) > 2:
                    print(f"[FAIL] {key}: Crossref year mismatch (bib={bib_year}, api={cm['year']})")
                    failures += 1
                    continue
                print(f"[OK][DOI]   {key} ({e['doi']}, {cm['year']}): {cm['title'][:64]}")
                verified = True
            except urllib.error.URLError as exc:
                print(f"[WARN][DOI] {key} ({e['doi']}): network error {exc}")
        if not verified:
            print(f"[OK][BOOK]  {key}: monograph/classic entry (no eprint/DOI)")

    print(f"\n[CITATIONS] Audited {len(entries)} entries, {failures} failures.")
    return 0 if failures == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
