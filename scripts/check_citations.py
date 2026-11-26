# SPDX-License-Identifier: Apache-2.0
# Copyright (c) 2026 Alexander Stephen Donahue
"""Verify bibliography citations in paper/references.bib (syntax + optional live HTTP 200 checks)."""

from __future__ import annotations

import argparse
import pathlib
import re
import sys
import urllib.error
import urllib.request

ROOT = pathlib.Path(__file__).resolve().parents[1]


def parse_bib(bib_path: pathlib.Path) -> list[dict[str, str]]:
    text = bib_path.read_text(encoding="utf-8")
    raw_entries = re.split(r"\n(?=@)", text.strip())
    entries: list[dict[str, str]] = []
    for raw in raw_entries:
        m = re.match(r"@(\w+)\{([^,]+),", raw.strip())
        if not m:
            continue
        entry: dict[str, str] = {"type": m.group(1), "key": m.group(2).strip()}
        for fm in re.finditer(r"(\w+)\s*=\s*\{([^}]*)\}", raw):
            entry[fm.group(1).lower()] = fm.group(2).strip()
        entries.append(entry)
    return entries


def check_url(url: str, timeout: float = 12.0) -> tuple[bool, str]:
    req = urllib.request.Request(
        url,
        headers={"User-Agent": "zero-error-torus-frontier-citation-audit/1.0 (mailto:0_0@0thernes.art)"},
        method="HEAD",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return (200 <= resp.status < 400), f"HTTP {resp.status}"
    except urllib.error.HTTPError as e:
        if e.code in (403, 405):
            # Fallback to GET for servers rejecting HEAD
            req_get = urllib.request.Request(
                url,
                headers={"User-Agent": "zero-error-torus-frontier-citation-audit/1.0 (mailto:0_0@0thernes.art)"},
                method="GET",
            )
            try:
                with urllib.request.urlopen(req_get, timeout=timeout) as resp:
                    return (200 <= resp.status < 400), f"HTTP {resp.status} (GET)"
            except (urllib.error.URLError, OSError, TimeoutError) as e2:
                return False, f"ERR {e2}"
        return False, f"HTTP {e.code}"
    except (urllib.error.URLError, OSError, TimeoutError) as e:
        return False, f"ERR {e}"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--live", action="store_true", help="Perform live HTTP resolution checks")
    args = parser.parse_args()

    bib = ROOT / "paper" / "references.bib"
    assert bib.exists(), f"Missing {bib}"
    entries = parse_bib(bib)
    assert len(entries) >= 12, f"Expected >=12 bibliography entries, found {len(entries)}"

    failures: list[str] = []
    for e in entries:
        key = e["key"]
        assert "author" in e and "title" in e and "year" in e, f"Incomplete bib entry: {key}"
        assert "TBD" not in e["title"] and "TODO" not in e["title"], f"Placeholder in {key}"
        if args.live:
            url = None
            if "doi" in e:
                url = f"https://doi.org/{e['doi']}"
            elif "eprint" in e and e.get("archiveprefix", "").lower() == "arxiv":
                url = f"https://arxiv.org/abs/{e['eprint']}"
            elif "url" in e:
                url = e["url"]
            if url:
                ok, status = check_url(url)
                print(f"  [{('OK' if ok else 'FAIL')}] {key}: {url} -> {status}")
                if not ok:
                    failures.append(f"{key} ({url}): {status}")

    print(f"Parsed {len(entries)} bibliography entries cleanly.")
    if failures:
        print("Live citation check failures:", failures, file=sys.stderr)
        raise SystemExit(1)


if __name__ == "__main__":
    main()
