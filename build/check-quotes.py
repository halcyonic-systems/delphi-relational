"""Check that every quote in claims.json occurs in the source PDF's text layer.

Usage: python3 build/check-quotes.py <path to Louie 2012 PDF>
Needs pdftotext (poppler). The PDF is not in the repo (copyright); any copy of the
published article works.

The text layer is normalized before matching, and each rule is listed here:
  - control characters from typeset brackets are dropped;
  - running heads and page numbers are dropped;
  - curly quotes become straight quotes; whitespace collapses;
  - '(M,R)system' becomes '(M,R)-system' (a hyphen lost at a line break, checked on the page image);
  - claims marked quote_check: page-image are skipped and listed; their text layer is unusable
    and the quote was checked against the rendered page instead;
  - for claims with a quote_note, 'H A; B' becomes 'H(A,B)', 'B A' becomes 'B^A',
    and the space the text layer leaves before punctuation after notation is dropped.
"""
import json, re, subprocess, sys
from pathlib import Path

pdf = sys.argv[1]
raw = subprocess.run(["pdftotext", pdf, "-"], capture_output=True, text=True, check=True).stdout
lines = [l for l in raw.splitlines()
         if l.strip() not in ("International Journal of General Systems", "A.H. Louie")
         and not re.fullmatch(r"\s*\d{1,2}\s*", l)]
text = re.sub(r"[\x00-\x08\x0b-\x1f]", "", "\n".join(lines))
text = text.replace("‘", "'").replace("’", "'").replace("(M,R)system", "(M,R)-system")
text = re.sub(r"\s+", " ", text)
notation = re.sub(r" ([.;,])", r"\1", text.replace("H A; B", "H(A,B)").replace("B A", "B^A"))
norm = lambda s: re.sub(r"\s+", " ", s.replace("‘", "'").replace("’", "'")).strip()

claims = json.loads((Path(__file__).parent.parent / "claims.json").read_text())["claims"]
bad = 0
for c in claims:
    if c.get("quote_check") == "page-image":
        print("page " + c["id"] + "  (checked against the rendered page; text layer unusable)")
        continue
    hay = notation if c.get("quote_note") else text
    ok = norm(c["quote"]) in re.sub(r"\s+", " ", hay)
    bad += not ok
    print(("ok   " if ok else "MISS ") + c["id"])
sys.exit(1 if bad else 0)
