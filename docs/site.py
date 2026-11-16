"""Builds the site gh-pages serves: each docs/**/*.md as an HTML page of
the same name, and each other docs/*.html as the body of one, in
layout.html; index.md is the home page.

    python3 docs/site.py OUT_DIR

Needs Python-Markdown (pip install markdown). A link to another page's
.md goes to its .html; headings get GitHub's anchors, so a link such as
manual.md#limitations works on both.
"""
import html
import re
import sys
from pathlib import Path

import markdown

DOCS = Path(__file__).resolve().parent
NAV = [("Manyan", "index.html"), ("Playground", "playground.html"), ("Manual", "manual.html"),
       ("Roadmap", "roadmap.html"), ("Benchmark", "benchmark.html"), ("GitHub", "https://github.com/soasme/manyan")]


def slug(text, seen):
    """GitHub's anchor of a heading: lowercase, punctuation dropped, spaces dashes."""
    s = re.sub(r"[^\w\- ]", "", html.unescape(re.sub(r"<[^>]+>", "", text)).lower()).replace(" ", "-")
    n = seen.get(s, 0)
    seen[s] = n + 1
    return f"{s}-{n}" if n else s


def page(path):
    """The title and body of a page."""
    text = path.read_text()
    if path.suffix == ".html":
        return re.sub(r"<[^>]+>", "", re.search(r"<h1>(.+?)</h1>", text).group(1)), text
    seen = {}
    md = markdown.Markdown(extensions=["tables", "fenced_code", "toc"],
                           extension_configs={"toc": {"slugify": lambda t, sep: slug(t, seen)}})
    body = re.sub(r'href="(?![a-z]+:)([^"#]*)\.md(#[^"]*)?"', r'href="\1.html\2"', md.convert(text))
    return re.search(r"^# (.+)$", text, re.M).group(1), body


def main(out):
    out = Path(out)
    layout = (DOCS / "layout.html").read_text()
    for path in sorted([*DOCS.rglob("*.md"), *(p for p in DOCS.glob("*.html") if p.name != "layout.html")]):
        rel = path.relative_to(DOCS).with_suffix(".html")
        root = "../" * (len(rel.parts) - 1)
        title, body = page(path)
        nav = "".join(f'<a href="{href if "://" in href else root + href}"'
                      f'{" aria-current=page" if href == rel.as_posix() else ""}>{name}</a>' for name, href in NAV)
        target = out / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(layout.replace("{title}", html.escape("Manyan" if rel.name == "index.html" else title + " · Manyan"))
                          .replace("{root}", root).replace("{nav}", nav).replace("{body}", body))


if __name__ == "__main__":
    main(*sys.argv[1:])
