#!/usr/bin/env python3
"""Extract a curated sample of benchmark problems into docs/static/problems.json.

Run from anywhere:  python3 docs/scripts/build_problems.py

The sample is intentionally small and made of *compact* problems so every
artifact (description, spec, code, proof) can be shown in full — nothing is
truncated. Edit PICK to change which problems appear in the website's explorer;
prefer problems whose description and proof are short enough to display whole.
"""
import json, os, re

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))

# (relative problem dir, source label)
# LeetCode: 2 Easy, 2 Medium, 1 Hard — recognizable, compact problems.
# Codeforces: an even spread across the rating spectrum (~800 / ~1300 / ~1800).
PICK = [
    ("benchmarks/verus/problems/leetcode/lc121", "LeetCode"),    # Easy — Best Time to Buy and Sell Stock
    ("benchmarks/verus/problems/leetcode/lc169", "LeetCode"),    # Easy — Majority Element (Boyer–Moore)
    ("benchmarks/verus/problems/leetcode/lc343", "LeetCode"),    # Medium — Integer Break
    ("benchmarks/verus/problems/leetcode/lc1492", "LeetCode"),   # Medium — The kth Factor of n
    ("benchmarks/verus/problems/leetcode/lc1250", "LeetCode"),   # Hard — Check If It Is a Good Array
    ("benchmarks/verus/problems/codeforces/cf617A", "Codeforces"),  # Rating 800 — Elephant
    ("benchmarks/verus/problems/codeforces/cf1826C", "Codeforces"), # Rating 1300 — Dreaming of Freedom
    ("benchmarks/verus/problems/codeforces/cf478C", "Codeforces"),  # Rating 1800 — Table Decorations
]


def slugify(title):
    return re.sub(r"[^a-z0-9]+", "-", title.lower()).strip("-")


def source_id_and_url(pid, source, title):
    """Return (display_id, url) linking to the problem's official page."""
    if source == "LeetCode":
        num = pid[2:]  # strip "lc"
        return num, f"https://leetcode.com/problems/{slugify(title)}/"
    # Codeforces: "cf617A" -> contest 617, index A
    rest = pid[2:]
    m = re.match(r"(\d+)([A-Za-z]\d?)", rest)
    contest, index = (m.group(1), m.group(2)) if m else (rest, "")
    return rest, f"https://codeforces.com/problemset/problem/{contest}/{index}"


def readf(p):
    try:
        with open(p, encoding="utf-8") as f:
            return f.read().rstrip()
    except FileNotFoundError:
        return ""


# Rendering the raw description.md faithfully requires only display cleanup: the
# source carries LaTeX ($...$, \leq, ^k, \text{}) and a trailing "Starter Code"
# section. We convert the LaTeX to readable Unicode and drop the title heading and
# starter-code scaffold, but never change the wording, examples, or constraints.

_SUP = {
    "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴",
    "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹",
    "+": "⁺", "-": "⁻", "(": "⁽", ")": "⁾", "n": "ⁿ",
    "i": "ⁱ", "a": "ᵃ", "b": "ᵇ", "c": "ᶜ", "d": "ᵈ",
    "e": "ᵉ", "h": "ʰ", "k": "ᵏ", "m": "ᵐ", "t": "ᵗ",
    "x": "ˣ",
}


def _sup(body):
    return "".join(_SUP.get(ch, ch) for ch in body)


def latexify(s):
    """Render inline LaTeX to Unicode without changing the underlying text."""
    s = re.sub(r"\\text\{([^}]*)\}", r"\1", s)
    s = s.replace(r"\lfloor", "⌊").replace(r"\rfloor", "⌋")
    s = s.replace(r"\leq", "≤").replace(r"\geq", "≥")
    s = s.replace(r"\le ", "≤ ").replace(r"\ge ", "≥ ")
    s = s.replace(r"\times", "×").replace(r"\cdot", "·")
    s = s.replace(r"\ldots", "…").replace(r"\dots", "…")
    s = re.sub(r"\^\{([^}]*)\}", lambda m: _sup(m.group(1)), s)
    s = re.sub(r"\^([A-Za-z0-9])", lambda m: _sup(m.group(1)), s)
    s = s.replace("$", "")
    return s


def clean_desc(raw):
    """Faithful description: drop the H1 title and the Starter Code section,
    then render LaTeX. Wording, examples, and constraints are untouched."""
    text = raw
    idx = text.find("## Starter Code")
    if idx != -1:
        text = text[:idx]
    text = re.sub(r"^\s*#\s+.*\n", "", text, count=1)  # drop leading title heading
    return latexify(text).strip()


def main():
    out = []
    for d, source in PICK:
        full = os.path.join(ROOT, d)
        pid = os.path.basename(d)
        raw = readf(os.path.join(full, "description.md"))
        tags_raw = readf(os.path.join(full, "tags")).splitlines()

        m = re.search(r"^#\s+(.*)", raw, re.M)
        title = re.sub(r"^\d+\.\s*", "", m.group(1).strip()) if m else pid
        # strip a redundant leading "A. " / "C. " problem-letter prefix (Codeforces)
        title = re.sub(r"^[A-Z]\.\s+", "", title)

        # faithful description straight from description.md (display cleanup only)
        desc = clean_desc(raw)

        line0 = tags_raw[0].strip() if tags_raw else ""
        algo = tags_raw[1].strip() if len(tags_raw) > 1 else ""
        meta = tags_raw[2].strip() if len(tags_raw) > 2 else ""

        if source == "LeetCode":
            level_kind = "difficulty"
            level = line0 or "Medium"        # Easy / Medium / Hard
        else:
            level_kind = "rating"
            r = re.search(r"(\d+)", line0)
            level = r.group(1) if r else "?"  # numeric Codeforces rating

        tags = [t.strip() for t in re.split(r"[,\n]", algo) if t.strip()]
        display_id, url = source_id_and_url(pid, source, title)

        out.append({
            "id": pid,
            "displayId": display_id,
            "url": url,
            "source": source,
            "title": title,
            "levelKind": level_kind,
            "level": level,
            "tags": tags,
            "meta": meta,
            "description": desc,
            "spec": readf(os.path.join(full, "spec.rs")),
            "code": readf(os.path.join(full, "code.rs")),
            "proof": readf(os.path.join(full, "verified.rs")),
        })

    dst = os.path.join(ROOT, "docs", "static", "problems.json")
    with open(dst, "w", encoding="utf-8") as f:
        json.dump(out, f, indent=1, ensure_ascii=False)
    print(f"wrote {dst} with {len(out)} problems")
    for p in out:
        lvl = p["level"] if p["levelKind"] == "difficulty" else "Rating " + p["level"]
        print(f"  {p['id']:8} {p['source']:11} {lvl:12} {p['title']}")


if __name__ == "__main__":
    main()
