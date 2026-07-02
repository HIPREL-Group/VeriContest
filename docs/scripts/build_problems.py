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
    ("benchmark/leetcode/lc121", "LeetCode"),    # Easy — Best Time to Buy and Sell Stock
    ("benchmark/leetcode/lc169", "LeetCode"),    # Easy — Majority Element (Boyer–Moore)
    ("benchmark/leetcode/lc343", "LeetCode"),    # Medium — Integer Break
    ("benchmark/leetcode/lc1492", "LeetCode"),   # Medium — The kth Factor of n
    ("benchmark/leetcode/lc1250", "LeetCode"),   # Hard — Check If It Is a Good Array
    ("benchmark/codeforces/cf617A", "Codeforces"),  # Rating 800 — Elephant
    ("benchmark/codeforces/cf1826C", "Codeforces"), # Rating 1300 — Dreaming of Freedom
    ("benchmark/codeforces/cf478C", "Codeforces"),  # Rating 1800 — Table Decorations
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


# Hand-polished descriptions for the small explorer sample. Source description.md
# files carry raw LaTeX ($...$, ^) and run-together example blocks that render
# poorly, so for the displayed problems we curate clean markdown here. The spec,
# code, and proof shown in the explorer still come straight from the repo files.
DESCRIPTIONS = {
"lc121": """\
You are given an array `prices` where `prices[i]` is the price of a stock on day `i`.

Choose **one day to buy** and a **later day to sell** to maximize your profit. Return the maximum profit, or `0` if no profit is possible.

**Example 1**
```
Input:  prices = [7,1,5,3,6,4]
Output: 5
```
Buy on day 2 (price = 1) and sell on day 5 (price = 6): profit = 6 - 1 = 5. You must buy before you sell.

**Example 2**
```
Input:  prices = [7,6,4,3,1]
Output: 0
```
Prices only fall, so the best choice is no transaction: profit = 0.

**Constraints**
- 1 ≤ `prices.length` ≤ 10⁵
- 0 ≤ `prices[i]` ≤ 10⁴
""",

"lc169": """\
Given an array `nums` of size `n`, return the **majority element**: the value that appears more than ⌊n / 2⌋ times. A majority element is guaranteed to exist.

**Example 1**
```
Input:  nums = [3,2,3]
Output: 3
```

**Example 2**
```
Input:  nums = [2,2,1,1,1,2,2]
Output: 2
```

**Constraints**
- `n == nums.length`
- 1 ≤ n ≤ 5 × 10⁴
- -10⁹ ≤ `nums[i]` ≤ 10⁹
""",

"lc343": """\
Given an integer `n`, break it into a sum of `k` **positive integers** with `k ≥ 2`, and maximize the product of those integers. Return the maximum product.

**Example 1**
```
Input:  n = 2
Output: 1
```
2 = 1 + 1, and 1 × 1 = 1.

**Example 2**
```
Input:  n = 10
Output: 36
```
10 = 3 + 3 + 4, and 3 × 3 × 4 = 36.

**Constraints**
- 2 ≤ `n` ≤ 58
""",

"lc1492": """\
Given two positive integers `n` and `k`, list all factors of `n` (integers `i` with `n % i == 0`) in **ascending order**. Return the `k`th factor, or `-1` if `n` has fewer than `k` factors.

**Example 1**
```
Input:  n = 12, k = 3
Output: 3
```
Factors of 12 are [1, 2, 3, 4, 6, 12]; the 3rd is 3.

**Example 2**
```
Input:  n = 7, k = 2
Output: 7
```
Factors of 7 are [1, 7]; the 2nd is 7.

**Example 3**
```
Input:  n = 4, k = 4
Output: -1
```
Factors of 4 are [1, 2, 4]: only 3 factors, so return -1.

**Constraints**
- 1 ≤ `k` ≤ `n` ≤ 1000
""",

"lc1250": """\
Given an array `nums` of positive integers, pick any subset, multiply each chosen element by any integer, and sum the results. The array is **good** if some choice yields a total of exactly `1`. Return `true` if the array is good, otherwise `false`.

(Equivalently, the array is good exactly when the gcd of all its elements is 1.)

**Example 1**
```
Input:  nums = [12,5,7,23]
Output: true
```
Pick 5 and 7: 5·3 + 7·(-2) = 1.

**Example 2**
```
Input:  nums = [29,6,10]
Output: true
```
29·1 + 6·(-3) + 10·(-1) = 1.

**Example 3**
```
Input:  nums = [3,6]
Output: false
```

**Constraints**
- 1 ≤ `nums.length` ≤ 10⁵
- 1 ≤ `nums[i]` ≤ 10⁹
""",

"cf617A": """\
An elephant starts at point `0` and wants to reach his friend at point `x` (`x > 0`) on a line. In one step he can move forward by 1, 2, 3, 4, or 5. Find the **minimum number of steps** to reach `x`.

**Example 1**
```
Input:  5
Output: 1
```
One step of length 5 reaches the point.

**Example 2**
```
Input:  12
Output: 3
```
Move by 3, 5, and 4, for instance. It cannot be done in fewer than 3 steps.

**Constraints**
- 1 ≤ `x` ≤ 1 000 000
""",

"cf1826C": """\
There are `n` programmers and `m` options. Each round, every programmer votes for one still-available option; afterwards only the options with the most votes remain. This repeats until a single option is left.

For each test case, decide whether the process is **guaranteed to finish** in finitely many rounds no matter how people vote. Print `YES` or `NO`.

**Example**
```
 n         m         Answer
 3         2         YES
 4         2         NO
 5         3         YES
 1000000   1000000   NO
 1         1000000   YES
```

**Constraints**
- `t` test cases, each a pair of integers `n` and `m`.
""",

"cf478C": """\
You have `r` red, `g` green, and `b` blue balloons. Each table needs exactly three balloons that are **not all the same color**. Find the maximum number of tables `t` you can decorate.

**Example 1**
```
Input:  r = 5, g = 4, b = 3
Output: 4
```
One optimal set of tables: rgg, gbb, brr, rrg.

**Example 2**
```
Input:  r = 1, g = 1, b = 1
Output: 1
```

**Example 3**
```
Input:  r = 2, g = 3, b = 3
Output: 2
```

**Constraints**
- 0 ≤ `r`, `g`, `b` ≤ 2 × 10⁹
""",
}


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

        # prefer a hand-polished description; fall back to the raw source file
        desc = DESCRIPTIONS.get(pid, raw).strip()

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
