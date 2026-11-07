"""
fetch_problem.py — Fetch a LeetCode problem's description, tags, and Rust starter code.

Usage:
    python scripts/fetch_problem.py <title-slug>

Example:
    python scripts/fetch_problem.py remove-duplicates-from-sorted-array

This creates result/lc<id>/ (inside this skill folder) with:
  - description.md  (problem statement in markdown, faithful to LeetCode)
  - tags            (difficulty, topics, acceptance rate)

It also prints the Rust starter code snippet to stdout for reference.
"""

import urllib.request, json, html, re, sys, os


def fetch_problem(slug):
    url = "https://leetcode.com/graphql"
    query = """query questionData($titleSlug: String!) {
      question(titleSlug: $titleSlug) {
        questionFrontendId
        title
        content
        difficulty
        topicTags { name }
        stats
        isPaidOnly
        codeSnippets { lang langSlug code }
      }
    }"""
    payload = json.dumps(
        {
            "operationName": "questionData",
            "variables": {"titleSlug": slug},
            "query": query,
        }
    ).encode()
    req = urllib.request.Request(
        url,
        data=payload,
        headers={
            "Content-Type": "application/json",
            "Referer": "https://leetcode.com",
            "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
            "Origin": "https://leetcode.com",
        },
    )
    resp = urllib.request.urlopen(req)
    data = json.loads(resp.read())
    return data["data"]["question"]


def html_to_markdown(h):
    """Best-effort HTML-to-Markdown for LeetCode problem descriptions.
    For high-fidelity results, consider using the `markdownify` package instead."""
    # Links
    h = re.sub(r'<a[^>]*href="([^"]*)"[^>]*>(.*?)</a>', r"[\2](\1)", h, flags=re.DOTALL)
    # Bold / italic / code
    h = re.sub(r"<strong>(.*?)</strong>", r"**\1**", h)
    h = re.sub(r"<b>(.*?)</b>", r"**\1**", h)
    h = re.sub(r"<em>(.*?)</em>", r"*\1*", h)
    h = re.sub(r"<code>(.*?)</code>", r"`\1`", h)
    # Pre blocks
    h = re.sub(
        r"<pre>(.*?)</pre>",
        lambda m: "\n```\n" + m.group(1).strip() + "\n```\n",
        h,
        flags=re.DOTALL,
    )
    # Lists
    h = re.sub(r"<li>\s*", "- ", h)
    h = re.sub(r"</li>", "\n", h)
    h = re.sub(r"<ul>|</ul>|<ol>|</ol>", "", h)
    # Paragraphs / divs / breaks
    h = re.sub(r"<p>", "\n", h)
    h = re.sub(r"</p>", "\n", h)
    h = re.sub(r"</?div[^>]*>", "", h)
    h = re.sub(r"<sup>(.*?)</sup>", r"^\1", h)
    h = re.sub(r"<sub>(.*?)</sub>", r"_\1", h)
    h = re.sub(r"<br\s*/?>", "\n", h)
    h = re.sub(r"&nbsp;", " ", h)
    # Strip remaining tags (meta, span, etc.)
    h = re.sub(r"<[^>]+>", "", h)
    h = html.unescape(h)
    # Clean up excessive blank lines
    h = re.sub(r"\n{3,}", "\n\n", h)
    return h.strip()


def get_rust_snippet(q):
    """Extract the Rust code snippet from the problem data."""
    for s in q.get("codeSnippets", []):
        if s["langSlug"] == "rust":
            return s["code"]
    return None


def write_problem_files(q, repo_root):
    problem_id = q["questionFrontendId"]
    title = q["title"]
    difficulty = q["difficulty"]
    topics = ", ".join(t["name"] for t in q["topicTags"])
    stats = json.loads(q["stats"])
    acceptance = stats.get("acRate", "N/A")

    out_dir = os.path.join(repo_root, "result", f"lc{problem_id}")
    os.makedirs(out_dir, exist_ok=True)

    # description.md
    md = f"# {title}\n\n{html_to_markdown(q['content'])}\n"
    with open(os.path.join(out_dir, "description.md"), "w", encoding="utf-8") as f:
        f.write(md)

    # tags
    with open(os.path.join(out_dir, "tags"), "w", encoding="utf-8") as f:
        f.write(f"{difficulty}\n{topics}\nAcceptance rate: {acceptance}\n")

    return out_dir


def main():
    if len(sys.argv) < 2:
        print("Usage: python fetch_problem.py <title-slug>")
        print("Example: python fetch_problem.py remove-duplicates-from-sorted-array")
        sys.exit(1)

    slug = sys.argv[1]
    q = fetch_problem(slug)

    if q["isPaidOnly"]:
        print(f"ERROR: '{slug}' is a premium problem — content is not publicly available.")
        sys.exit(1)

    # Output is written to the skill's own `result/` folder so the script is
    # self-contained: <skill-dir>/result/lc<id>/. The script lives in
    # <skill-dir>/scripts/, so its parent directory is the skill dir.
    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    out_dir = write_problem_files(q, repo_root)

    print(f"Problem:    LC {q['questionFrontendId']} — {q['title']}")
    print(f"Difficulty: {q['difficulty']}")
    print(f"Output dir: {out_dir}")
    print()

    rust_snippet = get_rust_snippet(q)
    if rust_snippet:
        print("=== Rust starter code (use this for function signature) ===")
        print(rust_snippet)
    else:
        print("WARNING: No Rust code snippet found for this problem.")


if __name__ == "__main__":
    main()
