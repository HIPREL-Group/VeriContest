"""
fetch_cf_problem.py — Fetch a Codeforces problem's description, tags, and metadata.

Usage:
    python scripts/fetch_cf_problem.py <contestId> <index>

Example:
    python scripts/fetch_cf_problem.py 1 A
    python scripts/fetch_cf_problem.py 158 A

This creates result/cf<contestId><index>/ (inside this skill folder) with:
  - description.md  (problem statement in markdown, faithful to Codeforces)
  - tags            (rating, topics, solved count)
"""

import urllib.request, json, html, re, sys, os, time as time_mod


CODEFORCES_API = "https://codeforces.com/api"
HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
}
RATE_LIMIT_DELAY = 2.1


def api_get(path):
    url = f"{CODEFORCES_API}/{path}"
    req = urllib.request.Request(url, headers=HEADERS)
    resp = urllib.request.urlopen(req)
    data = json.loads(resp.read())
    time_mod.sleep(RATE_LIMIT_DELAY)
    if data["status"] != "OK":
        raise RuntimeError(f"API error: {data.get('comment', 'unknown')}")
    return data["result"]


def fetch_problem_meta(contest_id, index):
    result = api_get(f"contest.standings?contestId={contest_id}&from=1&count=1")
    for p in result["problems"]:
        if p["index"].upper() == index.upper():
            return p, result["contest"]
    raise RuntimeError(f"Problem {index.upper()} not found in contest {contest_id}")


def fetch_solved_count(contest_id, index):
    try:
        result = api_get("problemset.problems")
        for ps in result["problemStatistics"]:
            if ps.get("contestId") == int(contest_id) and ps["index"].upper() == index.upper():
                return ps.get("solvedCount")
    except Exception:
        pass
    return None


def fetch_problem_page(contest_id, index):
    url = f"https://codeforces.com/problemset/problem/{contest_id}/{index.upper()}"
    req = urllib.request.Request(url, headers=HEADERS)
    resp = urllib.request.urlopen(req)
    return resp.read().decode("utf-8")


def _find_div_extent(text, start):
    """Given text starting right after an opening <div ...>, find the matching
    </div> and return the index just past it.  Returns the content between the
    opening tag and the closing tag, plus the end position."""
    depth = 1
    i = start
    while i < len(text) and depth > 0:
        if text[i:i + 4] == "<div":
            depth += 1
        elif text[i:i + 6] == "</div>":
            if depth == 1:
                return text[start:i], i + 6
            depth -= 1
        i += 1
    return text[start:], len(text)


def _find_section(text, class_name):
    """Find a <div class="class_name"> in *text* and return (content, start, end)
    where content is the inner HTML and start/end delimit the whole element."""
    marker = f'<div class="{class_name}">'
    idx = text.find(marker)
    if idx == -1:
        return None, -1, -1
    inner_start = idx + len(marker)
    content, end = _find_div_extent(text, inner_start)
    return content, idx, end


def extract_problem_div(page_html):
    """Extract raw HTML inside <div class="problem-statement">...</div>."""
    content, _, _ = _find_section(page_html, "problem-statement")
    return content


def _strip_tags(s):
    s = re.sub(r"<br\s*/?>", "\n", s)
    return html.unescape(re.sub(r"<[^>]+>", "", s))


def _convert_inline(h):
    """Convert inline HTML formatting to Markdown."""
    h = re.sub(r'<span class="tex-font-style-it">(.*?)</span>', r"*\1*", h)
    h = re.sub(r'<span class="tex-font-style-bf">(.*?)</span>', r"**\1**", h)
    h = re.sub(r'<span class="tex-font-style-tt">(.*?)</span>', r"`\1`", h)
    h = re.sub(
        r'<span class="tex-span">(.*?)</span>',
        lambda m: "$" + _strip_tags(m.group(1)) + "$",
        h,
    )
    h = re.sub(r"<strong>(.*?)</strong>", r"**\1**", h)
    h = re.sub(r"<b>(.*?)</b>", r"**\1**", h)
    h = re.sub(r"<em>(.*?)</em>", r"*\1*", h)
    h = re.sub(r"<code>(.*?)</code>", r"`\1`", h)
    h = re.sub(r"<sup>(.*?)</sup>", r"^\1", h)
    h = re.sub(r"<sub>(.*?)</sub>", r"_\1", h)
    return h


def _body_to_md(body_html):
    """Convert a chunk of inner HTML to Markdown text."""
    h = _convert_inline(body_html)
    h = re.sub(r'<div class="section-title">.*?</div>', "", h)
    h = re.sub(r"<li>\s*", "- ", h)
    h = re.sub(r"</li>", "\n", h)
    h = re.sub(r"</?[uo]l[^>]*>", "", h)
    h = re.sub(r"<p>", "\n", h)
    h = re.sub(r"</p>", "\n", h)
    h = re.sub(r"<br\s*/?>", "\n", h)
    h = re.sub(r"&nbsp;", " ", h)
    h = re.sub(r"<[^>]+>", "", h)
    h = html.unescape(h)
    h = re.sub(r"\n{3,}", "\n\n", h)
    return h.strip()


def problem_html_to_markdown(raw_html, title):
    """Convert Codeforces problem-statement inner HTML to clean Markdown."""
    parts = [f"# {title}\n"]

    # --- header (time/memory limits) ---
    header_html, hdr_start, hdr_end = _find_section(raw_html, "header")
    if header_html is not None:
        tl_html, _, _ = _find_section(header_html, "time-limit")
        ml_html, _, _ = _find_section(header_html, "memory-limit")
        limits = []
        if tl_html is not None:
            tl_text = re.sub(r'<div class="property-title">.*?</div>', "", tl_html)
            limits.append("Time limit: " + _strip_tags(tl_text).strip())
        if ml_html is not None:
            ml_text = re.sub(r'<div class="property-title">.*?</div>', "", ml_html)
            limits.append("Memory limit: " + _strip_tags(ml_text).strip())
        if limits:
            parts.append(" | ".join(limits) + "\n")

    # Everything after the header is the "body" area.
    body_area = raw_html[hdr_end:] if header_html is not None else raw_html

    # Locate each named section inside body_area.
    inp_html, inp_s, inp_e = _find_section(body_area, "input-specification")
    out_html, out_s, out_e = _find_section(body_area, "output-specification")
    sam_html, sam_s, sam_e = _find_section(body_area, "sample-tests")
    note_html, note_s, note_e = _find_section(body_area, "note")

    # The problem statement text is everything before the first named section.
    first = len(body_area)
    for s in [inp_s, out_s, sam_s, note_s]:
        if 0 <= s < first:
            first = s

    statement_md = _body_to_md(body_area[:first])
    if statement_md:
        parts.append(statement_md + "\n")

    if inp_html is not None:
        parts.append("## Input\n")
        parts.append(_body_to_md(inp_html) + "\n")

    if out_html is not None:
        parts.append("## Output\n")
        parts.append(_body_to_md(out_html) + "\n")

    if sam_html is not None:
        inputs = re.findall(
            r'<div class="input">.*?<pre[^>]*>(.*?)</pre>',
            sam_html,
            re.DOTALL,
        )
        outputs = re.findall(
            r'<div class="output">.*?<pre[^>]*>(.*?)</pre>',
            sam_html,
            re.DOTALL,
        )
        if inputs:
            parts.append("## Examples\n")
            for idx, (inp, out) in enumerate(zip(inputs, outputs), 1):
                if len(inputs) > 1:
                    parts.append(f"### Example {idx}\n")
                parts.append(f"**Input:**\n```\n{_strip_tags(inp).strip()}\n```\n")
                parts.append(f"**Output:**\n```\n{_strip_tags(out).strip()}\n```\n")

    if note_html is not None:
        note_md = _body_to_md(note_html)
        if note_md:
            parts.append("## Note\n")
            parts.append(note_md + "\n")

    return "\n".join(parts) + "\n"


def write_problem_files(meta, contest, solved_count, description_md, repo_root):
    contest_id = meta["contestId"]
    index = meta["index"]
    rating = meta.get("rating", "N/A")
    tags = ", ".join(meta.get("tags", []))
    solved_str = str(solved_count) if solved_count is not None else "N/A"

    out_dir = os.path.join(repo_root, "result", f"cf{contest_id}{index}")
    os.makedirs(out_dir, exist_ok=True)

    with open(os.path.join(out_dir, "description.md"), "w", encoding="utf-8") as f:
        f.write(description_md)

    with open(os.path.join(out_dir, "tags"), "w", encoding="utf-8") as f:
        f.write(f"Rating: {rating}\n{tags}\nSolved by: {solved_str} users\n")

    return out_dir


def main():
    if len(sys.argv) < 3:
        print("Usage: python fetch_cf_problem.py <contestId> <index>")
        print("Example: python fetch_cf_problem.py 1 A")
        print("         python fetch_cf_problem.py 158 A")
        sys.exit(1)

    contest_id = sys.argv[1]
    index = sys.argv[2]

    print(f"Fetching metadata for CF {contest_id}/{index.upper()}...")
    meta, contest = fetch_problem_meta(contest_id, index)

    MAX_RATING = 1600
    rating = meta.get("rating")
    if rating is None:
        print(f"ERROR: Problem CF {contest_id}/{index.upper()} has no rating assigned.")
        print(f"  Only problems with rating <= {MAX_RATING} are in scope.")
        sys.exit(1)
    if rating > MAX_RATING:
        print(f"ERROR: Problem CF {contest_id}/{index.upper()} has rating {rating}, which exceeds the limit of {MAX_RATING}.")
        sys.exit(1)

    print(f"Fetching solved count...")
    solved_count = fetch_solved_count(contest_id, index)

    print(f"Scraping problem page...")
    page_html = fetch_problem_page(contest_id, index)

    raw_div = extract_problem_div(page_html)
    if not raw_div:
        print("ERROR: Could not extract problem statement from the page.")
        print("The page structure may have changed. Try manually creating description.md.")
        sys.exit(1)

    description_md = problem_html_to_markdown(raw_div, meta["name"])

    # Output is written to the skill's own `result/` folder so the script is
    # self-contained: <skill-dir>/result/cf<contestId><index>/. The script lives
    # in <skill-dir>/scripts/, so its parent directory is the skill dir.
    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
    out_dir = write_problem_files(meta, contest, solved_count, description_md, repo_root)

    print()
    print(f"Problem:    CF {contest_id}{index.upper()} — {meta['name']}")
    print(f"Contest:    {contest.get('name', 'N/A')}")
    print(f"Rating:     {meta.get('rating', 'N/A')}")
    print(f"Tags:       {', '.join(meta.get('tags', []))}")
    if solved_count is not None:
        print(f"Solved by:  {solved_count} users")
    print(f"Output dir: {out_dir}")
    print()
    print("NOTE: Codeforces does not provide starter code. Design the function")
    print("signature from the problem's input/output specification (see SKILL Step 3).")


if __name__ == "__main__":
    main()
