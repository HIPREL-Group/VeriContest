"""
fetch_cf_solutions.py — Fetch editorial and top solutions for a Codeforces problem.

Usage:
    python scripts/fetch_cf_solutions.py <contestId> <index>

Example:
    python scripts/fetch_cf_solutions.py 1 A
    python scripts/fetch_cf_solutions.py 158 A

Strategy:
    1. Attempts to find the contest editorial by checking the contest author's
       blog entries for keywords like "editorial" or "tutorial".
    2. Lists top accepted submissions (handles, languages, timing).
    3. Notes that source code is not available via the API and provides the
       contest status URL for manual inspection.
"""

import urllib.request, json, sys, re, html as htmlmod, time as time_mod


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


def fetch_editorial(contest_id):
    """Try to find the editorial blog entry for the contest.

    Looks through the contest author's blog entries for titles containing
    editorial/tutorial keywords.
    """
    try:
        standings = api_get(
            f"contest.standings?contestId={contest_id}&from=1&count=1"
        )
    except Exception:
        return None

    contest = standings["contest"]
    author = contest.get("preparedBy")
    if not author:
        return None

    try:
        entries = api_get(f"user.blogEntries?handle={author}")
    except Exception:
        return None

    keywords = ["editorial", "tutorial", "разбор", "solution", "analysis"]
    contest_name = contest.get("name", "").lower()

    candidates = []
    for entry in entries:
        title_clean = re.sub(r"<[^>]+>", "", entry.get("title", "")).lower()

        has_keyword = any(kw in title_clean for kw in keywords)
        mentions_contest = (
            str(contest_id) in title_clean
            or any(
                word in title_clean
                for word in contest_name.split()
                if len(word) > 3
            )
        )

        if has_keyword and mentions_contest:
            candidates.append(entry)

    if not candidates:
        return None

    candidates.sort(key=lambda e: e.get("creationTimeSeconds", 0), reverse=True)

    try:
        blog = api_get(f"blogEntry.view?blogEntryId={candidates[0]['id']}")
        return blog
    except Exception:
        return None


def fetch_accepted_submissions(contest_id, index, count=10):
    """Fetch a sample of accepted submissions for the problem."""
    try:
        subs = api_get(
            f"contest.status?contestId={contest_id}&from=1&count=1000"
        )
    except Exception as e:
        print(f"  Warning: could not fetch submissions: {e}")
        return []

    accepted = []
    seen_handles = set()
    for sub in subs:
        if sub.get("verdict") != "OK":
            continue
        if sub["problem"]["index"].upper() != index.upper():
            continue
        members = sub.get("author", {}).get("members", [])
        if not members:
            continue
        handle = members[0]["handle"]
        if handle in seen_handles:
            continue
        accepted.append(sub)
        seen_handles.add(handle)
        if len(accepted) >= count:
            break

    return accepted


def clean_blog_content(raw):
    text = re.sub(r"<[^>]+>", "", raw)
    text = htmlmod.unescape(text)
    text = text.replace("\\n", "\n")
    text = text.encode("ascii", errors="replace").decode("ascii")
    return text.strip()


def print_submissions(submissions):
    if not submissions:
        print("  No submissions found.\n")
        return

    print(
        f"  {'Handle':<25} {'Language':<22} {'Time (ms)':<12} {'Memory (KB)':<12}"
    )
    print("  " + "-" * 70)
    for sub in submissions:
        handle = sub["author"]["members"][0]["handle"]
        lang = sub["programmingLanguage"]
        time_ms = sub["timeConsumedMillis"]
        mem_kb = sub["memoryConsumedBytes"] // 1024
        print(f"  {handle:<25} {lang:<22} {time_ms:<12} {mem_kb:<12}")
    print()


def main():
    if len(sys.argv) < 3:
        print("Usage: python fetch_cf_solutions.py <contestId> <index>")
        print("Example: python fetch_cf_solutions.py 1 A")
        sys.exit(1)

    contest_id = sys.argv[1]
    index = sys.argv[2].upper()

    ALLOWED_INDICES = {"A", "B", "C", "D"}
    if index not in ALLOWED_INDICES:
        print(f"ERROR: Only Div. 2 problems A, B, C, and D are in scope.")
        print(f"  Got index '{index}', which is outside the allowed set {ALLOWED_INDICES}.")
        sys.exit(1)

    print(f"=== Looking for editorial for contest {contest_id} ===\n")
    editorial = fetch_editorial(contest_id)

    if editorial:
        title = re.sub(r"<[^>]+>", "", editorial.get("title", ""))
        print(f"Found editorial: {title}")
        print(f"URL: https://codeforces.com/blog/entry/{editorial['id']}")
        print()
        content = editorial.get("content", "")
        if content:
            cleaned = clean_blog_content(content)
            if len(cleaned) > 5000:
                cleaned = (
                    cleaned[:5000]
                    + "\n\n... [truncated — see full editorial at URL above] ..."
                )
            print(cleaned)
        print("\n" + "=" * 72 + "\n")
    else:
        print("No editorial found automatically.")
        print(f"Check manually: https://codeforces.com/contest/{contest_id}")
        print()

    print(f"=== Top accepted submissions for {contest_id}/{index} ===\n")

    all_subs = fetch_accepted_submissions(contest_id, index)
    rust_subs = [
        s for s in all_subs if "rust" in s["programmingLanguage"].lower()
    ]

    if rust_subs:
        print(f"Rust submissions ({len(rust_subs)}):")
        print_submissions(rust_subs[:5])

    print(f"Top submissions across all languages ({len(all_subs)}):")
    print_submissions(all_subs[:10])

    print("NOTE: Codeforces does not expose submission source code via its API.")
    print("To view solution code, visit:")
    print(
        f"  https://codeforces.com/contest/{contest_id}/status/{index}"
        f"?order=BY_ARRIVED_ASC"
    )


if __name__ == "__main__":
    main()
