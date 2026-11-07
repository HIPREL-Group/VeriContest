"""
fetch_solutions.py — Fetch top-rated community solutions for a LeetCode problem.

Usage:
    python scripts/fetch_solutions.py <title-slug> [--lang LANG] [--top N]

Example:
    python scripts/fetch_solutions.py search-in-rotated-sorted-array
    python scripts/fetch_solutions.py two-sum --lang python3 --top 3

Strategy:
    1. Fetches Rust solutions first.
    2. If no high-rated Rust solutions exist, falls back to Python.
    3. If still nothing useful, fetches top solutions across all languages.
"""

import urllib.request, json, sys, argparse, re, html as htmlmod


GRAPHQL_URL = "https://leetcode.com/graphql"
HEADERS = {
    "Content-Type": "application/json",
    "Referer": "https://leetcode.com",
    "Origin": "https://leetcode.com",
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36",
}
VOTE_THRESHOLD = 25


def fetch_solutions(slug, lang_tags=None, top=5):
    query = """query questionSolutions($filters: QuestionSolutionsFilterInput!) {
      questionSolutions(filters: $filters) {
        totalNum
        solutions {
          id
          title
          post {
            id
            voteCount
            content
            author { username }
          }
        }
      }
    }"""
    filters = {
        "questionSlug": slug,
        "first": top,
        "skip": 0,
        "orderBy": "most_votes",
    }
    if lang_tags:
        filters["languageTags"] = lang_tags

    payload = json.dumps({"query": query, "variables": {"filters": filters}}).encode()
    req = urllib.request.Request(GRAPHQL_URL, data=payload, headers=HEADERS)
    resp = urllib.request.urlopen(req)
    data = json.loads(resp.read())
    qs = data.get("data", {}).get("questionSolutions")
    if not qs:
        return 0, []
    return qs["totalNum"], qs["solutions"]


def clean_content(raw):
    """Strip HTML tags and unescape entities for readable output."""
    text = re.sub(r"<[^>]+>", "", raw)
    text = htmlmod.unescape(text)
    # Collapse \\n literals (LeetCode stores newlines this way)
    text = text.replace("\\n", "\n")
    # Replace non-ASCII characters that may break Windows console encoding
    text = text.encode("ascii", errors="replace").decode("ascii")
    return text.strip()


def print_solutions(solutions, lang_label):
    if not solutions:
        print(f"  No {lang_label} solutions found.\n")
        return
    for sol in solutions:
        post = sol["post"]
        author = post["author"]["username"] if post.get("author") else "anonymous"
        votes = post["voteCount"]
        title = sol["title"].encode("ascii", errors="replace").decode("ascii")
        print(f"=== {title} (votes: {votes}, by: {author}) ===")
        print(clean_content(post["content"]))
        print("\n---\n")


def has_high_rated(solutions):
    return any(s["post"]["voteCount"] >= VOTE_THRESHOLD for s in solutions)


def main():
    parser = argparse.ArgumentParser(description="Fetch top LeetCode community solutions.")
    parser.add_argument("slug", help="LeetCode problem title-slug (e.g. two-sum)")
    parser.add_argument("--lang", help="Language tag to filter by (e.g. rust, python3). "
                        "If omitted, uses the automatic Rust → Python → all fallback strategy.")
    parser.add_argument("--top", type=int, default=5, help="Number of solutions to fetch (default: 5)")
    args = parser.parse_args()

    if args.lang:
        # Explicit language requested — just fetch and print
        total, solutions = fetch_solutions(args.slug, lang_tags=[args.lang], top=args.top)
        print(f"Found {total} total {args.lang} solutions for '{args.slug}'.\n")
        print_solutions(solutions, args.lang)
        return

    # Automatic fallback: Rust → Python → all
    print(f"Searching for Rust solutions for '{args.slug}'...")
    total, solutions = fetch_solutions(args.slug, lang_tags=["rust"], top=args.top)
    print(f"  {total} Rust solutions available.\n")

    if has_high_rated(solutions):
        print_solutions(solutions, "Rust")
        return

    print(f"No high-rated Rust solutions. Falling back to Python...")
    total, solutions = fetch_solutions(args.slug, lang_tags=["python3"], top=args.top)
    print(f"  {total} Python solutions available.\n")

    if has_high_rated(solutions):
        print_solutions(solutions, "Python")
        return

    print(f"No high-rated Python solutions either. Fetching top solutions across all languages...")
    total, solutions = fetch_solutions(args.slug, top=args.top)
    print(f"  {total} total solutions available.\n")
    print_solutions(solutions, "all languages")


if __name__ == "__main__":
    main()
