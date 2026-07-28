"""
submit_leetcode.py — Submit code to LeetCode, poll results, and fetch optimal code samples.

Uses curl_cffi to bypass Cloudflare TLS fingerprinting. Requires LEETCODE_SESSION
and LEETCODE_CSRF_TOKEN in a .env file at the repository root.

Usage:
    python scripts/submit_leetcode.py submit --slug <title-slug> --question-id <id> --code-file <path> [--lang rust]
    python scripts/submit_leetcode.py fetch-optimal --question-id <id> --submission-id <id> [--lang rust] [--output <path>]

Commands:
    submit          Submit code to LeetCode and print the result.
    fetch-optimal   Given a successful submission ID, fetch the fastest code sample
                    from the runtime distribution chart.

Examples:
    python scripts/submit_leetcode.py submit --slug two-sum --question-id 1 --code-file code.rs
    python scripts/submit_leetcode.py fetch-optimal --question-id 1 --submission-id 123456 --output optimal.rs

Install dependencies:
    pip install curl_cffi python-dotenv
"""

import argparse
import json
import os
import sys
import time

try:
    from curl_cffi import requests as cffi_requests
except ImportError:
    print(
        "ERROR: curl_cffi is not installed.\n"
        "Install it with:  pip install curl_cffi\n"
        "This library is required to bypass Cloudflare TLS fingerprinting."
    )
    sys.exit(1)

try:
    from dotenv import load_dotenv
except ImportError:
    print(
        "ERROR: python-dotenv is not installed.\n"
        "Install it with:  pip install python-dotenv"
    )
    sys.exit(1)


LEETCODE_GRAPHQL_URL = "https://leetcode.com/graphql"
LEETCODE_BASE_URL = "https://leetcode.com"
BROWSER_IMPERSONATE = "chrome120"
MAX_POLL_ATTEMPTS = 30
POLL_INTERVAL_SECONDS = 2
MAX_RETRIES = 3


def load_credentials():
    """Load LeetCode session credentials from .env file."""
    script_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.abspath(os.path.join(script_dir, "..", "..", ".."))
    env_path = os.path.join(repo_root, ".env")

    if not os.path.exists(env_path):
        print(f"ERROR: .env file not found at {env_path}")
        print("Create a .env file with LEETCODE_SESSION and LEETCODE_CSRF_TOKEN.")
        print("See the skill documentation for instructions on obtaining these values.")
        sys.exit(1)

    load_dotenv(env_path)

    session = os.getenv("LEETCODE_SESSION")
    csrf = os.getenv("LEETCODE_CSRF_TOKEN")

    if not session or not csrf:
        print("ERROR: LEETCODE_SESSION and/or LEETCODE_CSRF_TOKEN not set in .env")
        sys.exit(1)

    return session, csrf


def create_session(leetcode_session, csrf_token):
    """Create an authenticated curl_cffi session with browser TLS impersonation."""
    session = cffi_requests.Session(impersonate=BROWSER_IMPERSONATE)
    session.cookies.set("LEETCODE_SESSION", leetcode_session, domain="leetcode.com")
    session.cookies.set("csrftoken", csrf_token, domain="leetcode.com")
    session.headers.update({
        "Content-Type": "application/json",
        "Referer": f"{LEETCODE_BASE_URL}/",
        "Origin": LEETCODE_BASE_URL,
        "x-csrftoken": csrf_token,
    })
    return session


def validate_session(session):
    """Check if the LeetCode session is valid by querying the user profile.
    Sessions typically expire after ~2 weeks. Exits with a clear message if invalid."""
    query = """query { user { username isCurrentUserPremium } }"""
    try:
        payload = json.dumps({"query": query, "variables": {}})
        resp = session.post(LEETCODE_GRAPHQL_URL, data=payload)
        if resp.status_code == 200:
            data = resp.json()
            user = data.get("data", {}).get("user")
            if user and user.get("username"):
                print(f"  Authenticated as: {user['username']}")
                return True
        print(
            "ERROR: LeetCode session is expired or invalid.\n"
            "Sessions typically last ~2 weeks. Please refresh your credentials:\n"
            "  1. Log in to leetcode.com in your browser\n"
            "  2. Open DevTools (F12) > Application > Cookies > leetcode.com\n"
            "  3. Copy LEETCODE_SESSION and csrftoken into your .env file\n"
            "  See references/authentication_setup.md for details."
        )
        sys.exit(1)
    except Exception as e:
        print(f"ERROR: Could not validate session: {e}")
        sys.exit(1)


def graphql_request(session, query, variables, retries=MAX_RETRIES):
    """Send a GraphQL request to LeetCode with retry logic."""
    payload = json.dumps({"query": query, "variables": variables})
    for attempt in range(retries):
        try:
            resp = session.post(LEETCODE_GRAPHQL_URL, data=payload)
            if resp.status_code == 200:
                data = resp.json()
                if "data" in data:
                    return data
                print(f"  Warning: GraphQL response missing 'data': {data}")
            elif resp.status_code == 429:
                wait = 2 ** (attempt + 1)
                print(f"  Rate limited (429). Waiting {wait}s...")
                time.sleep(wait)
            else:
                print(f"  HTTP {resp.status_code}: {resp.text[:200]}")
        except Exception as e:
            print(f"  Request error (attempt {attempt + 1}/{retries}): {e}")
        if attempt < retries - 1:
            time.sleep(1.5 ** attempt)
    return None


def submit_code(session, slug, question_id, code, lang="rust"):
    """Submit code to LeetCode and return the submission ID."""
    url = f"{LEETCODE_BASE_URL}/problems/{slug}/submit/"
    payload = json.dumps({
        "lang": lang,
        "question_id": str(question_id),
        "typed_code": code,
    })

    for attempt in range(MAX_RETRIES):
        try:
            resp = session.post(url, data=payload)
            if resp.status_code == 200:
                data = resp.json()
                submission_id = data.get("submission_id")
                if submission_id:
                    return submission_id
                print(f"  Unexpected response: {data}")
            else:
                print(f"  Submit HTTP {resp.status_code}: {resp.text[:300]}")
        except Exception as e:
            print(f"  Submit error (attempt {attempt + 1}/{MAX_RETRIES}): {e}")
        if attempt < MAX_RETRIES - 1:
            time.sleep(2)

    return None


def poll_submission(session, submission_id):
    """Poll submission status until it completes. Returns the result dict."""
    url = f"{LEETCODE_BASE_URL}/submissions/detail/{submission_id}/check/"

    for attempt in range(MAX_POLL_ATTEMPTS):
        try:
            resp = session.get(url)
            if resp.status_code == 200:
                data = resp.json()
                state = data.get("state")
                if state == "SUCCESS":
                    return data
                elif state == "PENDING" or state == "STARTED":
                    pass
                else:
                    return data
            else:
                print(f"  Poll HTTP {resp.status_code}")
        except Exception as e:
            print(f"  Poll error: {e}")
        time.sleep(POLL_INTERVAL_SECONDS)

    print(f"  Timed out after {MAX_POLL_ATTEMPTS * POLL_INTERVAL_SECONDS}s")
    return None


def get_submission_details(session, submission_id):
    """Fetch submission details including runtime/memory distribution via GraphQL."""
    query = """query submissionDetails($submissionId: Int!) {
      submissionDetails(submissionId: $submissionId) {
        runtime
        runtimeDisplay
        runtimePercentile
        runtimeDistribution
        memory
        memoryDisplay
        memoryPercentile
        memoryDistribution
        code
        statusCode
      }
    }"""
    result = graphql_request(session, query, {"submissionId": int(submission_id)})
    if result and result.get("data", {}).get("submissionDetails"):
        return result["data"]["submissionDetails"]
    return None


def fetch_code_with_runtime(session, question_id, lang, runtime, skip=0):
    """Fetch a code sample at a specific runtime bucket from the distribution chart."""
    query = """query codeWithRuntime($questionId: Int!, $lang: String!, $runtime: Int!, $skip: Int!) {
      codeWithRuntime(
        questionId: $questionId
        lang: $lang
        runtime: $runtime
        skip: $skip
      ) {
        code
        hasPrevious
        hasNext
      }
    }"""
    variables = {
        "questionId": int(question_id),
        "lang": lang,
        "skip": skip,
        "runtime": int(runtime),
    }
    result = graphql_request(session, query, variables)
    if result and result.get("data", {}).get("codeWithRuntime"):
        return result["data"]["codeWithRuntime"]
    return None


def find_fastest_runtime_bucket(runtime_distribution_json):
    """Parse the runtimeDistribution JSON string and return the fastest (lowest ms) bucket."""
    try:
        dist = json.loads(runtime_distribution_json)
        distribution = dist.get("distribution", [])
        if not distribution:
            return None
        fastest = min(distribution, key=lambda x: float(x[0]))
        return int(float(fastest[0]))
    except (json.JSONDecodeError, ValueError, TypeError, IndexError) as e:
        print(f"  Error parsing runtime distribution: {e}")
        return None


def resolve_question_id(session, slug):
    """Resolve slug to internal questionId via GraphQL."""
    query = """query questionData($titleSlug: String!) {
      question(titleSlug: $titleSlug) {
        questionId
      }
    }"""
    result = graphql_request(session, query, {"titleSlug": slug})
    if result and result.get("data", {}).get("question"):
        q_data = result["data"]["question"]
        if q_data and q_data.get("questionId"):
            return int(q_data["questionId"])
    return None


def cmd_submit(args):
    """Handle the 'submit' command."""
    leetcode_session, csrf_token = load_credentials()
    session = create_session(leetcode_session, csrf_token)
    validate_session(session)

    if not os.path.exists(args.code_file):
        print(f"ERROR: Code file not found: {args.code_file}")
        sys.exit(1)

    with open(args.code_file, "r", encoding="utf-8") as f:
        code = f.read()

    question_id = args.question_id
    if not question_id:
        print(f"  Resolving question ID for slug '{args.slug}'...")
        question_id = resolve_question_id(session, args.slug)
        if not question_id:
            print(f"ERROR: Could not resolve question ID for slug '{args.slug}'.")
            sys.exit(1)
        print(f"  Resolved to question ID: {question_id}")

    print(f"Submitting {args.code_file} to LC #{question_id} ({args.slug})...")
    submission_id = submit_code(session, args.slug, question_id, code, lang=args.lang)

    if not submission_id:
        print("FAILED: Could not submit code.")
        sys.exit(1)

    print(f"  Submission ID: {submission_id}")
    print(f"  Polling for result...")

    result = poll_submission(session, submission_id)
    if not result:
        print("FAILED: Could not get submission result.")
        sys.exit(1)

    status = result.get("status_msg", "Unknown")
    runtime = result.get("status_runtime", "N/A")
    memory = result.get("status_memory", "N/A")
    total_correct = result.get("total_correct", "?")
    total_testcases = result.get("total_testcases", "?")

    print(f"\n{'='*50}")
    print(f"  Status:     {status}")
    print(f"  Runtime:    {runtime}")
    print(f"  Memory:     {memory}")
    print(f"  Test cases: {total_correct}/{total_testcases}")
    print(f"  Submission: https://leetcode.com/submissions/detail/{submission_id}/")
    print(f"{'='*50}")

    if status == "Accepted":
        print(f"\nSubmission ID for fetch-optimal: {submission_id}")
    else:
        if result.get("input_formatted"):
            print(f"\n  Failed input:    {result.get('input_formatted', 'N/A')[:200]}")
        if result.get("expected_output"):
            print(f"  Expected output: {result.get('expected_output', 'N/A')[:200]}")
        if result.get("code_output"):
            print(f"  Your output:     {result.get('code_output', 'N/A')[:200]}")
        if result.get("full_compile_error"):
            print(f"\n  Compile error:\n{result['full_compile_error'][:500]}")
        if result.get("full_runtime_error"):
            print(f"\n  Runtime error:\n{result['full_runtime_error'][:500]}")
        sys.exit(1)


def cmd_fetch_optimal(args):
    """Handle the 'fetch-optimal' command."""
    leetcode_session, csrf_token = load_credentials()
    session = create_session(leetcode_session, csrf_token)
    validate_session(session)

    print(f"Fetching submission details for ID {args.submission_id}...")
    details = get_submission_details(session, args.submission_id)

    if not details:
        print("FAILED: Could not retrieve submission details.")
        sys.exit(1)

    runtime_dist = details.get("runtimeDistribution")
    if not runtime_dist:
        print("FAILED: No runtimeDistribution data available for this submission.")
        sys.exit(1)

    fastest_runtime = find_fastest_runtime_bucket(runtime_dist)
    if fastest_runtime is None:
        print("FAILED: Could not parse runtime distribution.")
        sys.exit(1)

    print(f"  Fastest runtime bucket: {fastest_runtime} ms")
    print(f"  Fetching code sample at {fastest_runtime} ms...")

    time.sleep(0.5)
    code_data = fetch_code_with_runtime(
        session, args.question_id, args.lang, fastest_runtime, skip=0
    )

    if not code_data or not code_data.get("code"):
        print(f"  No code found at {fastest_runtime} ms. Trying next buckets...")
        dist = json.loads(runtime_dist)
        distribution = sorted(dist.get("distribution", []), key=lambda x: float(x[0]))
        found = False
        for bucket_runtime, _ in distribution:
            rt = int(float(bucket_runtime))
            if rt == fastest_runtime:
                continue
            time.sleep(0.5)
            code_data = fetch_code_with_runtime(
                session, args.question_id, args.lang, rt, skip=0
            )
            if code_data and code_data.get("code"):
                fastest_runtime = rt
                found = True
                print(f"  Found code at {rt} ms")
                break
        if not found:
            print("FAILED: Could not fetch any code sample from distribution.")
            sys.exit(1)

    optimal_code = code_data["code"]

    if args.output:
        with open(args.output, "w", encoding="utf-8") as f:
            f.write(optimal_code)
        print(f"\n  Optimal code ({fastest_runtime} ms) saved to: {args.output}")
    else:
        print(f"\n{'='*50}")
        print(f"Optimal code ({fastest_runtime} ms):")
        print(f"{'='*50}")
        print(optimal_code)
        print(f"{'='*50}")

    print(f"\n  Runtime percentile: {details.get('runtimePercentile', 'N/A')}")
    print(f"  Memory:            {details.get('memoryDisplay', 'N/A')}")
    print(f"  Memory percentile: {details.get('memoryPercentile', 'N/A')}")


def main():
    parser = argparse.ArgumentParser(
        description="Submit code to LeetCode and fetch optimal code samples.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    subparsers = parser.add_subparsers(dest="command", required=True)

    # submit command
    submit_parser = subparsers.add_parser(
        "submit", help="Submit code to LeetCode and print the result."
    )
    submit_parser.add_argument("--slug", required=True, help="LeetCode problem title-slug")
    submit_parser.add_argument("--question-id", type=int, help="LeetCode question ID (numeric, optional if slug is provided)")
    submit_parser.add_argument("--code-file", required=True, help="Path to the code file to submit")
    submit_parser.add_argument("--lang", default="rust", help="Language slug (default: rust)")

    # fetch-optimal command
    fetch_parser = subparsers.add_parser(
        "fetch-optimal", help="Fetch the fastest code sample from runtime distribution."
    )
    fetch_parser.add_argument("--question-id", required=True, type=int, help="LeetCode question ID (numeric)")
    fetch_parser.add_argument("--submission-id", required=True, type=int, help="Accepted submission ID")
    fetch_parser.add_argument("--lang", default="rust", help="Language slug (default: rust)")
    fetch_parser.add_argument("--output", help="Output file path for the optimal code")

    args = parser.parse_args()

    if args.command == "submit":
        cmd_submit(args)
    elif args.command == "fetch-optimal":
        cmd_fetch_optimal(args)


if __name__ == "__main__":
    main()
