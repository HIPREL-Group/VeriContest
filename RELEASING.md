# Releasing VeriContest

This is the maintainer guide for versioning the benchmark and its Verus
toolchain.

## Versioning policy

A **release** freezes three things together: the benchmark source revision,
the problem list, and the exact Verus build that verifies it. Leaderboard
results are only comparable within one release.

- Releases are named after the year and month of the release: git tag
  `vYYYY.MM`, release id `YYYY-MM` in `leaderboard/release.json`. If a second
  release happens in the same month, use `vYYYY.MM.1` and `YYYY-MM.1`.
- Verus publishes new builds very frequently. Do **not** cut a release for every
  Verus build. Bump Verus deliberately, for example when a needed feature or fix
  lands, or a few times per year.
- Cut a new release when any of these change:
  - problem membership (problems added or removed)
  - scoring-relevant artifacts (`spec.rs`, `code_spec.rs`, `verified.rs`,
    checkers, or test cases)
  - the pinned Verus build or verification flags
- Docs, website, and leaderboard tooling changes do not need a new release.

## What a release pins

| Item | Where it is recorded |
|---|---|
| Source revision | git tag; `benchmark_revision` in `leaderboard/release.json` |
| Problem list | `leaderboard/problem_ids.txt` and its sha256 in `release.json` |
| Verus build | `verus` in `release.json`; `verus/version.json` |
| Verus toolchain archive | GitHub Release asset; sha256 in `release.json` |
| Verification flags | `verus.flags` in `release.json` |
| Test cases | Hugging Face dataset tag with the same name as the git tag |
| What changed | `CHANGELOG.md` entry; GitHub Release notes |

Always attach the Verus toolchain to the GitHub Release. Upstream rolling
builds get pruned, so the archive in our release may become the only copy.

## Cutting a release

1. Make sure the benchmark is committed and `benchmark/` has no uncommitted changes.
2. Verify every problem with the pinned toolchain:

   ```bash
   mkdir -p /tmp/vc-verify
   find benchmark -name verified.rs | sort | xargs -P "$(nproc)" -I{} sh -c \
     './verus/verus --no-cheating --expand-errors --rlimit 100000 "$1" >/tmp/vc-verify/$(echo "$1" | tr / _).log 2>&1 || echo "FAIL $1"' _ {}
   grep -h "^verification results::" /tmp/vc-verify/*.log | grep -vc " 0 errors"   # must print 0
   ```

   No `FAIL` line should be printed.
3. Build the toolchain archive from the release commit. Archive the commit (not
   the `<rev>:verus` tree) so file times are fixed and the hash is reproducible:

   ```bash
   REV=<release commit>; VER=$(python3 -c 'import json;print(json.load(open("verus/version.json"))["verus"]["version"])')
   git archive --format=tar "$REV" verus | gzip -n -9 > "verus-$VER-x86-linux.tar.gz"
   sha256sum "verus-$VER-x86-linux.tar.gz"
   ```

4. Update `leaderboard/release.json` (`id`, `git_tag`, `benchmark_revision`,
   `counts`, `problem_ids_sha256`, `verus`, `verus_archive`) and the protocol
   `release` and `verus_version` fields. Run `python3 leaderboard/manage.py validate`
   and `python3 -m unittest discover -s leaderboard -p 'test_*.py'`, then
   `python3 leaderboard/manage.py build` to refresh the website data.
5. In `CHANGELOG.md`, rename **Unreleased** to the new tag, add the commit and
   Verus version, and start a new empty **Unreleased** section.
6. Tag the commit and create the GitHub Release. Use that changelog entry as the
   release notes and attach only the toolchain archive:

   ```bash
   git tag -a <tag> "$REV" -m "VeriContest <tag>"
   git push origin <tag>
   gh release create <tag> --title "VeriContest <tag>" --notes-file <notes.md> "verus-$VER-x86-linux.tar.gz"
   ```

7. If the test cases changed, tag the matching Hugging Face dataset revision
   with the same name.

## Bumping Verus

1. Download the new build from
   [verus-lang/verus releases](https://github.com/verus-lang/verus/releases)
   and replace `verus/`.
2. Run the full verification from step 2 above and fix every failure.
   Also re-check the other Verus-checked artifacts (`code_spec.rs`, `spec.rs`,
   test generators under `tests/`), since syntax and `vstd` changes can break
   them too. Treat deprecation warnings as future errors.
3. If proofs needed changes, re-run the spec-validation and testcase checks for
   the affected problems.
4. Cut a new release as above. Existing leaderboard entries stay attached to
   their old release and must be re-evaluated before being ranked on the new one.
