# VeriContest Authoring Skills

This directory holds self-contained guides for adding new verified benchmark
problems to VeriContest. Each skill bundles its own workflow, scripts, and
reference material, so it can be followed without depending on anything outside
the skill folder.

## Available Skills

- [`add-leetcode-benchmark/`](add-leetcode-benchmark/SKILL.md) — add a new
  LeetCode problem.
- [`add-codeforces-benchmark/`](add-codeforces-benchmark/SKILL.md) — add a new
  Codeforces problem (handles the `main.rs` stdin/stdout split).

## How to Use

These skills are written for an **AI coding agent** (e.g. Claude Code), not for
manual execution. You drive the work by asking the agent to add a problem; the
agent loads the matching skill and carries out the workflow itself.

1. Run a coding agent inside the VeriContest repository.
2. Ask it to add a problem, e.g. *"add LeetCode problem two-sum"* or *"add
   Codeforces problem 1 A"*. The agent selects the matching skill from this
   folder based on the request.
3. The agent then follows the skill's `SKILL.md` top to bottom — choosing a
   suitable problem, fetching the description, writing `spec.rs`, implementing the
   code, proving `verified.rs`, and checking consistency — running the bundled
   scripts and the `./verus/verus` toolchain on your behalf.

You do not need to invoke the scripts or Verus yourself; the `SKILL.md` files
document those commands so the agent knows how to run them.

## Related Repository Folders

- `benchmark/` — where finished problems live (`leetcode/`, `codeforces/`).
- `lemmas/` — reusable Verus proof lemmas to consult while proving. 
- `verus/` — the bundled Verus toolchain, invoked as `./verus/verus`.
