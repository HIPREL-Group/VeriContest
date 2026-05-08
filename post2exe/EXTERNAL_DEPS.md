# External Dependencies

Post2Exe uses the external open-source parser
[`secure-foundations/tree-sitter-verus`](https://github.com/secure-foundations/tree-sitter-verus).

We do not vendor that repository in VeriContest. Users who want to run Post2Exe
can decide whether to download and build it locally.

The local checkout path expected by Post2Exe is:

```text
post2exe/tree-sitter-verus/
```

The local version used during development was:

```text
repository: https://github.com/secure-foundations/tree-sitter-verus
commit: 33478ffa93c0f46eec3e1486c66c53ea9e70cd70
```

To install it from the VeriContest repository root:

```bash
git clone https://github.com/secure-foundations/tree-sitter-verus post2exe/tree-sitter-verus
cd post2exe/tree-sitter-verus
git checkout 33478ffa93c0f46eec3e1486c66c53ea9e70cd70
pip install -e .
```

After installation, Post2Exe expects the parser shared library at:

```text
post2exe/tree-sitter-verus/verus.so
```

Because `post2exe/tree-sitter-verus/` is listed in the top-level `.gitignore`,
a local checkout will not be uploaded when committing this repository.
