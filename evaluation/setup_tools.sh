#!/usr/bin/env bash
# Build the pinned third-party tools the scorer uses. Run from anywhere:
#   evaluation/setup_tools.sh
# Needs git and cargo (Rust 1.94.0). Installs into evaluation/tools/ only.
set -euo pipefail

here=$(cd "$(dirname "$0")" && pwd)
tools="$here/tools"
mkdir -p "$tools/src"

# lynette: checks that ProofGen answers keep the code and spec unchanged.
# Pinned upstream plus patches/lynette.patch (spec-fn soundness fix and fewer
# false rejections; see README.md "Improved lynette").
LYNETTE_REPO=https://github.com/microsoft/verus-proof-synthesis
LYNETTE_REV=af0d0f41657287447be8eeff98caebbec8499e5c
src="$tools/src/verus-proof-synthesis"
[ -d "$src/.git" ] || git clone --quiet --filter=blob:none "$LYNETTE_REPO" "$src"
git -C "$src" fetch --quiet origin "$LYNETTE_REV"
git -C "$src" checkout --quiet --force "$LYNETTE_REV"
git -C "$src" apply "$here/patches/lynette.patch"
cargo build --release --locked --manifest-path "$src/utils/lynette/source/Cargo.toml"
cp "$src/utils/lynette/source/target/release/lynette" "$tools/lynette"

echo "lynette: $tools/lynette"
