#!/usr/bin/env bash
# Application compatibility checks; no cubical code is imported into Horn.
# Each snapshot is checked as stored, then compressed and checked again.
set -euo pipefail
source_dir="$(cd "${1:?usage: bash scripts/check-kamo3.sh /path/to/kamo3}" && pwd)"
cd "$(dirname "$0")/.."
work="$(mktemp -d)"
trap 'rm -rf "$work"' EXIT
for fragment in path faces face-ops restricted systems composition sigma equivalence-defs glue equality canonical-map computation; do
  cat "$source_dir/theories/$fragment.horn" >> "$work/deep.horn"
  printf '\n' >> "$work/deep.horn"
done
cargo build --release --locked --offline --bins
bin_dir="${CARGO_TARGET_DIR:-target}/release"
for name in deep equiv glue identity ua ua-graph transport ua-beta homotopy transport-equiv glue-fiber contr-prop isequiv-prop to-pathp ua-unglue-center equiv-ext canonical-map compute constant-transport; do
  if [[ -f "$source_dir/examples/$name.proof.gz" ]]; then
    gzip -cd "$source_dir/examples/$name.proof.gz" > "$work/current.proof"
  else
    cp "$source_dir/examples/$name.proof" "$work/current.proof"
  fi
  printf '%s\n' "Checking $name"
  "$bin_dir/kernel" "$work/deep.horn" "$source_dir/examples/$name.goals" "$work/current.proof"
  "$bin_dir/horn-compress" "$work/deep.horn" "$work/current.proof" "$work/compact.proof"
  "$bin_dir/kernel" "$work/deep.horn" "$source_dir/examples/$name.goals" "$work/compact.proof"
  "$bin_dir/horn-oracle" encode "$work/deep.horn" "$source_dir/examples/$name.goals" "$work/current.proof" "$work/current.oracle"
  "$bin_dir/oracle-kernel" "$work/deep.horn" "$source_dir/examples/$name.goals" "$work/current.oracle"
  printf '%s -> %s compact -> %s oracle bytes\n' "$(stat -c %s "$work/current.proof")" "$(stat -c %s "$work/compact.proof")" "$(stat -c %s "$work/current.oracle")"
done
