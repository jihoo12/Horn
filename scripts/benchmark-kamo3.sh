#!/usr/bin/env bash
# Check existing application snapshots; certificate generation is not timed.
set -euo pipefail
source_dir="$(cd "${1:?usage: bash scripts/benchmark-kamo3.sh KAMO3 OUTPUT_DIR [RUNS=5]}" && pwd)"
mkdir -p "${2:?missing output directory}"
output_dir="$(cd "$2" && pwd)"
runs="${3:-5}"
cd "$(dirname "$0")/.."
for fragment in path faces face-ops restricted systems composition sigma equivalence-defs glue equality canonical-map computation; do
  cat "$source_dir/theories/$fragment.horn"
  printf '\n'
done > "$output_dir/deep.horn"
{
  rustc --version
  uname -sm
  git rev-parse HEAD
  git status --short
} > "$output_dir/environment.txt"
cargo build --release --locked --offline --example benchmark
bin_dir="${CARGO_TARGET_DIR:-target}/release/examples"
for name in ua-beta compute; do
  if [[ -f "$source_dir/examples/$name.proof.gz" ]]; then
    gzip -cd "$source_dir/examples/$name.proof.gz" > "$output_dir/$name.proof"
  else
    cp "$source_dir/examples/$name.proof" "$output_dir/$name.proof"
  fi
  sha256sum "$output_dir/deep.horn" "$source_dir/examples/$name.goals" "$output_dir/$name.proof" > "$output_dir/$name.sha256"
  "$bin_dir/benchmark" "$output_dir/deep.horn" "$source_dir/examples/$name.goals" "$output_dir/$name.proof" "$runs" > "$output_dir/$name.csv"
done
