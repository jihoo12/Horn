#!/usr/bin/env bash
# Translation validation of a cubical script's certificate in Cubical Agda.
#
#   scripts/adequacy/run.sh WORKDIR NAME K
#
# Certifies examples/cubical/script/NAME.hcs, expands the certificate into
# ground judgments, checks every syntactic fact against reference semantics,
# and checks up to K rhas/req conclusions per rule in Cubical Agda (needs
# `agda` 2.8 on PATH). Set HORN_COMP_FF=transp to read a composition at the
# empty face as Agda's transp. Nothing here is trusted by Horn.
set -euo pipefail
T=$(cd "$(dirname "$0")" && pwd); R=$(cd "$T/../.." && pwd)
W=$1; n=$2; k=$3; c=$W/c/$n
mkdir -p "$W/c"
[ -f "$c/proof.oracle" ] || "$R/target/release/horn" cubical eval "$R/examples/cubical/script/$n.hcs" --emit "$c" > /dev/null
[ -f "$c/proof.compact" ] || "$R/target/release/horn-oracle" decode "$c/theory.horn" "$c/goals" "$c/proof.oracle" "$c/proof.compact" > /dev/null
[ -f "$c/steps.pkl" ] || python3 -I "$T/expand.py" "$c/theory.horn" "$c/proof.compact" "$c/steps.pkl" > /dev/null
[ -f "$c/steps.pkl.syntax" ] || python3 -I "$T/check_syntax.py" "$c/steps.pkl" | head -2
o=$W/runs/$n-$k${HORN_COMP_FF:+-$HORN_COMP_FF}; rm -rf "$o"; mkdir -p "$o"
python3 -I "$T/emit.py" "$c/theory.horn" "$c/steps.pkl" "$o" rules "$k"
cp "$T/HornPrelude.agda" "$o/"
(cd "$o" && agda --no-libraries HornDefs.agda > defs.log 2>&1) || { echo "definitions rejected"; tail -5 "$o/defs.log"; exit 1; }
(cd "$o" && python3 -I "$T/run_agda.py" . 64 4)
