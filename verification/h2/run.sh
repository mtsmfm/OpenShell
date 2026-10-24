#!/usr/bin/env bash
# Run TLC on every config. JAVA and TLA2TOOLS point at a JRE and tla2tools.jar (v1.8.0).
# Bug_*.cfg seed a defect and are expected to report a violation.
set -u
cd "$(dirname "$0")"
for cfg in Safety.cfg Liveness1.cfg Liveness2.cfg Bug_*.cfg; do
  echo "== $cfg"
  "${JAVA:-java}" -XX:+UseParallelGC -cp "$TLA2TOOLS" tlc2.TLC -deadlock -workers auto \
    -metadir "${TMPDIR:-/tmp}/h2relay-tlc/$cfg" -config "$cfg" H2Relay.tla |
    grep -E 'violated|No error|distinct states found, 0|depth of'
done
rm -f H2Relay_TTrace_*
