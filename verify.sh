#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p verification
lake build JSP572Four 2>&1 | tee verification/build.log
lake env lean Audit.lean 2>&1 | tee verification/axioms.log
printf '%s\n' 'Complete theorem build and axiom allowlist audit passed.'
