#!/usr/bin/env bash
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# check-chapel-bridge.sh — runtime sibling of tools/chapel-bridge.scm
#
# Why a Bash sibling:
#   chapel-bridge.scm is the canonical capability gate, but Guile is
#   not currently installed on every build host (it is itself an
#   optional dep on Kinoite). This script implements the same
#   chpl-on-PATH detection in plain Bash so the standard build can
#   honour the cap:chapel-2 declaration in coordination.k9 without a
#   Guile prerequisite.
#
# Exit codes:
#   0 — Chapel present + version reported on stdout
#   1 — Chapel absent (graceful: not an error for cap:chapel-2: optional)
#   2 — `chpl` found on PATH but failed to report a version (broken install)
#
# Output is one line on stdout; diagnostics go to stderr.

set -uo pipefail

if ! command -v chpl >/dev/null 2>&1; then
  echo "chapel: absent" >&2
  echo "[chapel-bridge] cap:chapel-2 optional → not present; standard build unaffected." >&2
  echo "absent"
  exit 1
fi

if ver=$(chpl --version 2>/dev/null | head -1); then
  echo "chapel: ${ver}"
  exit 0
else
  echo "chapel: present-but-broken" >&2
  echo "[chapel-bridge] chpl on PATH but --version failed; treat as absent." >&2
  echo "broken"
  exit 2
fi
