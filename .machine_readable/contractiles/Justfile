# Minimal proof-focused task runner for tropical-resource-typing.

default:
    @just --list

# Run the primary proof check.
test:
    @just isabelle-build

# Type-check all Isabelle theories in the Tropical_Semirings session.
isabelle-build:
    #!/usr/bin/env bash
    set -euo pipefail
    ISABELLE=$(command -v isabelle 2>/dev/null || echo "$HOME/Isabelle/bin/isabelle")
    if [ ! -x "$ISABELLE" ]; then
        echo "ERROR: isabelle not found. Install Isabelle and ensure it is on PATH."
        exit 1
    fi
    export ISABELLE_HOME_USER="${ISABELLE_HOME_USER:-/tmp/isabelle-home-user}"
    mkdir -p "$ISABELLE_HOME_USER"
    echo "Building Tropical_Semirings with $ISABELLE ..."
    cd {{justfile_directory()}} && "$ISABELLE" build -D . -v Tropical_Semirings

# Lightweight guard: ensure no explicit sorry placeholders remain.
check-sorry:
    #!/usr/bin/env bash
    set -euo pipefail
    COUNT=$(grep -rn "^[[:space:]]*sorry\\b" {{justfile_directory()}}/*.thy | wc -l || true)
    echo "Actual sorry count: $COUNT"
    if [ "$COUNT" -gt 0 ]; then
        grep -rn "^[[:space:]]*sorry\\b" {{justfile_directory()}}/*.thy || true
        echo "Sorry placeholders detected."
        exit 1
    fi
    echo "No sorry placeholders found."
