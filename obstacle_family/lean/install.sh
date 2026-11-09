#!/usr/bin/env bash
# Installs Lean (through elan, which reads the version pinned in TsigmaProof/lean-toolchain),
# downloads Mathlib's prebuilt cache (about 5 GB), builds the proof and prints its axioms.
set -euo pipefail
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
if ! command -v elan >/dev/null 2>&1; then
  if command -v brew >/dev/null 2>&1; then
    brew install elan-init
    elan-init -y --default-toolchain none
  else
    echo "elan is not installed. Install it as described at" >&2
    echo "https://lean-lang.org/install/ (or https://github.com/leanprover/elan), then rerun." >&2
    exit 1
  fi
fi
cd TsigmaProof
echo "[$(date +%T)] Lean toolchain: $(cat lean-toolchain)"
lake exe cache get
echo "[$(date +%T)] building the proof"
lake build
echo "[$(date +%T)] axioms behind the main theorems:"
lake env lean AxiomReport.lean
