#!/usr/bin/env bash
set -euo pipefail
lake build ReportProof
lake env lean ReportProof.lean
