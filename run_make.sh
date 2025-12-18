#!/bin/bash
# Build script for TAPL Rocq Project

set -e  # Exit on error

echo "==> Cleaning previous builds..."
make cleanall 2>/dev/null || true

echo "==> Generating CoqMakefile..."
rocq makefile -f _CoqProject -o CoqMakefile

echo "==> Building the project..."
make

echo "==> Build completed successfully!"