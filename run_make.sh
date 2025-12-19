#!/bin/bash
# Distributed build script for TAPL Rocq Project
# Each subdirectory maintains its own _CoqProject

set -e

# Define build order (respecting dependencies)
# Props and Tactics have no dependencies
# plf has no dependencies (builds PLF modules)
# src depends on Props, Tactics, and plf
MODULES=("Props" "Tactics" "plf" "src")

echo "==> Building TAPL Rocq Project (distributed mode)"
echo ""

# Function to build a single module
build_module() {
    local module=$1
    echo "===> Building module: $module"
    
    cd "$module"
    
    # Check if _CoqProject exists
    if [ ! -f _CoqProject ]; then
        echo "     WARNING: No _CoqProject found in $module, skipping..."
        cd ..
        return
    fi
    
    # Generate or update Makefile
    if [ ! -f Makefile ] || [ _CoqProject -nt Makefile ]; then
        echo "     Generating Makefile from _CoqProject..."
        rocq makefile -f _CoqProject -o Makefile
    else
        echo "     Makefile is up to date"
    fi
    
    # Build with parallel jobs
    echo "     Compiling..."
    make -j$(nproc) -f Makefile
    
    cd ..
    echo "     ✓ $module build complete"
    echo ""
}

# Build each module in order
for module in "${MODULES[@]}"; do
    if [ -d "$module" ]; then
        build_module "$module"
    else
        echo "     WARNING: Directory $module not found, skipping..."
        echo ""
    fi
done

echo "==> All modules built successfully!"