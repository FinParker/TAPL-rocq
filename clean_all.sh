#!/bin/bash
# Clean all generated files in distributed build structure

set -e

MODULES=("Props" "Tactics" "src" "plf")

echo "==> Cleaning TAPL Rocq Project (distributed mode)"
echo ""

clean_module() {
    local module=$1
    echo "===> Cleaning module: $module"
    
    cd "$module"
    
    if [ -f Makefile ]; then
        make cleanall -f Makefile 2>/dev/null || true
        rm -f Makefile Makefile.conf .Makefile.d
    fi
    
    # Clean auxiliary files
    rm -f *.vo *.vok *.vos *.glob *.aux .*.aux
    rm -rf .coq-native .lia.cache .nia.cache
    
    cd ..
    echo "     ✓ $module cleaned"
    echo ""
}

# Clean each module
for module in "${MODULES[@]}"; do
    if [ -d "$module" ]; then
        clean_module "$module"
    fi
done

# Clean root directory generated files
rm -f CoqMakefile CoqMakefile.conf .CoqMakefile.d

echo "==> Clean complete!"
