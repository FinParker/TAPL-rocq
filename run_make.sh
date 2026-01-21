#!/bin/bash
# Distributed build script for TAPL Rocq Project
# Each subdirectory maintains its own _CoqProject

set -e

# Define build order (respecting dependencies)
# Props and Tactics have no dependencies
# plf has no dependencies (builds PLF modules)
# src depends on Props, Tactics, and plf
MODULES=("Props" "Tactics" "plf" "src")
DOC_ROOT="$(pwd)/docs"
STYLE_SOURCE="$(pwd)/common"

# Determine Coq executable (rocq or coq)
if command -v rocq >/dev/null 2>&1; then
    COQMAKEFILE="rocq makefile"
    echo "==> Using Rocq toolchain"
else
    COQMAKEFILE="coq_makefile"
    echo "==> Using Coq toolchain"
fi

echo "==> Building TAPL Rocq Project and Documentation"
echo ""
mkdir -p "$DOC_ROOT"

# Copy common style files from project common to docs/common
if [ -d "$STYLE_SOURCE" ]; then
    echo "===> Copying style files from common to docs/common"
    mkdir -p "$DOC_ROOT"
    rm -rf "$DOC_ROOT/common"
    cp -r "$STYLE_SOURCE" "$DOC_ROOT/common"
    echo "     ✓ Style files copied"
    echo ""
fi

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
        $COQMAKEFILE -f _CoqProject -o Makefile
    else
        echo "     Makefile is up to date"
    fi
    
    # Build with parallel jobs
    echo "     Compiling..."
    make -j$(nproc) -f Makefile
    
    echo "     ✓ $module build complete"
    echo ""

    # Generate documentation
    echo "     Generating coqdoc..."
    mkdir -p "$DOC_ROOT/$module"
    
    make html COQDOCFLAGS="--utf8"
    
    if [ -d "html" ]; then
        cp -r html/* "$DOC_ROOT/$module/"
        
        # Update CSS links to use new tapl.css style
        if [ -f "$DOC_ROOT/$module/coqdoc.css" ]; then
            # Create a custom CSS file that imports our unified style
            cat > "$DOC_ROOT/$module/coqdoc.css" << 'EOF'
@import url('../common/css/tapl.css');
EOF
        fi
        
        # Update HTML files to reference common styles
        for html_file in "$DOC_ROOT/$module"/*.html; do
            if [ -f "$html_file" ]; then
                # Add link to common styles in HTML head
                sed -i '/<head>/a <link href="../common/css/tapl.css" rel="stylesheet" type="text/css" />' "$html_file"
            fi
        done

        # Replace the unreadable Global Index (index.html) with the Table of Contents (toc.html)
        if [ -f "$DOC_ROOT/$module/toc.html" ]; then
            echo "     ✓ Replacing Global Index with Table of Contents for readability"
            cp "$DOC_ROOT/$module/toc.html" "$DOC_ROOT/$module/index.html"
            # Optional: Update title in the new index.html
            sed -i 's/<title>Table of contents<\/title>/<title>Module Index<\/title>/' "$DOC_ROOT/$module/index.html"
        fi
        
        echo "     ✓ Documentation for $module available at docs/$module/index.html"
    fi
    
    cd ..
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

echo "==> All modules and docs built successfully!"