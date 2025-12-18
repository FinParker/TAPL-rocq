#!/bin/bash
# Build script for TAPL Rocq Project with Caching support

set -e

# 1. 只有当 CoqMakefile 不存在，或者 _CoqProject 比它新时，才重新生成
if [ ! -f CoqMakefile ] || [ _CoqProject -nt CoqMakefile ]; then
    echo "==> _CoqProject changed or CoqMakefile missing. Updating..."
    rocq makefile -f _CoqProject -o CoqMakefile
else
    echo "==> CoqMakefile is up to date."
fi

# 2. 直接运行 make。
# CoqMakefile 内部会处理依赖关系（.CoqMakefile.d），只编译改变的文件。
echo "==> Building the project (incremental)..."

# 使用全部 CPU 核心进行并行编译
make -j$(nproc) -f CoqMakefile

echo "==> Build finished!"