# TAPL Rocq 项目构建说明

## 项目结构

本项目采用**分布式 `_CoqProject` 管理方式**，每个子模块维护自己的 `_CoqProject` 配置：

```
TAPL-rocq/
├── Props/
│   ├── _CoqProject       # 配置: -Q . TAPL.Props
│   └── RelationProp.v
├── Tactics/
│   ├── _CoqProject       # 配置: -Q . TAPL.Tactics
│   ├── Tactics.v
│   └── Examples.v
├── src/
│   ├── _CoqProject       # 配置: -Q . TAPL
│   ├── UntypedArithExpr.v
│   ├── ArithExpr.v
│   └── Stlc.v
└── plf/
    ├── _CoqProject       # 配置: -Q . PLF
    └── *.v files
```

## 构建脚本

### 构建项目
```bash
./run_make.sh
```

此脚本会按照依赖顺序构建各个模块：
1. Props（基础属性定义）
2. Tactics（策略库）
3. plf（编程语言基础）
4. src（核心TAPL实现，依赖前三者）

### 清理项目
```bash
./clean_all.sh
```

清理所有模块的编译产物和生成的Makefile。

## 模块依赖关系

- **Props**: 无依赖，定义基础关系属性
- **Tactics**: 无依赖，提供证明策略
- **plf**: 无依赖，编程语言基础模块
- **src**: 依赖 Props、Tactics、plf

## VSCode/VSCoq 配置

`.vscode/settings.json` 已配置为自动识别各子目录的 `_CoqProject` 文件。
每个目录的 Coq 文件会使用其所在目录的 `_CoqProject` 配置。

## 手动构建单个模块

如需单独构建某个模块：

```bash
cd src  # 或其他模块目录
rocq makefile -f _CoqProject -o Makefile
make -j$(nproc)
```

## 添加新文件

1. 在对应子目录创建 `.v` 文件
2. 将文件名添加到该目录的 `_CoqProject` 中
3. 运行 `./run_make.sh`

## 注意事项

- 根目录的 `_CoqProject` 仅作为全局配置参考，实际构建使用各子目录配置
- 修改任何 `_CoqProject` 后，对应的 Makefile 会自动重新生成
- 并行编译使用所有可用CPU核心 (`nproc`)
