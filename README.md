# TAPL-rocq

Types and Programming Languages in Rocq (formerly Coq)

## Requirements

- [Rocq Prover 9.0.0](https://rocq-prover.org/docs/using-opam)
- OCaml 4.14.0 or later (installed with Rocq)

```sh
opam switch create TAPL-rocq --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
opam switch TAPL-rocq
opam repo add rocq-released https://rocq-prover.org/opam/released
opam pin add rocq-prover 9.0.0
```

Recommand to use VsRocq Extension.
(Please use rocq-language-server 2.3.3 or later)

## Setup

Ensure Rocq environment is loaded:

```sh
eval $(opam env) # Very Important!!
rocq --version  # Verify installation
```

## Building the Project

### Option A: Quick Build (Recommended)

```sh
./run_make.sh
```

This script will:
1. Clean previous builds
2. Generate CoqMakefile
3. Build all files

### Option B: Manual Build

**Step 1: Generate CoqMakefile**

```sh
rocq makefile -f _CoqProject -o CoqMakefile
```

**Step 2: Build**

```sh
make           # Build all files
make all       # Same as above
```

**Step 3: Clean**

```sh
make clean     # Remove compiled files
make cleanall  # Remove all generated files including CoqMakefile
```

**Step 4: Compile Single File**

```sh
make <file>.vo  # e.g., make plf/Maps.vo
# or
rocq compile -R . TAPL <file>.v
```

## Project Structure

```
TAPL-rocq/
├── _CoqProject          # Project configuration
├── Makefile             # Build system wrapper
├── CoqMakefile.local    # Custom build extensions
├── run_make.sh          # Quick build script
├── src/                 # Source files
│   ├── UntypedArithExpr.v
│   └── ArithExpr.v
├── plf/                 # Programming Language Foundations
│   └── Maps.v
├── Props/               # Properties
│   └── RelationProp.v
└── Tactics/             # Custom tactics
    └── Tactics.v
```

## VS Code / VsRocq Setup

### Prerequisites
Ensure VsRocq extension is installed in VS Code

### Launching VS Code with Correct Environment

**Option 1: Use the launch script (Recommended)**
```sh
./launch_vscode.sh
```

**Option 2: Manual launch**
```sh
eval $(opam env)
code .
```

### Debugging VsRocq Issues

If `.v` files are not recognized or highlighted:

1. **Run the debug script:**
   ```sh
   ./debug_vsrocq.sh
   ```

2. **Check VS Code Output:**
   - Open: `View` → `Output`
   - Select: `VsRocq` from dropdown
   - Look for error messages

3. **Common Issues:**
   - ❌ **VsRocq not starting**: Restart VS Code after running `eval $(opam env)`
   - ❌ **Files not recognized**: Check `.vscode/settings.json` has correct `vsrocq.path`
   - ❌ **No syntax highlighting**: Ensure `files.associations` includes `"*.v": "rocq"`

4. **Enable verbose logging:**
   - Already enabled in `.vscode/settings.json`
   - Check Output panel for detailed logs

5. **Verify configuration:**
   ```sh
   # Check vsrocqtop is accessible
   which vsrocqtop
   
   # Test manually
   vsrocqtop --version
   ```

### VS Code Configuration Files

- `.vscode/settings.json` - VsRocq configuration
- `.vscode/tasks.json` - Build tasks
- `.vscode/extensions.json` - Recommended extensions

## Notes

- This project uses Rocq 9.0.0 (the rebranded version of Coq)
- The `-R` flag in `_CoqProject` allows flexible module loading
- All files use the `TAPL` logical root namespace
- VS Code must be launched with opam environment loaded for VsRocq to work