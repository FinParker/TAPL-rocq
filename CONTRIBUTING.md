# Contributing to TAPL in Rocq

Thank you for your interest in improving this project!

## Best Practices & Recommendations

### 1. Continuous Integration (CI)
We recommend setting up **GitHub Actions** to:
- automatically build the project on every push to ensure no proofs are broken.
- automatically deploy the documentation to GitHub Pages, so you don't need to manually commit the `docs/` folder.

### 2. Dependency Management
Consider adding an `opam` file to the root of the project to explicitly list dependencies (Coq version, plugins, etc.). This makes it easier for others to set up the environment.

### 3. Build System
While `make` is standard, the modern ecosystem is moving towards **Dune**. Migrating to Dune can offer better incremental builds and editor integration.

### 4. Code Style
- Keep proofs readable. Use bullet points (`-`, `+`, `*`) for structure.
- Use `Admitted` only for temporary placeholders, never in final code.

### 5. Documentation
- Ensure every new definition has a comment explaining it.
- Run `./run_make.sh` locally to verify the documentation generation before submitting.
