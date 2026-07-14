# Yamaguchi Lean4 Library

This ZIP is a Lake project generated from the Lean sources used by the website.
The source tree follows the same shape as the working Lean project: Lake files at
the project root, and Lean source modules under `Lean4/`.

## Documentation

The generated YamaLean4Lib documentation is available at:

https://n-yamaguchi-0729.github.io/YamaLean4Lib_pages/

## Build

For a fresh checkout or extracted ZIP:

```bash
lake exe cache get
lake build
```

If dependency download was interrupted, remove `.lake/` and run:

```bash
lake update
lake exe cache get
lake build
```

## Package Information

- Generated at: 2026-07-14T19:32:09+09:00
- Package: YamaguchiLean4Library
- Lean toolchain: `leanprover/lean4:v4.27.0`
- Mathlib ref: `v4.27.0`
- Locked dependencies: included
- Lean source files: 673
- Importable modules: 673
- Source repository: https://github.com/n-yamaguchi-0729/YamaLean4Lib
- Source ref: main


## Top-Level Libraries

- `CompletedGroupAlgebra`
- `CrowellExactSequence`
- `FenchelNielsenZomorrodian`
- `FoxDifferential`
- `ProCGroups`
- `ReidemeisterSchreier`
- `Yama2026_Sections_1_And_2_1`

## Use

```lean
import CompletedGroupAlgebra
```

The project root module is:

```lean
import YamaguchiLean4Library
```
