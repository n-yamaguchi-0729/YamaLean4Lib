import CrowellExactSequence.Profinite.FiniteRank
import CrowellExactSequence.Profinite.MainTheorem

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite Crowell exact sequence over pro-C integer coefficients

This is the profinite public entry point.  It exposes the finite-coordinate Blanchfield--Lyndon
maps, the completed Crowell exactness route, and the paper sequence

```text
N^ab(C) -> A_psi(C) -> Z_C[[H]] -> Z_C
```

and its finite-basis Blanchfield--Lyndon coordinate expression through
`CrowellExactSequence.Profinite.MainTheorem`.
-/
