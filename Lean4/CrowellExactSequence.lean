import CrowellExactSequence.FiniteFamilyExactness
import CrowellExactSequence.Discrete.MainTheorem
import CrowellExactSequence.Profinite.MainTheorem

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Crowell exact sequences

Public entry point for the discrete and profinite Crowell exact sequence libraries.  This root
imports the shared finite-family exactness layer and the focused discrete and profinite main
theorem entry points directly. General Fox calculus has been factored out to the independent
`FoxDifferential` library.
-/
