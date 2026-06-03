import ReidemeisterSchreier.Discrete.OpenSubgroups.ClassicalGeneratorBasis

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Singerman/ReidemeisterSchreier.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Singerman/Reidemeister-Schreier bridge

Cyclic quotient actions, cyclic product identities, Schreier kernel computations, free-group word
identities, and kernel transport for the compact Fuchsian proof.
-/

namespace FenchelNielsen
export ReidemeisterSchreier.Discrete.OpenSubgroups (
  IsRightSchreierTransversal
  schreierGenerator
  schreierGeneratorSet
  schreierGeneratorInverseBasisEquiv
  schreierGeneratorInverseBasisEquiv_of
  schreierGenerator_eq_one_of_mem
  schreierRepresentative
  schreierRepresentative_eq_of_mem_mul_inv_mem
  schreierRepresentative_eq_one_of_mem
)
end FenchelNielsen
