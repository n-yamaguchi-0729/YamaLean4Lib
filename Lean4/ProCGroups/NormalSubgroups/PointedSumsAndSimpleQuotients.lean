import ProCGroups.NormalSubgroups.Framework

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/NormalSubgroups/PointedSumsAndSimpleQuotients.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Closed normal subgroups and simple quotients

Develops normal-subgroup frameworks, maximal intersections, simple quotient ranks, compactness arguments, and algebraic comparison theorems.
-/

namespace ProCGroups.NormalSubgroups

universe u

/-- Input data recording a closed normal closure that is free of the expected stabilized rank. -/
structure NormalClosureFreeInputData
    (C : ProCGroups.FiniteGroupClass.{u})
    (F : Type u) [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (S : Set F) (m : Cardinal) : Type (u + 1) where
  normalClosure : Subgroup F
  isClosedNormalClosure : IsClosedNormalClosure S normalClosure
  isFree : ProCGroups.FreeProC.IsFreeProCGroupOfClassRank C normalClosure (m ⊔ ℵ₀)

end ProCGroups.NormalSubgroups
