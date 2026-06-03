import ProCGroups.ProC.GroupPredicate

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/MaximalQuotients/Definitions.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open Set

namespace ProCGroups.ProC

universe u

section

variable {ProC : ProCGroupPredicate}

/-- Maximal pro-`C` quotient groups via their universal property. -/
structure IsMaximalProCQuotient
    (ProC : ProCGroupPredicate)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (π : G →* Q) : Prop where
  isProC : ProC (G := Q)
  continuous_π : Continuous π
  surjective_π : Function.Surjective π
  existsUnique_lift :
    ∀ {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H],
      ProC (G := H) →
      ∀ (φ : G →* H), Continuous φ →
        ∃! φbar : Q →* H, Continuous φbar ∧ φbar.comp π = φ

end

end ProCGroups.ProC
