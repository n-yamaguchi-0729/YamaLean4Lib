import FenchelNielsenZomorrodian.Discrete.Torsion.FuchsianFiniteSubgroupFrontier

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Torsion/CompactFiniteOrder.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete finite-order torsion frontier

Compact finite-order lemmas and the remaining finite-subgroup theorem for Fuchsian orbifold groups.
-/

namespace FenchelNielsen

theorem finiteOrder_isConj_elliptic_zpow_of_ne_one
    (σ : FuchsianSignature) (g : FuchsianPresentedGroup σ)
    (hg : IsOfFinOrder g) (hgne : g ≠ 1) :
    ∃ i : Fin σ.numPeriods, ∃ n : ℤ,
      IsConj g (ellipticElement σ i ^ n) := by
  exact
    finiteOrder_isConj_elliptic_zpow_of_frontier (ellipticElement σ)
      (fun K hKfinite hKne => by
        haveI : Finite K := hKfinite
        exact finiteSubgroup_le_conj_ellipticStabilizer σ K hKne)
      g hg hgne

theorem finiteOrder_eq_one_or_isConj_elliptic_zpow
    (σ : FuchsianSignature) (g : FuchsianPresentedGroup σ)
    (hg : IsOfFinOrder g) :
    g = 1 ∨ ∃ i : Fin σ.numPeriods, ∃ n : ℤ,
      IsConj g (ellipticElement σ i ^ n) := by
  exact
    finiteOrder_eq_one_or_isConj_elliptic_zpow_of_frontier (ellipticElement σ)
      (fun K hKfinite hKne => by
        haveI : Finite K := hKfinite
        exact finiteSubgroup_le_conj_ellipticStabilizer σ K hKne)
      g hg

end FenchelNielsen
