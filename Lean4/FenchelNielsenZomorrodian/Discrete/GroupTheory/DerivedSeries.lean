import FenchelNielsenZomorrodian.Discrete.GroupTheory.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/GroupTheory/DerivedSeries.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete group-theoretic support

Derived-series and basic group-theoretic lemmas used by the finite-index constructions.
-/

namespace FenchelNielsen

universe u v

theorem derivedSeries_one_eq_bot_of_commGroup
    (G : Type*) [CommGroup G] :
    derivedSeries G 1 = ⊥ := by
  rw [derivedSeries_one]
  rw [commutator_eq_bot_iff_center_eq_top, CommGroup.center_eq_top]

theorem derivedSeries_succ_le_map_derivedSeries_of_firstDerived_le
    {G : Type*} [Group G] (H : Subgroup G) (hH : derivedSeries G 1 ≤ H) :
    ∀ n : ℕ, derivedSeries G (n + 1) ≤ (derivedSeries H n).map H.subtype := by
  intro n
  induction n with
  | zero =>
      have hRange : H ≤ H.subtype.range := by
        simp only [H.range_subtype, le_refl]
      simpa [derivedSeries_zero, MonoidHom.range_eq_map] using hH.trans hRange
  | succ n ih =>
      calc
        derivedSeries G (n + 1 + 1) = ⁅derivedSeries G (n + 1), derivedSeries G (n + 1)⁆ := by
          rw [derivedSeries_succ]
        _ ≤ ⁅(derivedSeries H n).map H.subtype, (derivedSeries H n).map H.subtype⁆ :=
          Subgroup.commutator_mono ih ih
        _ = (derivedSeries H (n + 1)).map H.subtype := by
          rw [derivedSeries_succ, Subgroup.map_commutator]

theorem derivedSeries_map_surjective
    {G : Type*} {H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) :
    ∀ m : ℕ, Subgroup.map f (derivedSeries G m) = derivedSeries H m := by
  intro m
  induction m with
  | zero =>
      ext y
      constructor
      · intro _hy
        trivial
      · intro _hy
        rcases hf y with ⟨x, rfl⟩
        exact ⟨x, trivial, rfl⟩
  | succ m ih =>
      rw [derivedSeries_succ, derivedSeries_succ, Subgroup.map_commutator, ih]

theorem derivedSeries_ulift_eq_bot_of
    {G : Type v} [Group G] {m : ℕ}
    (h : derivedSeries G m = ⊥) :
    derivedSeries (ULift.{u, v} G) m = ⊥ := by
  let e : ULift.{u, v} G ≃* G := MulEquiv.ulift
  have hmap :
      Subgroup.map e.toMonoidHom (derivedSeries (ULift.{u, v} G) m) =
        (⊥ : Subgroup G) := by
    rw [derivedSeries_map_surjective e.toMonoidHom e.surjective m, h]
  apply le_antisymm
  · intro x hx
    have hxmap :
        e.toMonoidHom x ∈
          Subgroup.map e.toMonoidHom (derivedSeries (ULift.{u, v} G) m) :=
      ⟨x, hx, rfl⟩
    rw [hmap] at hxmap
    exact Subgroup.mem_bot.mpr
      (e.injective (Subgroup.mem_bot.mp hxmap))
  · exact bot_le

end FenchelNielsen
