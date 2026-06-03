import Mathlib.Tactic.NormNum.LegendreSymbol

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/GroupTheory/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete group-theoretic support

Derived-series and basic group-theoretic lemmas used by the finite-index constructions.
-/

namespace FenchelNielsen

def IsTorsionFreeGroup (G : Type*) [Group G] : Prop :=
  ∀ g : G, IsOfFinOrder g → g = 1

def IsPerfectGroup (G : Type*) [Group G] : Prop :=
  derivedSeries G 1 = ⊤

theorem isTorsionFreeGroup_of_mulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hTF : IsTorsionFreeGroup G) :
    IsTorsionFreeGroup H := by
  intro h hfin
  have hpre :
      e.symm h = 1 :=
    hTF (e.symm h) (MonoidHom.isOfFinOrder e.symm.toMonoidHom hfin)
  simpa using congrArg e hpre

theorem orderOf_map_eq_of_torsionFree_ker
    {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hker : IsTorsionFreeGroup φ.ker) {x : G} (hx : IsOfFinOrder x) :
    orderOf (φ x) = orderOf x := by
  apply Nat.dvd_antisymm
  · exact orderOf_map_dvd φ x
  · have hpowMap : φ (x ^ orderOf (φ x)) = 1 := by
      rw [map_pow, pow_orderOf_eq_one]
    let k : φ.ker := ⟨x ^ orderOf (φ x), hpowMap⟩
    have hkfin : IsOfFinOrder k := by
      have hxpow : IsOfFinOrder (x ^ orderOf (φ x)) := hx.pow
      simpa [k] using
        (Submonoid.isOfFinOrder_coe
          (H := φ.ker.toSubmonoid) (x := k)).1 hxpow
    have hkone : k = 1 := hker k hkfin
    have hxpowOne : x ^ orderOf (φ x) = 1 := by
      simpa [k] using congrArg Subtype.val hkone
    exact orderOf_dvd_of_pow_eq_one hxpowOne

end FenchelNielsen
