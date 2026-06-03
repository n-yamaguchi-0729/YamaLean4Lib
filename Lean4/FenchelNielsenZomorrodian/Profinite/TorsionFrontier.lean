import FenchelNielsenZomorrodian.Profinite.FGroup
import ProCGroups.Generation.WordProductsAndClosure

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Profinite/TorsionFrontier.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite finite-subgroup torsion frontier

Isolates the remaining profinite torsion-classification frontier:
finite subgroups of a profinite Fenchel group are conjugate into inertia.
-/

namespace FenchelNielsen

universe u

namespace ProfiniteFGroup

/-- A subgroup is contained in a conjugate of one inertia group, up to powers. -/
def finiteSubgroupLeConjInertia
    (Δ : ProfiniteFGroup.{u}) (K : Subgroup Δ.carrier) : Prop :=
  ∃ i : Fin Δ.signature.numPeriods, ∃ c : Δ.carrier,
    ∀ k : K, ∃ n : ℤ,
      (k : Δ.carrier) = c * Δ.inertia i ^ n * c⁻¹

/- FRONTIER `profinite-fgroup-torsion-theorem`.

This is the profinite torsion theorem allowed by the user: finite subgroups of
a profinite F-group are controlled by the stack inertia groups.  It is kept
separate from the discrete Fuchsian torsion frontier.
-/
/-- Finite nontrivial profinite `F`-subgroups lie in conjugates of inertia groups. -/
axiom finiteSubgroup_le_conj_inertia
    (Δ : ProfiniteFGroup.{u})
    (K : Subgroup Δ.carrier) [Finite K]
    (hK : K ≠ ⊥) :
    Δ.finiteSubgroupLeConjInertia K

/-- A nontrivial finite-order element is conjugate to a power of an inertia element. -/
theorem finiteOrder_isConj_inertia_zpow_of_ne_one
    (Δ : ProfiniteFGroup.{u}) (g : Δ.carrier)
    (hg : IsOfFinOrder g) (hgne : g ≠ 1) :
    ∃ i : Fin Δ.signature.numPeriods, ∃ n : ℤ,
      IsConj g (Δ.inertia i ^ n) := by
  classical
  let K : Subgroup Δ.carrier := Subgroup.zpowers g
  letI : Fintype K := Fintype.ofEquiv (Fin (orderOf g)) (finEquivZPowers hg)
  letI : Finite K := Finite.of_fintype K
  have hKne : K ≠ ⊥ := by
    intro hK
    have hgmem : g ∈ K := Subgroup.mem_zpowers g
    have hgbot : g ∈ (⊥ : Subgroup Δ.carrier) := by
      simpa [K, hK] using hgmem
    exact hgne (Subgroup.mem_bot.mp hgbot)
  rcases finiteSubgroup_le_conj_inertia Δ K hKne with
    ⟨i, c, hcontain⟩
  rcases hcontain ⟨g, Subgroup.mem_zpowers g⟩ with ⟨n, hn⟩
  exact ⟨i, n, (isConj_iff.2 ⟨c, hn.symm⟩).symm⟩

/-- An open normal subgroup avoids the nontrivial profinite inertia powers. -/
def avoidsNontrivialInertia
    (Δ : ProfiniteFGroup.{u}) (U : OpenNormalSubgroup Δ.carrier) : Prop :=
  ∀ i : Fin Δ.signature.numPeriods, ∀ n : ℤ,
    Δ.inertia i ^ n ∈ (U : Subgroup Δ.carrier) →
      Δ.inertia i ^ n = 1

/-- Avoiding nontrivial inertia powers makes an open normal subgroup torsion-free. -/
theorem torsionFree_of_avoidsNontrivialInertia
    (Δ : ProfiniteFGroup.{u}) (U : OpenNormalSubgroup Δ.carrier)
    (hAvoid : Δ.avoidsNontrivialInertia U) :
    ProfiniteOpenNormalSubgroupTorsionFree Δ.carrier U := by
  intro x hx hxfin
  by_cases hx1 : x = 1
  · exact hx1
  · rcases finiteOrder_isConj_inertia_zpow_of_ne_one Δ x hxfin hx1 with
      ⟨i, n, hconj⟩
    have hinU : Δ.inertia i ^ n ∈ (U : Subgroup Δ.carrier) := by
      rcases isConj_iff.1 hconj with ⟨c, hc⟩
      rw [← hc]
      exact U.isNormal'.conj_mem x hx c
    have hpow1 : Δ.inertia i ^ n = 1 := hAvoid i n hinU
    exact isConj_one_left.mp (by simpa [hpow1] using hconj)

/-- There is an open normal subgroup avoiding all nontrivial inertia powers. -/
theorem exists_openNormal_avoidsNontrivialInertia
    (Δ : ProfiniteFGroup.{u}) :
    ∃ U : OpenNormalSubgroup Δ.carrier,
      Δ.avoidsNontrivialInertia U := by
  classical
  have hEach :
      ∀ i : Fin Δ.signature.numPeriods,
        ∃ U : OpenNormalSubgroup Δ.carrier,
          ((U : Subgroup Δ.carrier) ⊓
              Subgroup.zpowers (Δ.inertia i)) = ⊥ := by
    intro i
    let K : Subgroup Δ.carrier := Subgroup.zpowers (Δ.inertia i)
    have hfinord : IsOfFinOrder (Δ.inertia i) := by
      rw [← orderOf_pos_iff]
      rw [Δ.inertia_order i]
      exact lt_of_lt_of_le (by decide : 0 < 2) (Δ.signature.period_ge_two i)
    letI : Fintype K :=
      Fintype.ofEquiv (Fin (orderOf (Δ.inertia i)))
        (finEquivZPowers hfinord)
    letI : Finite K := Finite.of_fintype K
    exact
      ProCGroups.Generation.exists_openNormalSubgroup_inf_eq_bot_of_finite
        (G := Δ.carrier) Δ.isProfinite K
  choose U hU using hEach
  by_cases hnonempty :
      (Finset.univ : Finset (Fin Δ.signature.numPeriods)).Nonempty
  · let V : OpenNormalSubgroup Δ.carrier :=
      (Finset.univ : Finset (Fin Δ.signature.numPeriods)).inf' hnonempty U
    refine ⟨V, ?_⟩
    intro i n hn
    have hVle : V ≤ U i := by
      dsimp [V]
      exact Finset.inf'_le
        (s := (Finset.univ : Finset (Fin Δ.signature.numPeriods)))
        (f := U) (b := i) (by simp only [Finset.mem_univ])
    have hmemU : Δ.inertia i ^ n ∈ (U i : Subgroup Δ.carrier) :=
      hVle hn
    have hmemZ : Δ.inertia i ^ n ∈ Subgroup.zpowers (Δ.inertia i) :=
      Subgroup.mem_zpowers_iff.2 ⟨n, rfl⟩
    have hbot :
        Δ.inertia i ^ n ∈ (⊥ : Subgroup Δ.carrier) := by
      have hInf :
          Δ.inertia i ^ n ∈
            ((U i : Subgroup Δ.carrier) ⊓
              Subgroup.zpowers (Δ.inertia i)) :=
        ⟨hmemU, hmemZ⟩
      simpa [hU i] using hInf
    exact Subgroup.mem_bot.mp hbot
  · refine ⟨⊤, ?_⟩
    intro i
    exact False.elim (hnonempty ⟨i, by simp only [Finset.mem_univ]⟩)

/-- Every profinite `F`-group has a torsion-free open normal subgroup. -/
theorem exists_torsionFreeOpenNormalSubgroup
    (Δ : ProfiniteFGroup.{u}) :
    ∃ U : OpenNormalSubgroup Δ.carrier,
      ProfiniteOpenNormalSubgroupTorsionFree Δ.carrier U := by
  rcases exists_openNormal_avoidsNontrivialInertia Δ with ⟨U, hU⟩
  exact ⟨U, torsionFree_of_avoidsNontrivialInertia Δ U hU⟩

end ProfiniteFGroup

end FenchelNielsen
