import FenchelNielsenZomorrodian.Discrete.Core.CompactFuchsianPresentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Core/FamilySignature.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete Fenchel and compact Fuchsian core definitions

Signatures, generator indices, presentations, elliptic generators, quotient homomorphisms, and family-signature transformations.
-/

namespace FenchelNielsen

noncomputable def familyFuchsianSignature
    {ι : Type*} [Fintype ι]
    (periods : ι → ℕ) (hperiods : ∀ i, 2 ≤ periods i)
    (hcard : 3 ≤ Fintype.card ι) :
    FuchsianSignature where
  orbitGenus := 0
  numCusps := 0
  numPeriods := Fintype.card ι
  periods := fun i => periods ((Fintype.equivFin ι).symm i)
  period_ge_two := by
    intro i
    simpa using hperiods ((Fintype.equivFin ι).symm i)
  numCusps_eq_zero := rfl
  numPeriods_ge_three := hcard

@[simp] theorem familyFuchsianSignature_periods
    {ι : Type*} [Fintype ι]
    (periods : ι → ℕ) (hperiods : ∀ i, 2 ≤ periods i)
    (hcard : 3 ≤ Fintype.card ι) (i : ι) :
    (familyFuchsianSignature periods hperiods hcard).periods
        (Fintype.equivFin ι i) = periods i := by
  simp only [familyFuchsianSignature, Equiv.symm_apply_apply]

theorem familyFuchsianSignature_lcmCondition_of_lcmConditionFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (periods : ι → ℕ) (hperiods : ∀ i, 2 ≤ periods i)
    (hcard : 3 ≤ Fintype.card ι)
    (hLCM : LCMConditionFamily periods) :
    LCMCondition (familyFuchsianSignature periods hperiods hcard).toFenchelSignature := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  change LCMConditionFamily (familyFuchsianSignature periods hperiods hcard).periods
  intro i
  have hi : periods (e i) ∣ otherPeriodsLcmFamily periods (e i) := hLCM (e i)
  have hOtherDiv :
      otherPeriodsLcmFamily periods (e i) ∣
        otherPeriodsLcmFamily
          (familyFuchsianSignature periods hperiods hcard).periods i := by
    rw [otherPeriodsLcmFamily]
    apply Finset.lcm_dvd
    intro j hj
    let j' : Fin (Fintype.card ι) := e.symm j
    have hjNe : j ≠ e i := (Finset.mem_erase.mp hj).1
    have hj'Mem :
        j' ∈ (Finset.univ.erase i : Finset (Fin (Fintype.card ι))) := by
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ j'⟩
      intro hji
      apply hjNe
      have h := congrArg e hji
      simpa [j', e] using h
    have hdiv :=
      Finset.dvd_lcm
        (s := Finset.univ.erase i)
        (f := (familyFuchsianSignature periods hperiods hcard).periods)
        hj'Mem
    simpa [familyFuchsianSignature, j', e] using hdiv
  simpa [familyFuchsianSignature, e] using hi.trans hOtherDiv

end FenchelNielsen
