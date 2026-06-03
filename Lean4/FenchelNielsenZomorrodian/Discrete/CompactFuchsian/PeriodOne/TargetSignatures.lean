import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.FirstReduction.Signatures

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/PeriodOne/TargetSignatures.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Period-one cleanup step

Handles the cleanup of period-one target entries using quotient maps, kernel equivalences, low-cardinality dihedral cases, source subgroups, and relator proofs.
-/

open scoped BigOperators
namespace FenchelNielsen

noncomputable def doublePeriodOneTailReplicatedSignature
    {tailLen p : ℕ} (tail : Fin tailLen → ℕ)
    (htail : ∀ j, 2 ≤ tail j) (hHigh : 3 ≤ p * tailLen) :
    FuchsianSignature where
  orbitGenus := 0
  numCusps := 0
  numPeriods := p * tailLen
  periods := fun i => tail ((finProdFinEquiv.symm i).2)
  period_ge_two := by
    intro i
    exact htail ((finProdFinEquiv.symm i).2)
  numCusps_eq_zero := rfl
  numPeriods_ge_three := hHigh

theorem doublePeriodOneTailReplicatedSignature_lcmCondition
    {tailLen p : ℕ} (tail : Fin tailLen → ℕ)
    (htail : ∀ j, 2 ≤ tail j) (hHigh : 3 ≤ p * tailLen) :
    2 ≤ p →
    LCMCondition
      (doublePeriodOneTailReplicatedSignature tail htail hHigh).toFenchelSignature := by
  classical
  intro hp
  change LCMConditionFamily
    (fun i : Fin (p * tailLen) => tail ((finProdFinEquiv.symm i).2))
  apply lcmConditionFamily_of_hasEqualPartnerFamily
  intro i
  let kj : Fin p × Fin tailLen := finProdFinEquiv.symm i
  refine ⟨finProdFinEquiv (finPartner hp kj.1, kj.2), ?_, ?_⟩
  · intro h
    have hi : i = finProdFinEquiv kj := by
      dsimp [kj]
      exact (finProdFinEquiv.apply_symm_apply i).symm
    have hpair := finProdFinEquiv.injective (h.trans hi)
    exact finPartner_ne hp kj.1 (congrArg Prod.fst hpair)
  · simp only [finProdFinEquiv_symm_apply, Equiv.symm_apply_apply, kj]

abbrev OneHeadPeriodOneTargetIndex (tailLen p : ℕ) :=
  Sum (Fin 1) (Fin p × Fin tailLen)

def oneHeadPeriodOneTargetOrderedIndexEquiv (tailLen p : ℕ) :
    OneHeadPeriodOneTargetIndex tailLen p ≃ Fin (1 + p * tailLen) :=
  (Equiv.sumCongr (Equiv.refl (Fin 1))
      (finProdFinEquiv : Fin p × Fin tailLen ≃ Fin (p * tailLen))).trans
    finSumFinEquiv

def oneHeadPeriodOneTargetPeriods
    {tailLen p : ℕ} (m₂' : ℕ) (tail : Fin tailLen → ℕ) :
    OneHeadPeriodOneTargetIndex tailLen p → ℕ
  | .inl _ => m₂'
  | .inr kj => tail kj.2

noncomputable def oneHeadPeriodOneTargetSignature
    {tailLen p : ℕ} (m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₂' : 2 ≤ m₂') (htail : ∀ j, 2 ≤ tail j)
    (hTailLen : 0 < tailLen) : FuchsianSignature where
  orbitGenus := 0
  numCusps := 0
  numPeriods := 1 + p * tailLen
  periods := fun i =>
    oneHeadPeriodOneTargetPeriods (p := p) m₂' tail
      ((oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p).symm i)
  period_ge_two := by
    intro i
    cases h :
      (oneHeadPeriodOneTargetOrderedIndexEquiv tailLen p).symm i with
    | inl head =>
        fin_cases head
        exact hm₂'
    | inr kj =>
        exact htail kj.2
  numCusps_eq_zero := rfl
  numPeriods_ge_three := by
    have htailOne : 1 ≤ tailLen := Nat.succ_le_of_lt hTailLen
    have hprod : 2 ≤ p * tailLen := by
      exact Nat.mul_le_mul hp htailOne
    omega

end FenchelNielsen
