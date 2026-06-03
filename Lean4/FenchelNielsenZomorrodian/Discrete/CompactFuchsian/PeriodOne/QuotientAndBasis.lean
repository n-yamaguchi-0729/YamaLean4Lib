import FenchelNielsenZomorrodian.Discrete.Core.EllipticCompact
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.FirstReduction.QuotientAndBasis

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/PeriodOne/QuotientAndBasis.lean
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

theorem originalFirstReduction_canonical_periods_eq
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (x : OriginalFirstReductionIndex tailLen) :
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    source.periods ((originalFirstReductionOrderedIndexEquiv tailLen) x) =
      originalFirstReductionPeriods (p := p) m₁' m₂' tail x := by
  classical
  dsimp
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  cases x using Sum.casesOn with
  | inl i =>
      fin_cases i <;>
        simp only [originalFirstReductionSignature, Fin.mk_zero, Fin.mk_one, Fin.isValue,
  originalFirstReductionOrderedIndexEquiv, Fin.val_eq_zero_iff, Equiv.coe_fn_mk, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
  originalFirstReductionSignaturePeriod, one_ne_zero, ↓reduceDIte, originalFirstReductionPeriods, twoPeriods,
  Nat.reduceAdd, fin_cases_const_one, Fin.cases_zero]
  | inr j =>
      simp only [originalFirstReductionSignature, originalFirstReductionOrderedIndexEquiv_right,
  originalFirstReductionSignaturePeriod_tail, originalFirstReductionPeriods]

theorem originalFirstReduction_source_totalRelation_eq
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let e := originalFirstReductionOrderedIndexEquiv tailLen
    totalRelation source =
      xWord source (e (.inl (0 : Fin 2))) *
        xWord source (e (.inl (1 : Fin 2))) *
          (List.ofFn (fun j : Fin tailLen =>
            xWord source (e (.inr j)))).prod := by
  classical
  dsimp
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let e := originalFirstReductionOrderedIndexEquiv tailLen
  change totalRelation source =
      xWord source (e (.inl (0 : Fin 2))) *
        xWord source (e (.inl (1 : Fin 2))) *
          (List.ofFn (fun j : Fin tailLen => xWord source (e (.inr j)))).prod
  have hOneFin : (1 : Fin (2 + tailLen)) = ⟨1, by omega⟩ := by
    apply Fin.ext
    simp only [Fin.coe_ofNat_eq_mod]
    rw [Nat.mod_eq_of_lt (by omega : 1 < 2 + tailLen)]
  rw [totalRelation]
  simpa [source, e, originalFirstReductionSignature, List.ofFn_eq_map,
    List.prod_cons, mul_assoc, hOneFin] using
      congrArg List.prod
        (list_ofFn_two_add (fun i : Fin (2 + tailLen) => xWord source i))

noncomputable def originalFirstReductionPeriodOneQuotientImage
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    (let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
     Fin source.numPeriods → Multiplicative (ZMod p)) :=
  fun i =>
    match e.symm i with
    | .inl h => twoPeriods (Multiplicative.ofAdd (1 : ZMod p))
        (Multiplicative.ofAdd (-1 : ZMod p)) h
    | .inr _ => 1

theorem originalFirstReductionPeriodOneQuotientImage_pow
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (hperiods :
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ x : OriginalFirstReductionIndex tailLen,
        source.periods (e x) =
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x) :
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∀ i : Fin source.numPeriods,
      originalFirstReductionPeriodOneQuotientImage
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e i ^
        source.periods i = 1 := by
  classical
  dsimp
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  intro i
  let x : OriginalFirstReductionIndex tailLen := e.symm i
  have hi : i = e x := by
    simp only [Equiv.apply_symm_apply, x]
  rw [hi]
  cases x using Sum.casesOn with
  | inl h =>
      rw [hperiods (.inl h)]
      fin_cases h
      · apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
        simp only [originalFirstReductionPeriodOneQuotientImage, Fin.zero_eta, Fin.isValue, Equiv.symm_apply_apply,
  twoPeriods, Nat.reduceAdd, ofAdd_neg, Fin.cases_zero, originalFirstReductionPeriods, toAdd_pow, toAdd_ofAdd,
  nsmul_eq_mul, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, mul_one, toAdd_one]
      · apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
        simp only [originalFirstReductionPeriodOneQuotientImage, Fin.mk_one, Fin.isValue, Equiv.symm_apply_apply,
  twoPeriods, Nat.reduceAdd, ofAdd_neg, fin_cases_const_one, originalFirstReductionPeriods, inv_pow, toAdd_inv,
  toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, Nat.cast_mul, CharP.cast_eq_zero, zero_mul, mul_one, neg_zero, toAdd_one]
  | inr j =>
      rw [hperiods (.inr j)]
      simp only [originalFirstReductionPeriodOneQuotientImage, Equiv.symm_apply_apply, one_pow]

theorem originalFirstReductionPeriodOneQuotientImage_prod
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∏ i : Fin source.numPeriods,
      originalFirstReductionPeriodOneQuotientImage
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e i = 1 := by
  classical
  dsimp
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  rw [← Equiv.prod_comp e]
  simp only [OriginalFirstReductionIndex, originalFirstReductionPeriodOneQuotientImage, Equiv.symm_apply_apply,
  ofAdd_neg, Fintype.prod_sum_type, Fin.prod_univ_two, Fin.isValue, twoPeriods_zero, twoPeriods_one, mul_inv_cancel,
  Finset.prod_const_one, mul_one]

noncomputable def originalFirstReductionPeriodOneFreeQuotientHom
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    FreeGroup (FuchsianGenerator source) →* Multiplicative (ZMod p) := by
  classical
  dsimp
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  exact
    FreeGroup.lift
      (ellipticQuotientGeneratorImage source
        (originalFirstReductionPeriodOneQuotientImage
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e))

theorem originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (hperiods :
      let source :=
        originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
      ∀ x : OriginalFirstReductionIndex tailLen,
        source.periods (e x) =
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x) :
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    ∀ r ∈ relators source,
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e r = 1 := by
  classical
  dsimp
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  simpa [originalFirstReductionPeriodOneFreeQuotientHom, source] using
    ellipticQuotientGeneratorImage_respects_relators source
      (originalFirstReductionPeriodOneQuotientImage
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e)
      (originalFirstReductionPeriodOneQuotientImage_pow
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods)
      (originalFirstReductionPeriodOneQuotientImage_prod
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e)

theorem originalFirstReductionPeriodOneFreeQuotientHom_head_zero
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
        (FreeGroup.of (FuchsianGenerator.elliptic (e (.inl (0 : Fin 2))))) =
      Multiplicative.ofAdd (1 : ZMod p) := by
  classical
  dsimp
  simp only [originalFirstReductionPeriodOneFreeQuotientHom, Lean.Elab.WF.paramLet, id_eq, Fin.isValue,
  FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage, originalFirstReductionPeriodOneQuotientImage,
  Equiv.symm_apply_apply, ofAdd_neg, twoPeriods_zero]

theorem originalFirstReductionPeriodOneFreeQuotientHom_head_one
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
        (FreeGroup.of (FuchsianGenerator.elliptic (e (.inl (1 : Fin 2))))) =
      Multiplicative.ofAdd (-1 : ZMod p) := by
  classical
  dsimp
  simp only [originalFirstReductionPeriodOneFreeQuotientHom, Lean.Elab.WF.paramLet, id_eq, Fin.isValue,
  FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage, originalFirstReductionPeriodOneQuotientImage,
  Equiv.symm_apply_apply, twoPeriods, Nat.reduceAdd, ofAdd_neg, fin_cases_const_one]

theorem originalFirstReductionPeriodOneFreeQuotientHom_tail
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (j : Fin tailLen) :
    originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
        (FreeGroup.of (FuchsianGenerator.elliptic (e (.inr j)))) = 1 := by
  classical
  dsimp
  simp only [originalFirstReductionPeriodOneFreeQuotientHom, Lean.Elab.WF.paramLet, id_eq,
  FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage, originalFirstReductionPeriodOneQuotientImage,
  Equiv.symm_apply_apply]

noncomputable def originalFirstReductionPeriodOneDistinguishedGenerator
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    FuchsianGenerator source := by
  classical
  dsimp
  exact FuchsianGenerator.elliptic (e (.inl (0 : Fin 2)))

noncomputable def originalFirstReductionPeriodOneSchreierTransversal
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    Set (FreeGroup (FuchsianGenerator source)) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  exact Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))

theorem originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    IsRightSchreierTransversal φ.ker
      (originalFirstReductionPeriodOneSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e) := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  simpa [originalFirstReductionPeriodOneSchreierTransversal, source, φ, x] using
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx

noncomputable def originalFirstReductionPeriodOneSchreierBasisEquiv
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  exact freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx

@[simp 900] theorem originalFirstReductionPeriodOneSchreierBasisEquiv_symm_apply
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let hT :=
      originalFirstReductionPeriodOneSchreierTransversal_isRightSchreierTransversal
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    ∀ z : ↥(schreierGeneratorSet hT),
      (originalFirstReductionPeriodOneSchreierBasisEquiv
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e).symm (z : φ.ker) =
        (FreeGroup.of z)⁻¹ := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  letI : DecidableEq (FuchsianGenerator source) := Classical.decEq _
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  intro z
  let basis :=
    originalFirstReductionPeriodOneSchreierBasisEquiv
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  apply basis.injective
  simp only [originalFirstReductionPeriodOneSchreierTransversal, Lean.Elab.WF.paramLet, id_eq,
  originalFirstReductionPeriodOneSchreierBasisEquiv, MulEquiv.apply_symm_apply, map_inv,
  freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator_of φ x hx z, inv_inv, basis, φ, x]

noncomputable def originalFirstReductionPeriodOneFirstPowerKernel
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    φ.ker := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  refine ⟨(FreeGroup.of x) ^ p, ?_⟩
  rw [MonoidHom.mem_ker]
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  rw [map_pow, hx]
  apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
  simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]

noncomputable def originalFirstReductionPeriodOneSecondEdgeKernelElement
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    φ.ker := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  let r : ℕ := ((k.val : ZMod p) - 1).val
  refine ⟨(FreeGroup.of x) ^ k.val * FreeGroup.of y * ((FreeGroup.of x) ^ r)⁻¹, ?_⟩
  rw [MonoidHom.mem_ker]
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
    simpa [φ, y] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_one
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
  apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
  simp only [ofAdd_neg, toAdd_mul, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, toAdd_inv, ZMod.natCast_val,
  dvd_refl, ZMod.cast_sub, ZMod.cast_natCast, ZMod.cast_one, neg_sub, toAdd_one, r]
  ring

noncomputable def originalFirstReductionPeriodOneTailKernelElement
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    φ.ker := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inr j))
  refine ⟨(FreeGroup.of x) ^ k.val * FreeGroup.of y * ((FreeGroup.of x) ^ k.val)⁻¹, ?_⟩
  rw [MonoidHom.mem_ker]
  have hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simpa [φ, x, originalFirstReductionPeriodOneDistinguishedGenerator] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_zero
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  have hy : φ (FreeGroup.of y) = 1 := by
    simpa [φ, y] using
      originalFirstReductionPeriodOneFreeQuotientHom_tail
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j
  change φ ((FreeGroup.of x) ^ k.val * FreeGroup.of y * ((FreeGroup.of x) ^ k.val)⁻¹) = 1
  simp only [Lean.Elab.WF.paramLet, map_mul, map_pow, hx, hy, mul_one, map_inv, mul_inv_cancel]

noncomputable def originalFirstReductionPeriodOneSecondPowerKernel
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    φ.ker := by
  classical
  dsimp
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  refine ⟨(FreeGroup.of y) ^ p, ?_⟩
  rw [MonoidHom.mem_ker]
  have hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod p) := by
    simpa [φ, y] using
      originalFirstReductionPeriodOneFreeQuotientHom_head_one
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  rw [map_pow, hy]
  apply (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p).injective
  simp only [ofAdd_neg, inv_pow, toAdd_inv, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one,
  neg_zero, toAdd_one]

theorem originalFirstReductionPeriodOneFirstPowerKernel_coe
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let x : FuchsianGenerator source :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    ((originalFirstReductionPeriodOneFirstPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e : φ.ker) :
          FreeGroup (FuchsianGenerator source)) =
      (FreeGroup.of x) ^ p := by
  classical
  dsimp
  simp only [originalFirstReductionPeriodOneFirstPowerKernel, Lean.Elab.WF.paramLet,
  originalFirstReductionPeriodOneDistinguishedGenerator, Fin.isValue, id_eq]

theorem originalFirstReductionPeriodOneSecondPowerKernel_coe
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
    ((originalFirstReductionPeriodOneSecondPowerKernel
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e : φ.ker) :
          FreeGroup (FuchsianGenerator source)) =
      (FreeGroup.of y) ^ p := by
  classical
  dsimp
  simp only [originalFirstReductionPeriodOneSecondPowerKernel, Lean.Elab.WF.paramLet, Fin.isValue, id_eq]

theorem originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let x : FuchsianGenerator source :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
    let r : ℕ := ((k.val : ZMod p) - 1).val
    ((originalFirstReductionPeriodOneSecondEdgeKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k : φ.ker) :
          FreeGroup (FuchsianGenerator source)) =
      (FreeGroup.of x) ^ k.val * FreeGroup.of y * ((FreeGroup.of x) ^ r)⁻¹ := by
  classical
  dsimp
  simp only [originalFirstReductionPeriodOneSecondEdgeKernelElement, Lean.Elab.WF.paramLet,
  originalFirstReductionPeriodOneDistinguishedGenerator, Fin.isValue, id_eq]

theorem originalFirstReductionPeriodOneTailKernelElement_coe
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    (j : Fin tailLen) (k : Fin p) :
    letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    let φ :=
      originalFirstReductionPeriodOneFreeQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let x : FuchsianGenerator source :=
      originalFirstReductionPeriodOneDistinguishedGenerator
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
    let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inr j))
    ((originalFirstReductionPeriodOneTailKernelElement
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j k : φ.ker) :
          FreeGroup (FuchsianGenerator source)) =
      (FreeGroup.of x) ^ k.val * FreeGroup.of y * ((FreeGroup.of x) ^ k.val)⁻¹ := by
  classical
  dsimp
  simp only [originalFirstReductionPeriodOneTailKernelElement, Lean.Elab.WF.paramLet,
  originalFirstReductionPeriodOneDistinguishedGenerator, Fin.isValue, id_eq]

theorem originalFirstReductionPeriodOneSecondEdgeKernelElement_inj
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    {k₁ k₂ : Fin p}
    (hEq :
      originalFirstReductionPeriodOneSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k₁ =
        originalFirstReductionPeriodOneSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k₂) :
    k₁ = k₂ := by
  classical
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let y : FuchsianGenerator source := FuchsianGenerator.elliptic (e (.inl (1 : Fin 2)))
  have hval := congrArg
    (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) hEq
  let r₁ : ℕ := ((k₁.val : ZMod p) - 1).val
  let r₂ : ℕ := ((k₂.val : ZMod p) - 1).val
  have hleft :
      ((originalFirstReductionPeriodOneSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k₁ : φ.ker) :
            FreeGroup (FuchsianGenerator source)) =
        (FreeGroup.of x) ^ k₁.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ r₁)⁻¹ := by
    simpa [source, φ, x, y, r₁] using
      originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k₁
  have hright :
      ((originalFirstReductionPeriodOneSecondEdgeKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k₂ : φ.ker) :
            FreeGroup (FuchsianGenerator source)) =
        (FreeGroup.of x) ^ k₂.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ r₂)⁻¹ := by
    simpa [source, φ, x, y, r₂] using
      originalFirstReductionPeriodOneSecondEdgeKernelElement_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e k₂
  have hword :
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₁.val * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ r₁)⁻¹ =
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₂.val * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ r₂)⁻¹ := by
    simpa [hleft, hright] using hval
  have hxne : x ≠ y := by
    intro hEq'
    simp only [originalFirstReductionPeriodOneDistinguishedGenerator, Lean.Elab.WF.paramLet, Fin.isValue, id_eq,
  FuchsianGenerator.elliptic.injEq, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, zero_ne_one, x, y] at hEq'
  exact Fin.ext
    (freeGroup_pow_mul_of_mul_pow_inv_left_exponent_eq_of_eq hxne hword)

theorem originalFirstReductionPeriodOneTailKernelElement_inj
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (e :
      OriginalFirstReductionIndex tailLen ≃
        Fin (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail
          hTailLen).numPeriods)
    {j₁ j₂ : Fin tailLen} {k₁ k₂ : Fin p}
    (hEq :
      originalFirstReductionPeriodOneTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j₁ k₁ =
        originalFirstReductionPeriodOneTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j₂ k₂) :
    j₁ = j₂ ∧ k₁ = k₂ := by
  classical
  letI : NeZero p := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hp)⟩
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let φ :=
    originalFirstReductionPeriodOneFreeQuotientHom
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let x : FuchsianGenerator source :=
    originalFirstReductionPeriodOneDistinguishedGenerator
      m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e
  let tailGen : Fin tailLen → FuchsianGenerator source := fun j =>
    FuchsianGenerator.elliptic (e (.inr j))
  have hval := congrArg
    (fun z : φ.ker => (z : FreeGroup (FuchsianGenerator source))) hEq
  have hleft :
      ((originalFirstReductionPeriodOneTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j₁ k₁ : φ.ker) :
            FreeGroup (FuchsianGenerator source)) =
        (FreeGroup.of x) ^ k₁.val * FreeGroup.of (tailGen j₁) *
          ((FreeGroup.of x) ^ k₁.val)⁻¹ := by
    simpa [source, φ, x, tailGen] using
      originalFirstReductionPeriodOneTailKernelElement_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j₁ k₁
  have hright :
      ((originalFirstReductionPeriodOneTailKernelElement
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j₂ k₂ : φ.ker) :
            FreeGroup (FuchsianGenerator source)) =
        (FreeGroup.of x) ^ k₂.val * FreeGroup.of (tailGen j₂) *
          ((FreeGroup.of x) ^ k₂.val)⁻¹ := by
    simpa [source, φ, x, tailGen] using
      originalFirstReductionPeriodOneTailKernelElement_coe
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e j₂ k₂
  have hword :
      (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₁.val *
          FreeGroup.of (tailGen j₁) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₁.val)⁻¹ =
        (FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₂.val *
          FreeGroup.of (tailGen j₂) *
          ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₂.val)⁻¹ := by
    simpa [hleft, hright] using hval
  have hxne₁ : x ≠ tailGen j₁ := by
    intro hEq'
    simp only [originalFirstReductionPeriodOneDistinguishedGenerator, Lean.Elab.WF.paramLet, Fin.isValue, id_eq,
  FuchsianGenerator.elliptic.injEq, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, x, tailGen] at hEq'
  have hxne₂ : x ≠ tailGen j₂ := by
    intro hEq'
    simp only [originalFirstReductionPeriodOneDistinguishedGenerator, Lean.Elab.WF.paramLet, Fin.isValue, id_eq,
  FuchsianGenerator.elliptic.injEq, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, x, tailGen] at hEq'
  have hlen := congrArg
    (fun w : FreeGroup (FuchsianGenerator source) => (FreeGroup.toWord w).length) hword
  change
    (FreeGroup.toWord
      ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₁.val *
        FreeGroup.of (tailGen j₁) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₁.val)⁻¹)).length =
    (FreeGroup.toWord
      ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₂.val *
        FreeGroup.of (tailGen j₂) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₂.val)⁻¹)).length at hlen
  rw [freeGroup_toWord_pow_mul_of_mul_pow_inv hxne₁ k₁.val k₁.val,
    freeGroup_toWord_pow_mul_of_mul_pow_inv hxne₂ k₂.val k₂.val] at hlen
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.length_append, List.length_replicate,
  List.length_cons] at hlen
  have hk : k₁ = k₂ := by
    ext
    omega
  subst k₂
  have hwords := congrArg
    (fun w : FreeGroup (FuchsianGenerator source) => FreeGroup.toWord w) hword
  change
    FreeGroup.toWord
      ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₁.val *
        FreeGroup.of (tailGen j₁) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₁.val)⁻¹) =
    FreeGroup.toWord
      ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₁.val *
        FreeGroup.of (tailGen j₂) *
        ((FreeGroup.of x : FreeGroup (FuchsianGenerator source)) ^ k₁.val)⁻¹) at hwords
  rw [freeGroup_toWord_pow_mul_of_mul_pow_inv hxne₁ k₁.val k₁.val,
    freeGroup_toWord_pow_mul_of_mul_pow_inv hxne₂ k₁.val k₁.val] at hwords
  have hdrop := congrArg
    (fun L : List (FuchsianGenerator source × Bool) => L.drop k₁.val) hwords
  have hhead := congrArg List.head? hdrop
  have htailGenEq : tailGen j₁ = tailGen j₂ := by
    simpa using hhead
  have hj : j₁ = j₂ := by
    have hidx : (e (.inr j₁) : Fin source.numPeriods) = e (.inr j₂) := by
      have hidx' :=
        congrArg
          (fun g : FuchsianGenerator source =>
            match g with
            | .elliptic i => i
            | .surfaceA _ => e (.inr j₁)
            | .surfaceB _ => e (.inr j₁))
          htailGenEq
      change (e (.inr j₁) : Fin source.numPeriods) = e (.inr j₂) at hidx'
      exact hidx'
    exact Sum.inr.inj (e.injective hidx)
  exact ⟨hj, rfl⟩

noncomputable def originalFirstReductionPeriodOneQuotientHom
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    FuchsianPresentedGroup
        (originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen) →*
      Multiplicative (ZMod p) := by
  classical
  let source :=
    originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
  let e : OriginalFirstReductionIndex tailLen ≃ Fin source.numPeriods := by
    simpa [source, originalFirstReductionSignature] using
    originalFirstReductionOrderedIndexEquiv tailLen
  have hperiods :
      ∀ x : OriginalFirstReductionIndex tailLen,
        source.periods (e x) =
          originalFirstReductionPeriods (p := p) m₁' m₂' tail x := by
    intro x
    simpa [source, e] using
      originalFirstReduction_canonical_periods_eq
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen x
  exact
    PresentedGroup.toGroup (rels := relators source)
      (f := ellipticQuotientGeneratorImage source
        (originalFirstReductionPeriodOneQuotientImage
          m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e))
      (by
        simpa [originalFirstReductionPeriodOneFreeQuotientHom, source] using
          originalFirstReductionPeriodOneFreeQuotientHom_respects_relators
            m₁' m₂' tail hp hm₁' hm₂' htail hTailLen e hperiods)

theorem originalFirstReductionPeriodOneQuotientHom_head_zero
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    originalFirstReductionPeriodOneQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (ellipticElement source
          ((originalFirstReductionOrderedIndexEquiv tailLen) (.inl (0 : Fin 2)))) =
      Multiplicative.ofAdd (1 : ZMod p) := by
  classical
  dsimp
  simp only [originalFirstReductionSignature, originalFirstReductionPeriodOneQuotientHom, id_eq,
  ellipticElement, PresentedGroup.toGroup.of, ellipticQuotientGeneratorImage,
  originalFirstReductionPeriodOneQuotientImage, originalFirstReductionOrderedIndexEquiv_symm_zero, Fin.isValue,
  ofAdd_neg, twoPeriods_zero]

theorem originalFirstReductionPeriodOneQuotientHom_head_one
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen) :
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    originalFirstReductionPeriodOneQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (ellipticElement source
          ((originalFirstReductionOrderedIndexEquiv tailLen) (.inl (1 : Fin 2)))) =
      Multiplicative.ofAdd (-1 : ZMod p) := by
  classical
  dsimp
  simp only [originalFirstReductionSignature, originalFirstReductionPeriodOneQuotientHom, id_eq,
  ellipticElement, Fin.isValue, originalFirstReductionOrderedIndexEquiv_left_one, PresentedGroup.toGroup.of,
  ellipticQuotientGeneratorImage, originalFirstReductionPeriodOneQuotientImage,
  originalFirstReductionOrderedIndexEquiv_symm_one, twoPeriods, Nat.reduceAdd, ofAdd_neg, fin_cases_const_one]

theorem originalFirstReductionPeriodOneQuotientHom_tail
    {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hm₁' : 0 < m₁') (hm₂' : 0 < m₂')
    (htail : ∀ j, 2 ≤ tail j) (hTailLen : 0 < tailLen)
    (j : Fin tailLen) :
    let source :=
      originalFirstReductionSignature m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
    originalFirstReductionPeriodOneQuotientHom
        m₁' m₂' tail hp hm₁' hm₂' htail hTailLen
        (ellipticElement source
          ((originalFirstReductionOrderedIndexEquiv tailLen) (.inr j))) =
      1 := by
  classical
  dsimp
  simp only [originalFirstReductionSignature, originalFirstReductionPeriodOneQuotientHom, id_eq,
  ellipticElement, PresentedGroup.toGroup.of, ellipticQuotientGeneratorImage,
  originalFirstReductionPeriodOneQuotientImage, originalFirstReductionOrderedIndexEquiv_symm_right]

end FenchelNielsen
