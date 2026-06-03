import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.SecondReduction.TransportMaps

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/SecondReduction/Relators/Target.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Second compact zero-genus reduction

The second explicit reduction step, with ordered target signatures, transport maps, source and target relator calculations, and quotient-basis comparison.
-/

namespace FenchelNielsen

theorem secondReductionCanonicalTransportToSchreierHom_positiveDistinguished
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩
    let A :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    θ A =
      e.symm
        (secondReductionCanonicalFirstPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx :=
    secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩
  let A :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  simp only [secondReductionCanonicalTransportToSchreierHom, xWord,
  secondReductionCanonicalTransportDistinguishedIndex, Fin.isValue, Fin.zero_eta, FreeGroup.lift_apply_of,
  secondReductionCanonicalTransportToSchreierGeneratorImage, secondReductionCanonicalTransportToSchreierGenerator,
  Lean.Elab.WF.paramLet, Fin.val_eq_zero_iff, dite_eq_ite, Equiv.symm_apply_apply, id_eq, ↓reduceIte,
  secondReductionCanonicalFirstPowerKernel]
theorem secondReductionCanonicalTransportToSchreierHom_negativeDistinguished
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨1, by decide⟩
    let B :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    θ B =
      e.symm
        (secondReductionCanonicalSecondPowerKernel
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx :=
    secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨1, by decide⟩
  let B :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  simp only [secondReductionCanonicalTransportToSchreierHom, xWord,
  secondReductionCanonicalTransportDistinguishedIndex, Fin.isValue, Fin.zero_eta, FreeGroup.lift_apply_of,
  secondReductionCanonicalTransportToSchreierGeneratorImage, secondReductionCanonicalTransportToSchreierGenerator,
  Lean.Elab.WF.paramLet, Fin.val_eq_zero_iff, dite_eq_ite, Equiv.symm_apply_apply, id_eq, one_ne_zero, ↓reduceIte,
  secondReductionCanonicalSecondPowerKernel]
theorem secondReductionCanonicalTransportToSchreierHom_headZero
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k
    let C :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    θ C =
      e.symm
        (secondReductionCanonicalHeadZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx :=
    secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k
  let C :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  simp only [secondReductionCanonicalTransportToSchreierHom, xWord, secondReductionCanonicalTransportHeadIndex,
  Fin.isValue, id_eq, FreeGroup.lift_apply_of, secondReductionCanonicalTransportToSchreierGeneratorImage,
  secondReductionCanonicalTransportToSchreierGenerator, Lean.Elab.WF.paramLet, Fin.val_eq_zero_iff, dite_eq_ite,
  Equiv.symm_apply_apply, ↓reduceIte, secondReductionCanonicalHeadZeroKernelElement,
  secondReductionCanonicalZeroImageKernelElement]
theorem secondReductionCanonicalTransportToSchreierHom_headOne
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k
    let C :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    θ C =
      e.symm
        (secondReductionCanonicalHeadOneKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx :=
    secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k
  let C :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  simp only [secondReductionCanonicalTransportToSchreierHom, xWord, secondReductionCanonicalTransportHeadIndex,
  Fin.isValue, id_eq, FreeGroup.lift_apply_of, secondReductionCanonicalTransportToSchreierGeneratorImage,
  secondReductionCanonicalTransportToSchreierGenerator, Lean.Elab.WF.paramLet, Fin.val_eq_zero_iff, dite_eq_ite,
  Equiv.symm_apply_apply, one_ne_zero, ↓reduceIte, secondReductionCanonicalHeadOneKernelElement,
  secondReductionCanonicalZeroImageKernelElement]
theorem secondReductionCanonicalTransportToSchreierHom_middleRest
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (r : Fin (p - 2)) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k
    let C :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    θ C =
      e.symm
        (secondReductionCanonicalMiddleRestZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail r k) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx :=
    secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k
  let C :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  simp only [secondReductionCanonicalTransportToSchreierHom, xWord,
  secondReductionCanonicalTransportMiddleRestIndex, id_eq, FreeGroup.lift_apply_of,
  secondReductionCanonicalTransportToSchreierGeneratorImage, secondReductionCanonicalTransportToSchreierGenerator,
  Lean.Elab.WF.paramLet, Fin.val_eq_zero_iff, Fin.isValue, dite_eq_ite, Equiv.symm_apply_apply,
  secondReductionCanonicalMiddleRestZeroKernelElement, secondReductionCanonicalZeroImageKernelElement]
theorem secondReductionCanonicalTransportToSchreierHom_tail
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (b : Fin p) (j : Fin tailLen) (k : Fin q) :
    letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    let σ :=
      secondReductionCanonicalSourceSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
    let e :=
      secondReductionCanonicalSchreierBasisEquiv
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let θ :=
      secondReductionCanonicalTransportToSchreierHom
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    let idx :=
      secondReductionCanonicalTransportTailIndex tailLen p q b j k
    let C :=
      xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
    θ C =
      e.symm
        (secondReductionCanonicalTailZeroKernelElement
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail b j k) := by
  classical
  dsimp
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
  let σ :=
    secondReductionCanonicalSourceSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  letI : DecidableEq (FuchsianGenerator σ) := Classical.decEq _
  let e :=
    secondReductionCanonicalSchreierBasisEquiv
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let θ :=
    secondReductionCanonicalTransportToSchreierHom
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let idx :=
    secondReductionCanonicalTransportTailIndex tailLen p q b j k
  let C :=
    xWord τ ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q)) idx)
  simp only [secondReductionCanonicalTransportToSchreierHom, xWord, secondReductionCanonicalTransportTailIndex,
  id_eq, FreeGroup.lift_apply_of, secondReductionCanonicalTransportToSchreierGeneratorImage,
  secondReductionCanonicalTransportToSchreierGenerator, Lean.Elab.WF.paramLet, Fin.val_eq_zero_iff, Fin.isValue,
  dite_eq_ite, Equiv.symm_apply_apply, secondReductionCanonicalTailZeroKernelElement,
  secondReductionCanonicalZeroImageKernelElement]
noncomputable def secondReductionCanonicalTransportZeroBlockWord
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    Fin q → FreeGroup (FuchsianGenerator τ) := by
  classical
  dsimp
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let targetWord :=
    secondReductionCanonicalTransportTargetWord (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  intro k
  exact
    (List.ofFn (fun r : Fin (p - 2) =>
      targetWord (secondReductionCanonicalTransportMiddleRestIndex tailLen p q r k))).prod *
      (List.ofFn (fun b : Fin p =>
        (List.ofFn (fun j : Fin tailLen =>
          targetWord (secondReductionCanonicalTransportTailIndex tailLen p q b j k))).prod)).prod *
        targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨0, by decide⟩ k) *
        targetWord (secondReductionCanonicalTransportHeadIndex tailLen p q ⟨1, by decide⟩ k)
noncomputable def secondReductionCanonicalTransportBlockTotalWord
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    FreeGroup (FuchsianGenerator τ) := by
  classical
  dsimp
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let A :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨0, by decide⟩))
  let B :=
    xWord τ
      ((Fintype.equivFin (SecondReductionTransportIndex tailLen p q))
        (secondReductionCanonicalTransportDistinguishedIndex tailLen p q ⟨1, by decide⟩))
  let C :=
    (List.ofFn (fun k : Fin q =>
      secondReductionCanonicalTransportZeroBlockWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail k)).prod
  exact A * B * C
noncomputable def secondReductionCanonicalTransportBlockRelators
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let τ :=
      secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
    Set (FreeGroup (FuchsianGenerator τ)) := by
  classical
  dsimp
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  exact
    {r | (∃ i : Fin τ.numPeriods, r = (xWord τ i) ^ τ.periods i) ∨
      r =
        secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail}
theorem secondReductionCanonicalTransport_powerRelator_mem_blockRelators
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j)
    (i : Fin
      (secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail).numPeriods) :
    (xWord
        (secondReductionTransportSignature (p := p) hq
          m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail) i) ^
      (secondReductionTransportSignature (p := p) hq
        m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail).periods i ∈
      secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail := by
  classical
  left
  exact ⟨i, rfl⟩
theorem secondReductionCanonicalTransport_blockTotalWord_mem_blockRelators
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail ∈
      secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
        m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail := by
  classical
  right
  rfl
private theorem secondReductionCanonicalTransportBlockTotalWord_map_orderedTarget
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    let υ :=
      secondReductionCanonicalOrderedTargetSignature
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
    FreeGroup.freeGroupCongr
        (secondReductionCanonicalTransportGeneratorEquivOrderedTarget
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail)
        (secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) =
      totalRelation υ := by
  classical
  dsimp
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let υ :=
    secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let eGen :=
    secondReductionCanonicalTransportGeneratorEquivOrderedTarget
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hTotal :
      totalRelation υ =
        xWord υ
            (secondReductionCanonicalOrderedTargetDistinguishedIndex tailLen p q
              ⟨0, by decide⟩) *
          xWord υ
            (secondReductionCanonicalOrderedTargetDistinguishedIndex tailLen p q
              ⟨1, by decide⟩) *
          (List.ofFn (fun k : Fin q =>
            secondReductionCanonicalOrderedTargetZeroBlockWord
              m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k)).prod := by
    simpa [υ] using
      secondReductionCanonicalOrderedTarget_totalRelation_eq_blocks
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  have hZero :
      ∀ k : Fin q,
        secondReductionCanonicalOrderedTargetZeroBlockWord
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k =
          (List.ofFn (fun r : Fin (p - 2) =>
            xWord υ (secondReductionCanonicalOrderedTargetMiddleRestIndex tailLen p q r k))).prod *
            (List.ofFn (fun b : Fin p =>
              (List.ofFn (fun j : Fin tailLen =>
                xWord υ
                  (secondReductionCanonicalOrderedTargetTailIndex tailLen p q b j k))).prod)).prod *
            xWord υ
              (secondReductionCanonicalOrderedTargetHeadIndex tailLen p q ⟨0, by decide⟩ k) *
            xWord υ
              (secondReductionCanonicalOrderedTargetHeadIndex tailLen p q ⟨1, by decide⟩ k) := by
    intro k
    simpa [υ] using
      secondReductionCanonicalOrderedTargetZeroBlockWord_eq_nested
        m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail k
  rw [hTotal]
  simp only [secondReductionCanonicalTransportGeneratorEquivOrderedTarget, Equiv.coe_fn_mk,
  secondReductionCanonicalTransportBlockTotalWord, Lean.Elab.WF.paramLet, xWord, Fin.zero_eta, Fin.isValue,
  Fin.mk_one, secondReductionCanonicalTransportZeroBlockWord, secondReductionCanonicalTransportTargetWord, id_eq,
  mul_assoc, map_mul, FreeGroup.map.of, secondReductionCanonicalTransportFinEquivOrderedTargetFin_apply,
  secondReductionTransportIndexEquivCanonicalOrderedTargetFin_distinguished, map_list_prod, List.map_ofFn,
  Function.comp_def, secondReductionTransportIndexEquivCanonicalOrderedTargetFin_middleRest,
  secondReductionTransportIndexEquivCanonicalOrderedTargetFin_tail,
  secondReductionTransportIndexEquivCanonicalOrderedTargetFin_head, hZero, υ]
noncomputable def secondReductionCanonicalTransportBlockRelatorsEquivOrderedTarget
    {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hm₁' : 2 ≤ m₁') (hm₂' : 2 ≤ m₂') (hm₃' : 2 ≤ m₃')
    (htail : ∀ j, 2 ≤ tail j) :
    PresentedGroup
        (secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
          m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) ≃*
      FuchsianPresentedGroup
        (secondReductionCanonicalOrderedTargetSignature
          m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail) := by
  classical
  let τ :=
    secondReductionTransportSignature (p := p) hq
      m₁' m₂' m₃' tail hm₁' hm₂' hm₃' htail
  let υ :=
    secondReductionCanonicalOrderedTargetSignature
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let eFin :=
    secondReductionCanonicalTransportFinEquivOrderedTargetFin
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let eGen :=
    secondReductionCanonicalTransportGeneratorEquivOrderedTarget
      m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
  let eFG : FreeGroup (FuchsianGenerator τ) ≃*
      FreeGroup (FuchsianGenerator υ) :=
    FreeGroup.freeGroupCongr eGen
  let R : Set (FreeGroup (FuchsianGenerator τ)) :=
    secondReductionCanonicalTransportBlockRelators (p := p) (q := q)
      m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail
  let S : Set (FreeGroup (FuchsianGenerator υ)) := relators υ
  refine
    ReidemeisterSchreier.Discrete.Presentations.quotientEquivOfRelatorQuotientMutualMapData R S
      (ReidemeisterSchreier.Discrete.Presentations.relatorQuotientMutualMapDataOfRelatorImagesMemNormalClosure eFG R S ?_ ?_)
  · intro r hr
    change
        ((∃ i : Fin τ.numPeriods, r = (xWord τ i) ^ τ.periods i) ∨
          r =
            secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
              m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) at hr
    rcases hr with ⟨i, rfl⟩ | htotal
    · have hperiod :
          τ.periods i = υ.periods (eFin i) := by
        simpa [τ, υ, eFin] using
          secondReductionCanonicalTransportOrdered_period
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i
      have hx :
          eFG (xWord τ i) = xWord υ (eFin i) := by
        simpa [τ, υ, eFin, eGen, eFG] using
          secondReductionCanonicalTransportOrdered_xWord
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i
      have hrel :
          eFG ((xWord τ i) ^ τ.periods i) =
            (xWord υ (eFin i)) ^ υ.periods (eFin i) := by
        rw [map_pow, hx, hperiod]
      rw [hrel]
      exact Subgroup.subset_normalClosure (Or.inl ⟨eFin i, rfl⟩)
    · rw [htotal]
      have htotalMap :
          eFG
              (secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
                m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) =
            totalRelation υ := by
        simpa [τ, υ, eGen, eFG] using
          secondReductionCanonicalTransportBlockTotalWord_map_orderedTarget
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      rw [htotalMap]
      exact Subgroup.subset_normalClosure (Or.inr rfl)
  · intro s hs
    rcases hs with ⟨i, rfl⟩ | htotal
    · let j := eFin.symm i
      have hji : eFin j = i := by
        simp only [Equiv.apply_symm_apply, j]
      have hperiod : υ.periods i = τ.periods j := by
        rw [← hji]
        simpa [τ, υ, eFin, j] using
          (secondReductionCanonicalTransportOrdered_period
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail j).symm
      have hx :
          eFG.symm (xWord υ i) = xWord τ j := by
        simpa [τ, υ, eFin, eGen, eFG, j] using
          secondReductionCanonicalTransportOrdered_xWord_symm
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail i
      have hrel :
          eFG.symm ((xWord υ i) ^ υ.periods i) =
            (xWord τ j) ^ τ.periods j := by
        rw [map_pow, hx, hperiod]
      rw [hrel]
      exact Subgroup.subset_normalClosure (Or.inl ⟨j, rfl⟩)
    · rw [htotal]
      have htotalMap :
          eFG
              (secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
                m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail) =
            totalRelation υ := by
        simpa [τ, υ, eGen, eFG] using
          secondReductionCanonicalTransportBlockTotalWord_map_orderedTarget
            m₁' m₂' m₃' tail hp hq hm₁' hm₂' hm₃' htail
      have hsymm :
          eFG.symm (totalRelation υ) =
            secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
              m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail := by
        rw [← htotalMap]
        exact eFG.left_inv
          (secondReductionCanonicalTransportBlockTotalWord (p := p) (q := q)
            m₁' m₂' m₃' tail hq hm₁' hm₂' hm₃' htail)
      rw [hsymm]
      exact Subgroup.subset_normalClosure (Or.inr rfl)

end FenchelNielsen
