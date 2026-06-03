import CrowellExactSequence.Profinite.FreeProCSourceData
import FoxDifferential.Completed.Continuous.Free.Continuity
import FoxDifferential.Completed.Continuous.TopologicalGeneration

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/ContinuousMagnus/ClosedGeneratedVector.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Continuous Magnus criterion over pro-C integer coefficients

This file is internal to the proof that the displayed
`d_N : N^ab(C) -> A_psi(C)` is injective.  Its conclusions are stated back in terms of the
completed Fox differential on the genuine kernel, not as a second exact sequence.
-/

namespace CrowellExactSequence

noncomputable section

open ProCGroups.ProC

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {ProC : ProCGroupPredicate.{u}}

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass]

/-- The closed-generated continuous Fox derivative vector attached to a finite chosen free
pro-`C` basis and a presentation map. -/
def freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (htarget :
      ProC
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC)
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (ProC := ProC) sourceData hbasis i)) : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect
                ProC.finiteQuotientClass (ULift.{u} (Fin r)) H)))) :
    sourceData.carrier →
      FoxDifferential.ZCFreeFoxCoordinates
        ProC.finiteQuotientClass (X := ULift.{u} (Fin r)) (H := H) :=
  let hfree :=
    freeProCChosenULiftFamilyOfBasisCard_isFree (ProC := ProC) sourceData hbasis
  let φ : ULift.{u} (Fin r) → H := fun i =>
    psi (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis i)
  let hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) φ : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect
                ProC.finiteQuotientClass (ULift.{u} (Fin r)) H)))
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (ProC := ProC) φ) :=
    FoxDifferential.freeProCZCFoxSemiClosedGenGenerator_convergesToOne_of_finite
      (ProC := ProC) φ
  FoxDifferential.freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
    (ProC := ProC) hfree φ htarget hφconv

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- An abstract kernel word for the chosen finite free basis gives a genuine cycle point in the
closed-generated Fox graph target.  This is the algebraic source of the completed cycle-lifting
step: before passing to closures, every relation word `w` with target value `1` contributes
`(D w, 1)` to the closed-generated graph. -/
theorem freeProC_closedGeneratedTarget_mem_of_freeGroupFoxDerivativeVector_kernel
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    {w : FreeGroup (ULift.{u} (Fin r))}
    (hw :
      FreeGroup.lift
          (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard
              (ProC := ProC) sourceData hbasis i)) w = 1) :
    ({ left :=
        FoxDifferential.zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass
          (FreeGroup.lift
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (ProC := ProC) sourceData hbasis i))) w,
       right := (1 : H) } :
      FoxDifferential.ZCCompletedFoxSemidirect ProC.finiteQuotientClass
        (ULift.{u} (Fin r)) H) ∈
      (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC)
        (fun i : ULift.{u} (Fin r) =>
          psi (freeProCChosenULiftFamilyOfBasisCard
            (ProC := ProC) sourceData hbasis i)) : Subgroup
          (FoxDifferential.ZCCompletedFoxSemidirect ProC.finiteQuotientClass
            (ULift.{u} (Fin r)) H)) := by
  exact
    FoxDifferential.freeProCZCFoxClosedGenTarget_mem_of_freeFoxDerivVec_kernel
      (ProC := ProC)
      (fun i : ULift.{u} (Fin r) =>
        psi (freeProCChosenULiftFamilyOfBasisCard
          (ProC := ProC) sourceData hbasis i))
      hw

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- The right component of the closed-generated Fox graph attached to the chosen lifted finite
basis is the original presentation map.

This is the target-coordinate half of the paper graph identity.  It is independent of the left
Fox-coordinate calculation: the right component and `psi` are continuous homomorphisms from the
same free pro-`C` group, and they agree on the chosen free generators. -/
theorem freeProCCompletedFoxRightHomViaClosedGeneratedProCInteger_eq
    [T2Space H] [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi)
    (htarget :
      ProC
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC)
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (ProC := ProC) sourceData hbasis i)) : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect
                ProC.finiteQuotientClass (ULift.{u} (Fin r)) H)))) :
    FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated
        (ProC := ProC)
        (freeProCChosenULiftFamilyOfBasisCard_isFree (ProC := ProC) sourceData hbasis)
        (fun i : ULift.{u} (Fin r) =>
          psi (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis i))
        htarget
        (FoxDifferential.freeProCZCFoxSemiClosedGenGenerator_convergesToOne_of_finite
          (ProC := ProC)
          (fun i : ULift.{u} (Fin r) =>
            psi (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis i))) =
      psi.toMonoidHom := by
  let X : Type u := ULift.{u} (Fin r)
  let ι : X → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  let hfree := freeProCChosenULiftFamilyOfBasisCard_isFree (ProC := ProC) sourceData hbasis
  let φ : X → H := fun i => psi (ι i)
  let hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) φ : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (ProC := ProC) φ) :=
    FoxDifferential.freeProCZCFoxSemiClosedGenGenerator_convergesToOne_of_finite
      (ProC := ProC) φ
  have hH : ProC (G := H) :=
    (ProCGroup.of_surjective (G := sourceData.carrier) ProC psi hpsi).isProC
  have hφHconv : ProCGroups.FreeProC.FamilyConvergesToOne (G := H) φ := by
    simpa [φ, ι] using
      freeProCChosenULiftFamilyOfBasisCard_image_convergesToOne
        (ProC := ProC) sourceData hbasis psi.toMonoidHom
  have hφHgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ) := by
    simpa [φ, ι] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (ProC := ProC) sourceData hbasis psi hpsi
  simpa [X, ι, hfree, φ, hφconv] using
    FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
      (ProC := ProC) X H hfree hH φ htarget hφconv hφHconv hφHgen psi
      (by intro i; rfl)

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- The closed-generated continuous Fox derivative vector is a crossed differential with respect
to the original presentation map, once the presentation is surjective. -/
theorem freeProCCompletedFoxDerivVecViaClosedGenZC_isCrossedDiff
    [T2Space H] [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi)
    (htarget :
      ProC
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC)
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (ProC := ProC) sourceData hbasis i)) : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect
                ProC.finiteQuotientClass (ULift.{u} (Fin r)) H)))) :
    FoxDifferential.IsCrossedDifferential
      (FoxDifferential.zcCompletedGroupAlgebraScalar
        ProC.finiteQuotientClass psi.toMonoidHom)
      (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
        (H := H) (ProC := ProC) sourceData hbasis psi htarget) := by
  let X : Type u := ULift.{u} (Fin r)
  let ι : X → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  let hfree := freeProCChosenULiftFamilyOfBasisCard_isFree (ProC := ProC) sourceData hbasis
  let φ : X → H := fun i => psi (ι i)
  let hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) φ : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (ProC := ProC) φ) :=
    FoxDifferential.freeProCZCFoxSemiClosedGenGenerator_convergesToOne_of_finite
      (ProC := ProC) φ
  have hH : ProC (G := H) :=
    (ProCGroup.of_surjective (G := sourceData.carrier) ProC psi hpsi).isProC
  have hφHconv : ProCGroups.FreeProC.FamilyConvergesToOne (G := H) φ := by
    simpa [φ, ι] using
      freeProCChosenULiftFamilyOfBasisCard_image_convergesToOne
        (ProC := ProC) sourceData hbasis psi.toMonoidHom
  have hφHgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ) := by
    simpa [φ, ι] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (ProC := ProC) sourceData hbasis psi hpsi
  have hright :
      FoxDifferential.freeProCZCCompletedFoxRightHomViaClosedGenerated
          (ProC := ProC) hfree φ htarget hφconv =
        psi.toMonoidHom := by
    simpa [X, ι, hfree, φ, hφconv] using
      freeProCCompletedFoxRightHomViaClosedGeneratedProCInteger_eq
        (H := H) (ProC := ProC) sourceData hbasis psi hpsi htarget
  have hD :=
    FoxDifferential.freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated_isCrossedDifferential
      (ProC := ProC) hfree φ htarget hφconv
  simpa [freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger, X, ι, φ,
    hfree, hφconv, hright] using hD

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- The closed-generated continuous Fox derivative vector is continuous. -/
theorem continuous_freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (htarget :
      ProC
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC)
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (ProC := ProC) sourceData hbasis i)) : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect
                ProC.finiteQuotientClass (ULift.{u} (Fin r)) H)))) :
    Continuous
      (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
        (H := H) (ProC := ProC) sourceData hbasis psi htarget) := by
  let hfree :=
    freeProCChosenULiftFamilyOfBasisCard_isFree (ProC := ProC) sourceData hbasis
  let φ : ULift.{u} (Fin r) → H := fun i =>
    psi (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis i)
  let hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) φ : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect
                ProC.finiteQuotientClass (ULift.{u} (Fin r)) H)))
        (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator
          (ProC := ProC) φ) :=
    FoxDifferential.freeProCZCFoxSemiClosedGenGenerator_convergesToOne_of_finite
      (ProC := ProC) φ
  simpa [freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger, hfree, φ, hφconv] using
    FoxDifferential.continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
      (ProC := ProC) (ULift.{u} (Fin r)) H hfree φ htarget hφconv

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- Universal completed Magnus-kernel reduction for the closed-generated continuous Fox vector.

After this theorem, the remaining paper statement is exactly the concrete continuous Magnus
kernel for the completed Fox derivative vector. -/
theorem freeProC_zcUnivDiff_kernel_le_closedCommutator_of_closedGenFoxVector
    [T2Space H] [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    (sourceData : FreeProCSourceData ProC)
    {r : Nat} (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi)
    (htarget :
      ProC
        (G :=
          (FoxDifferential.freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC)
            (fun i : ULift.{u} (Fin r) =>
              psi (freeProCChosenULiftFamilyOfBasisCard
                (ProC := ProC) sourceData hbasis i)) : Subgroup
              (FoxDifferential.ZCCompletedFoxSemidirect
                ProC.finiteQuotientClass (ULift.{u} (Fin r)) H))))
    (hDker :
      ∀ n : ProfiniteKernelSubgroup psi,
        freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
            (H := H) (ProC := ProC) sourceData hbasis psi htarget n.1 = 0 →
          n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)) :
    ∀ n : ProfiniteKernelSubgroup psi,
      FoxDifferential.zcUniversalDifferential
          ProC.finiteQuotientClass psi.toMonoidHom n.1 = 0 →
        n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup psi) := by
  exact
    FoxDifferential.zcUniversalDifferential_kernel_le_closedCommutator_of_crossedDifferential
      ProC.finiteQuotientClass psi
      (freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
        (H := H) (ProC := ProC) sourceData hbasis psi htarget)
      (freeProCCompletedFoxDerivVecViaClosedGenZC_isCrossedDiff
        (H := H) (ProC := ProC) sourceData hbasis psi hpsi htarget)
      hDker

end

end CrowellExactSequence
