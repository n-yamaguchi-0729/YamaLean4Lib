import CrowellExactSequence.Profinite.BlanchfieldLyndon
import ProCGroups.FiniteStepSolvableQuotients.Abelianization
import ProCGroups.ProC.GroupPredicates.Standard

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/FiniteRank.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-rank pro-Sigma bridges for the profinite Crowell exact sequence

This file packages finite-rank free pro-`Σ` groups as `FreeProCSourceData` and exposes the
abelianization-kernel corollary used by center-freeness applications.
-/

open scoped Topology

namespace CrowellExactSequence

open ProCGroups.Abelian
open ProCGroups.FiniteStepSolvableQuotients

universe u

variable {F : Type u} [TopologicalSpace F] [Group F] [IsTopologicalGroup F]

/-- Package a finite-rank free pro-`Σ` group as CES free-source data. -/
noncomputable def finiteRank_freeProCSourceData
    {sigma : Set ℕ} {r : ℕ} (X : Fin r → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate
        (ProCGroups.FiniteGroupClass.sigmaGroup.{u} sigma))
      (Fin r) F X) :
    FreeProCSourceData (ProCGroups.ProC.proSigmaProC.{u} sigma) where
  basis := ULift.{u} (Fin r)
  carrier := F
  instGroup := inferInstance
  instTopologicalSpace := inferInstance
  instIsTopologicalGroup := inferInstance
  inclusion := fun i => X i.down
  isFree := by
    simpa [ProCGroups.ProC.proSigmaProC] using
      hFree.precompEquiv (Equiv.ulift : ULift.{u} (Fin r) ≃ Fin r)
  proCGroup := by
    refine
      { isProC := by
          simpa [ProCGroups.ProC.proSigmaProC] using hFree.isProC
        isProCGroup := ?_ }
    exact hFree.isProC.mono (D :=
      (ProCGroups.ProC.proSigmaProC.{u} sigma).finiteQuotientClass) (by
      intro Q _ hQ
      letI : Finite Q := ProCGroups.FiniteGroupClass.finite hQ
      exact (ProCGroups.ProC.proSigmaProC_finiteQuotientClass_iff
        (sigma := sigma) (Q := Q)).2 hQ)

/-- The finite-rank CES source data has the expected basis cardinality. -/
theorem finiteRank_freeProCSourceData_basis_card
    {sigma : Set ℕ} {r : ℕ} (X : Fin r → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate
        (ProCGroups.FiniteGroupClass.sigmaGroup.{u} sigma))
      (Fin r) F X) :
    Cardinal.mk (finiteRank_freeProCSourceData (F := F) X hFree).basis = r := by
  simp only [finiteRank_freeProCSourceData, Cardinal.mk_fintype, Fintype.card_ulift,
    Fintype.card_fin]

/-- The separated coordinate map for the topological abelianization of a finite-rank free
pro-`Σ` group. -/
noncomputable def finiteRank_topologicalAbelianization_sepCoordinateMap
    {sigma : Set ℕ} {r : ℕ} (X : Fin r → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate
        (ProCGroups.FiniteGroupClass.sigmaGroup.{u} sigma))
      (Fin r) F X) :=
  freeProCChosenULift_sepCoordinateMap
    (H := TopologicalAbelianization F)
    (ProC := ProCGroups.ProC.proSigmaProC.{u} sigma)
    (finiteRank_freeProCSourceData (F := F) X hFree)
    (finiteRank_freeProCSourceData_basis_card (F := F) X hFree)
    (TopologicalAbelianization.mkₜ F)
    (by
      change Function.Surjective (TopologicalAbelianization.mk F)
      exact TopologicalAbelianization.surjective_mk F)

/-- If the separated abelianized CES coordinate vector of a kernel element vanishes, the element
lies in the second closed derived subgroup. -/
theorem mem_topDerivedTop_two_of_finiteRank_topologicalAbelianization_sepCoordinateMap_eq_zero
    {sigma : Set ℕ} {r : ℕ} (X : Fin r → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate
        (ProCGroups.FiniteGroupClass.sigmaGroup.{u} sigma))
      (Fin r) F X)
    {a : F}
    (haψ : TopologicalAbelianization.mkₜ F a = 1)
    (hzero :
      finiteRank_topologicalAbelianization_sepCoordinateMap (F := F) X hFree
        (FoxDifferential.zcSeparatedUniversalDifferential
          (ProCGroups.ProC.proSigmaProC.{u} sigma).finiteQuotientClass
          (TopologicalAbelianization.mkₜ F).toMonoidHom a) = 0) :
    a ∈ topDerivedTop F 2 := by
  let sourceData := finiteRank_freeProCSourceData (F := F) (sigma := sigma) X hFree
  let hbasis := finiteRank_freeProCSourceData_basis_card (F := F) X hFree
  let ProC := ProCGroups.ProC.proSigmaProC.{u} sigma
  let ψ : F →ₜ* TopologicalAbelianization F := TopologicalAbelianization.mkₜ F
  have hψsurj : Function.Surjective ψ := by
    change Function.Surjective (TopologicalAbelianization.mk F)
    exact TopologicalAbelianization.surjective_mk F
  let htarget :=
    freeProCClosedGeneratedTarget_proC_of_surjective
      (H := TopologicalAbelianization F) (ProC := ProC) sourceData hbasis ψ hψsurj
  have hDzero :
      freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger
        (H := TopologicalAbelianization F) (ProC := ProC) sourceData hbasis ψ htarget a = 0 := by
    have happly := hzero
    dsimp [finiteRank_topologicalAbelianization_sepCoordinateMap, sourceData, hbasis, ProC, ψ] at happly
    change
      freeProCChosenULift_sepCoordinateMap
          (H := TopologicalAbelianization F) (ProC := ProC) sourceData hbasis ψ hψsurj
          (FoxDifferential.zcSeparatedUniversalDifferential ProC.finiteQuotientClass
            ψ.toMonoidHom a) = 0 at happly
    rw [freeProCChosenULift_sepCoordinateMap_universal] at happly
    simpa [finiteRank_topologicalAbelianization_sepCoordinateMap, sourceData, hbasis, ProC, ψ,
      freeProCCompletedFoxDerivativeVectorViaClosedGeneratedProCInteger, htarget] using happly
  have ha_closed :
      (⟨a, haψ⟩ : ProCGroups.ProC.ProfiniteKernelSubgroup ψ) ∈
        Subgroup.closedCommutator (ProCGroups.ProC.ProfiniteKernelSubgroup ψ) :=
    freeProC_closedGeneratedFoxVector_kernel_le_closedCommutator
      (H := TopologicalAbelianization F) (ProC := ProC) sourceData hbasis ψ hψsurj htarget
      ⟨a, haψ⟩ hDzero
  exact
    (mem_topDerivedTop_two_iff_mem_closedCommutator_topologicalAbelianizationKernel
      (G := F) haψ).2 ha_closed

end CrowellExactSequence
