import CrowellExactSequence.Profinite.ContinuousMagnus.KernelClosedCommutator
import CrowellExactSequence.Profinite.KernelInjectivity

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/ContinuousMagnus/Injectivity.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite Crowell exact sequence

Crowell-specific material is kept separate from general Fox calculus: relation modules, kernel boundaries, Blanchfield-Lyndon maps, and discrete/profinite exactness statements are assembled here.
-/
namespace CrowellExactSequence

noncomputable section

open ProCGroups.ProC

universe u

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {ProC : ProCGroupPredicate.{u}}

variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass]

omit [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass] in
/-- Continuous Magnus injectivity for the displayed boundary
`d_N : N^ab(C) -> A_psi(C)`.

This is the paper step obtained by combining the completed Fox-vector kernel theorem with the
general kernel criterion for the genuine topological kernel abelianization. -/
theorem freeProC_profKerAbBoundaryAddZC_inj_of_continuousMagnus
    [T2Space H]
    [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients]
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
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi) :
    Function.Injective
      (profiniteKernelAbelianizationBoundaryAddProCInteger
        (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi hwell_dN) :=
  profKerAbBoundaryAddZC_inj_of_kernel_le_closedCommutator
    (G := sourceData.carrier) (H := H) ProC.finiteQuotientClass psi hwell_dN
    (freeProC_zcUnivDiff_kernel_le_closedCommutator_of_closedGenFoxVector
      (H := H) (ProC := ProC) sourceData hbasis psi hpsi htarget
      (freeProC_closedGeneratedFoxVector_kernel_le_closedCommutator
        (H := H) (ProC := ProC) sourceData hbasis psi hpsi htarget))


end

end CrowellExactSequence
