import CrowellExactSequence.Profinite.KernelBoundary

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/KernelInjectivity.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite kernel boundary

This file contains the genuine boundary
`d_N : N^ab(C) -> A_psi(C)` and the continuous-Magnus injectivity criterion for it.
-/

namespace CrowellExactSequence

noncomputable section

open ProCGroups.ProC

universe u

variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Boundary from the genuine topological kernel abelianization to `A_psi(C)`, assuming the
displayed boundary kills `closure([N,N])`. -/
def profiniteKernelAbelianizationBoundaryHomProCInteger
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi) :
    ProfiniteKernelAbelianization psi →*
      Multiplicative (FoxDifferential.ZCCompletedDifferentialModule C psi.toMonoidHom) :=
  QuotientGroup.lift
    (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi)))
    (completedKernelBoundaryProCInteger (G := G) (H := H) C psi)
    hwell_dN

/-- Additive boundary from the genuine topological kernel abelianization to `A_psi(C)`. -/
def profiniteKernelAbelianizationBoundaryAddProCInteger
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi) :
    ProfiniteKernelAbelianizationAdd psi →+
      FoxDifferential.ZCCompletedDifferentialModule C psi.toMonoidHom :=
  (profiniteKernelAbelianizationBoundaryHomProCInteger
    (G := G) (H := H) C psi hwell_dN).toAdditiveLeft

@[simp]
theorem profiniteKernelAbelianizationBoundaryAddProCInteger_of
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi)
    (n : ProfiniteKernelSubgroup psi) :
    profiniteKernelAbelianizationBoundaryAddProCInteger
        (G := G) (H := H) C psi hwell_dN
        (Additive.ofMul
          (QuotientGroup.mk'
            (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n)) =
      FoxDifferential.zcUniversalDifferential C psi.toMonoidHom n.1 := by
  rfl

/-- Separated boundary from the genuine topological kernel abelianization to the finite-stage
separated completed differential module.  Unlike the algebraic target, this map is well-defined
without a separate closedness or continuity hypothesis. -/
def profiniteKernelAbelianizationBoundaryHomProCIntegerSep
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) :
    ProfiniteKernelAbelianization psi →*
      Multiplicative
        (FoxDifferential.ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom) :=
  QuotientGroup.lift
    (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi)))
    (separatedCompletedKernelBoundaryProCInteger (G := G) (H := H) C psi)
    (separatedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi)

/-- Additive separated boundary from the genuine topological kernel abelianization. -/
def profiniteKernelAbelianizationBoundaryAddProCIntegerSep
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H) :
    ProfiniteKernelAbelianizationAdd psi →+
      FoxDifferential.ZCSeparatedCompletedDifferentialModule C psi.toMonoidHom :=
  (profiniteKernelAbelianizationBoundaryHomProCIntegerSep
    (G := G) (H := H) C psi).toAdditiveLeft

/-- Pro-`C` notation for the separated topological kernel boundary. -/
def proCKernelAbelianizationBoundaryAddProCIntegerSep
    (ProC : ProCGroupPredicate.{u}) (psi : ContinuousMonoidHom G H) :
    ProCKernelAbelianizationAdd ProC psi →+
      FoxDifferential.ZCSeparatedCompletedDifferentialModule
        ProC.finiteQuotientClass psi.toMonoidHom :=
  profiniteKernelAbelianizationBoundaryAddProCIntegerSep
    (G := G) (H := H) ProC.finiteQuotientClass psi

@[simp]
theorem profiniteKernelAbelianizationBoundaryAddProCIntegerSep_of
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (n : ProfiniteKernelSubgroup psi) :
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
        (G := G) (H := H) C psi
        (Additive.ofMul
          (QuotientGroup.mk'
            (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n)) =
      FoxDifferential.zcSeparatedUniversalDifferential C psi.toMonoidHom n.1 := by
  rfl

theorem zcDiffModuleToSep_profKerAbBoundaryAddZC
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi)
    (x : ProfiniteKernelAbelianizationAdd psi) :
    FoxDifferential.zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom
        (profiniteKernelAbelianizationBoundaryAddProCInteger
          (G := G) (H := H) C psi hwell_dN x) =
      profiniteKernelAbelianizationBoundaryAddProCIntegerSep
        (G := G) (H := H) C psi x := by
  change
    (fun y : ProfiniteKernelAbelianization psi =>
      FoxDifferential.zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom
          (profiniteKernelAbelianizationBoundaryAddProCInteger
            (G := G) (H := H) C psi hwell_dN (Additive.ofMul y)) =
        profiniteKernelAbelianizationBoundaryAddProCIntegerSep
          (G := G) (H := H) C psi (Additive.ofMul y))
      (Additive.toMul x)
  refine QuotientGroup.induction_on (Additive.toMul x) ?_
  intro n
  change
    FoxDifferential.zcCompletedDifferentialModuleToSeparated C psi.toMonoidHom
        (profiniteKernelAbelianizationBoundaryAddProCInteger
          (G := G) (H := H) C psi hwell_dN
          (Additive.ofMul
            (QuotientGroup.mk'
              (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n))) =
      profiniteKernelAbelianizationBoundaryAddProCIntegerSep
        (G := G) (H := H) C psi
        (Additive.ofMul
          (QuotientGroup.mk'
            (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n))
  rw [profiniteKernelAbelianizationBoundaryAddProCInteger_of,
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep_of,
    FoxDifferential.zcCompletedDifferentialModuleToSeparated_universal]

theorem presentedCompletedToZC_profiniteKernelAbelianizationBoundaryAdd
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi)
    (x : ProfiniteKernelAbelianizationAdd psi) :
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi
        (profiniteKernelAbelianizationBoundaryAddProCInteger
          (G := G) (H := H) C psi hwell_dN x) =
      0 := by
  change
    (fun y : ProfiniteKernelAbelianization psi =>
      presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi
          (profiniteKernelAbelianizationBoundaryAddProCInteger
            (G := G) (H := H) C psi hwell_dN (Additive.ofMul y)) = 0)
      (Additive.toMul x)
  refine QuotientGroup.induction_on (Additive.toMul x) ?_
  intro n
  change
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger (G := G) (H := H) C psi
        (profiniteKernelAbelianizationBoundaryAddProCInteger
          (G := G) (H := H) C psi hwell_dN
          (Additive.ofMul
            (QuotientGroup.mk'
              (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n))) =
      0
  rw [profiniteKernelAbelianizationBoundaryAddProCInteger_of,
    presentedCompletedDifferentialToCompletedGroupAlgebraProCInteger_d_of_mem_ker]

/-- Magnus-kernel criterion form of injectivity for the genuine topological kernel boundary.

In paper language this is the step
`ker(D|_N) = closure([N,N]) => d_N : N^ab(C) -> A_psi(C)` is injective. -/
theorem profKerAbBoundaryAddZC_inj_of_kernel_le_closedCommutator
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi)
    (hker :
      ∀ n : ProfiniteKernelSubgroup psi,
        FoxDifferential.zcUniversalDifferential C psi.toMonoidHom n.1 = 0 →
          n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)) :
    Function.Injective
      (profiniteKernelAbelianizationBoundaryAddProCInteger
        (G := G) (H := H) C psi hwell_dN) := by
  intro x y hxy
  suffices x - y = 0 by exact sub_eq_zero.mp this
  let F :=
    profiniteKernelAbelianizationBoundaryAddProCInteger
      (G := G) (H := H) C psi hwell_dN
  have hmap : F (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hzero_of_map_zero :
      ∀ z : ProfiniteKernelAbelianizationAdd psi, F z = 0 → z = 0 := by
    intro z hz
    apply Additive.toMul.injective
    change (Additive.toMul z : ProfiniteKernelAbelianization psi) = 1
    revert hz
    change
      (fun q : ProfiniteKernelAbelianization psi =>
        F (Additive.ofMul q) = 0 → q = 1) (Additive.toMul z)
    refine QuotientGroup.induction_on (Additive.toMul z) ?_
    intro n hn
    change
      QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n = 1
    exact (QuotientGroup.eq_one_iff
      (N := Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n).2
        (by
          simpa [Subgroup.closedCommutator, F] using
            hker n (by simpa [F] using hn))
  exact hzero_of_map_zero (x - y) hmap

/-- Magnus-kernel criterion form of injectivity for the separated topological kernel boundary. -/
theorem profKerAbBoundaryAddZCSep_inj_of_kernel_le_closedCommutator
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (hker :
      ∀ n : ProfiniteKernelSubgroup psi,
        FoxDifferential.zcSeparatedUniversalDifferential C psi.toMonoidHom n.1 = 0 →
          n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)) :
    Function.Injective
      (profiniteKernelAbelianizationBoundaryAddProCIntegerSep
        (G := G) (H := H) C psi) := by
  intro x y hxy
  suffices x - y = 0 by exact sub_eq_zero.mp this
  let F :=
    profiniteKernelAbelianizationBoundaryAddProCIntegerSep
      (G := G) (H := H) C psi
  have hmap : F (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hzero_of_map_zero :
      ∀ z : ProfiniteKernelAbelianizationAdd psi, F z = 0 → z = 0 := by
    intro z hz
    apply Additive.toMul.injective
    change (Additive.toMul z : ProfiniteKernelAbelianization psi) = 1
    revert hz
    change
      (fun q : ProfiniteKernelAbelianization psi =>
        F (Additive.ofMul q) = 0 → q = 1) (Additive.toMul z)
    refine QuotientGroup.induction_on (Additive.toMul z) ?_
    intro n hn
    change
      QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n = 1
    exact (QuotientGroup.eq_one_iff
      (N := Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n).2
        (by
          simpa [Subgroup.closedCommutator, F] using
            hker n (by simpa [F] using hn))
  exact hzero_of_map_zero (x - y) hmap

/-- Injectivity of the genuine topological kernel boundary is exactly the Magnus-kernel
criterion in the reverse direction.

In paper language this says that once
`d_N : N^ab(C) -> A_psi(C)` is known to be injective, an element of `ker psi` whose completed
Fox differential vanishes is already in `closure([N,N])`. -/
theorem kernel_le_closedCommutator_of_profKerAbBoundaryAddZC_inj
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi)
    (hinj :
      Function.Injective
        (profiniteKernelAbelianizationBoundaryAddProCInteger
          (G := G) (H := H) C psi hwell_dN)) :
    ∀ n : ProfiniteKernelSubgroup psi,
      FoxDifferential.zcUniversalDifferential C psi.toMonoidHom n.1 = 0 →
        n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup psi) := by
  intro n hn
  let F :=
    profiniteKernelAbelianizationBoundaryAddProCInteger
      (G := G) (H := H) C psi hwell_dN
  have hzero :
      F
          (Additive.ofMul
            (QuotientGroup.mk'
              (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n)) =
        F 0 := by
    rw [profiniteKernelAbelianizationBoundaryAddProCInteger_of]
    simpa [F] using hn
  have hclass :
      Additive.ofMul
          (QuotientGroup.mk'
            (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n) =
        0 :=
    hinj hzero
  have hmk :
      QuotientGroup.mk'
          (Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n = 1 := by
    simpa using congrArg Additive.toMul hclass
  exact (QuotientGroup.eq_one_iff
    (N := Subgroup.topologicalClosure (commutator (ProfiniteKernelSubgroup psi))) n).1 hmk

/-- Paper-language form: injectivity of
`d_N : N^ab(C) -> A_psi(C)` is equivalent to the continuous Magnus-kernel criterion. -/
theorem profKerAbBoundaryAddZC_inj_iff_kernel_le_closedCommutator
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    (hwell_dN :
      CompletedBoundaryKillsTopologicalCommutatorProCInteger (G := G) (H := H) C psi) :
    Function.Injective
        (profiniteKernelAbelianizationBoundaryAddProCInteger
          (G := G) (H := H) C psi hwell_dN) ↔
      ∀ n : ProfiniteKernelSubgroup psi,
        FoxDifferential.zcUniversalDifferential C psi.toMonoidHom n.1 = 0 →
          n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup psi) := by
  constructor
  · exact
      kernel_le_closedCommutator_of_profKerAbBoundaryAddZC_inj
        (G := G) (H := H) C psi hwell_dN
  · exact
      profKerAbBoundaryAddZC_inj_of_kernel_le_closedCommutator
        (G := G) (H := H) C psi hwell_dN

/-- Continuous-boundary version of the Magnus-kernel injectivity criterion.

This packages the two paper steps `d_N` is well-defined and `ker D|_N <= closure([N,N])`:
continuity of the completed universal differential supplies well-definedness, and the kernel
criterion supplies injectivity of the resulting genuine boundary map. -/
theorem profKerAbBoundaryAddZC_inj_of_continuous_zcUnivDiff_kernel_le_closedCommutator
    (C : ProCGroups.FiniteGroupClass.{u}) (psi : ContinuousMonoidHom G H)
    [TopologicalSpace (FoxDifferential.ZCCompletedDifferentialModule C psi.toMonoidHom)]
    [T1Space (FoxDifferential.ZCCompletedDifferentialModule C psi.toMonoidHom)]
    (hD : Continuous
      (fun g : G => FoxDifferential.zcUniversalDifferential C psi.toMonoidHom g))
    (hker :
      ∀ n : ProfiniteKernelSubgroup psi,
        FoxDifferential.zcUniversalDifferential C psi.toMonoidHom n.1 = 0 →
          n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)) :
    let hwell_dN :=
      completedBoundaryKillsTopCommZC_of_continuous_zcUnivDiff
        (G := G) (H := H) C psi hD
    Function.Injective
      (profiniteKernelAbelianizationBoundaryAddProCInteger
        (G := G) (H := H) C psi hwell_dN) := by
  let hwell_dN :=
    completedBoundaryKillsTopCommZC_of_continuous_zcUnivDiff
      (G := G) (H := H) C psi hD
  exact
    profKerAbBoundaryAddZC_inj_of_kernel_le_closedCommutator
      (G := G) (H := H) C psi hwell_dN hker

end

end CrowellExactSequence
