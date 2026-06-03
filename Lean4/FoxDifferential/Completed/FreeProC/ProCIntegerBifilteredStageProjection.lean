import FoxDifferential.Completed.FreeProC.ProCIntegerStageCoeffProjection

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/ProCIntegerBifilteredStageProjection.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Bifiltered finite Fox stages built from `Z_C[[H]]` stage projections

This file specializes the coefficient-map density route to coefficient maps obtained from
finite stages of `Z_C[[H]]`.  The data consist of a finite `Z_C[[H]]` stage, a quotient from its
group component to the finite Fox target, and the transition formulas relating these choices.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v

section BifilteredFromZCStages

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable {J : Type v} [Preorder J]
variable (Nstage : J → Subgroup (FreeGroup X)) [∀ j, (Nstage j).Normal]
variable (nstage : J → ℕ) [∀ j, Fact (0 < nstage j)]
variable (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
variable (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
variable (zcIndex : J → ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H)
variable (hzcIndex : ∀ {i j : J}, i ≤ j → zcIndex i ≤ zcIndex j)
variable (hmod : ∀ j : J, nstage j ∣ (zcIndex j).1.modulus)
variable (qmap : ∀ j : J,
  CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2 →*
    finiteFoxStageTargetQuotient (X := X) (Nstage j))

/-- The completed-to-finite coefficient map at a bifiltered stage, built from an actual
`Z_C[[H]]` stage projection. -/
def zcCompletedGroupAlgebraBifilteredStageCoeffMap
    (j : J) :
    ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
      finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j) :=
  zcCompletedGroupAlgebraFiniteFoxStageCoeffMap
    (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j) (zcIndex j)
    (hmod j) (qmap j)

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
@[simp]
theorem zcCompletedGroupAlgebraBifilteredStageCoeffMap_apply
    (j : J) (a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) :
    zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j a =
      zcCompletedGroupAlgebraFiniteFoxStageCoeffMap
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j) (zcIndex j)
        (hmod j) (qmap j) a :=
  rfl

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/-- Group-like formula for a bifiltered stage projection, in terms of the chosen quotient map. -/
theorem zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike
    (j : J) (h : H) :
    zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j
        (zcGroupLike ProC.finiteQuotientClass H h) =
      MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
        (finiteFoxStageTargetQuotient (X := X) (Nstage j))
        (qmap j (QuotientGroup.mk h)) := by
  exact zcCompletedGroupAlgebraFiniteFoxStageCoeffMap_groupLike
    (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j) (zcIndex j)
    (hmod j) (qmap j) h

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/-- Group-like formula rewritten through the finite right quotient map. -/
theorem zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
    (stageRight : ∀ j : J,
      H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hqmap_groupLike : ∀ j : J, ∀ h : H,
      qmap j (QuotientGroup.mk h) = stageRight j h)
    (j : J) (h : H) :
    zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j
        (zcGroupLike ProC.finiteQuotientClass H h) =
      MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
        (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h) := by
  rw [zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike]
  rw [hqmap_groupLike j h]

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/-- Compatibility of the completed-to-finite coefficient maps under a bifiltered transition. -/
theorem zcCompletedGroupAlgebraBifilteredStageCoeffMap_transition
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    {i j : J} (hij : i ≤ j)
    (a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) :
    finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (zcCompletedGroupAlgebraBifilteredStageCoeffMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j a) =
      zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap i a := by
  exact zcCompletedGroupAlgebraFiniteFoxStageCoeffMap_transition
    (ProC := ProC) (X := X) (H := H) (hN hij) (hn hij) (hzcIndex hij)
    (hmod i) (hmod j) (hcoeff_mod hij) (qmap i) (qmap j)
    (hqmap_transition hij) a

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Completed density from actual `Z_C[[H]]` finite-stage projections.

This is the coefficient-map route with the coefficient maps specialized to genuine finite-stage
projections of the completed group algebra. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_zcBiStageProj_relDeriv
    [Fintype X] (φ : X → H)
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hqmap_groupLike : ∀ j : J, ∀ h : H,
      qmap j (QuotientGroup.mk h) = stageRight j h)
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (ProC := ProC) (X := X) (H := H) Nstage nstage
            (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
            stageRight
            (fun k h =>
              zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
                (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
                stageRight hqmap_groupLike k h)
            j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_kernelCycles_of_biCoeff_relDeriv
      (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn φ
      (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
      stageRight
      (fun k h =>
        zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
          (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
          stageRight hqmap_groupLike k h)
      (fun hij a =>
        zcCompletedGroupAlgebraBifilteredStageCoeffMap_transition
          (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
          hmod qmap hcoeff_mod hqmap_transition hij a)
      hright hright_generators hidentity_basis hNstage_kernel

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Completed graph-word density from actual `Z_C[[H]]` finite-stage projections.

This variant removes the completed kernel-word assumption from the density step.  Finite-stage
relation words are used through their finite right-coordinate equation only. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_zcBiStageProj_relDeriv
    [Fintype X] (φ : X → H)
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hqmap_groupLike : ∀ j : J, ∀ h : H,
      qmap j (QuotientGroup.mk h) = stageRight j h)
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (ProC := ProC) (X := X) (H := H) Nstage nstage
            (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
            stageRight
            (fun k h =>
              zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
                (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
                stageRight hqmap_groupLike k h)
            j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (ProC := ProC) φ) := by
  exact
    boundaryCycles_subset_graphWordClosure_of_biCoeffStages
      (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn φ
      (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
      stageRight
      (fun k h =>
        zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
          (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
          stageRight hqmap_groupLike k h)
      (fun hij a =>
        zcCompletedGroupAlgebraBifilteredStageCoeffMap_transition
          (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
          hmod qmap hcoeff_mod hqmap_transition hij a)
      hright hright_generators hidentity_basis

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Closed-generated target membership from actual `Z_C[[H]]` finite-stage projections, using
graph-word density rather than completed kernel-word density. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_zcBiStageProj_graphRelDeriv
    [Fintype X] (φ : X → H)
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hqmap_groupLike : ∀ j : J, ∀ h : H,
      qmap j (QuotientGroup.mk h) = stageRight j h)
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (ProC := ProC) (X := X) (H := H) Nstage nstage
            (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
            stageRight
            (fun k h =>
              zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
                (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
                stageRight hqmap_groupLike k h)
            j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density
      (ProC := ProC) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_zcBiStageProj_relDeriv
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
        hmod qmap φ stageRight hqmap_groupLike hcoeff_mod hqmap_transition hright
        hright_generators hidentity_basis)

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Closed-generated target membership from actual `Z_C[[H]]` finite-stage projections. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_zcBiStageProj_relDeriv
    [Fintype X] (φ : X → H)
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hqmap_groupLike : ∀ j : J, ∀ h : H,
      qmap j (QuotientGroup.mk h) = stageRight j h)
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
            (ProC := ProC) (X := X) (H := H) Nstage nstage
            (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
            stageRight
            (fun k h =>
              zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_eq_stageRight
                (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap
                stageRight hqmap_groupLike k h)
            j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density
      (ProC := ProC) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_zcBiStageProj_relDeriv
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
        hmod qmap φ stageRight hqmap_groupLike hcoeff_mod hqmap_transition hright
        hright_generators hidentity_basis hNstage_kernel)

end BifilteredFromZCStages

end

end FoxDifferential
