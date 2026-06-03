import FoxDifferential.Completed.FreeProC.CoordinateStageProjection
import FoxDifferential.Completed.FreeProC.BifilteredSystemStageProjection

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/BifilteredCoefficientStageProjection.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Bifiltered stage projections from coefficient maps

This file builds bifiltered finite-stage maps on completed Fox coordinates from a compatible
family of coefficient ring maps

`Z_C[[H]] -> (Z/n_jZ)[F/N_j]`

together with compatible target quotient maps `H -> F/N_j`.  The coordinate maps, semidirect maps,
transition laws, boundary-cycle preservation, and kernel-word formulas are then derived
coordinatewise.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v

section BifilteredCoefficientMaps

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

/-- Coordinate maps attached to a compatible family of coefficient maps. -/
def zcFreeFoxCoordinatesBifilteredStageMap
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (j : J) :
    ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
      finiteFoxStageCoordinateVector (X := X) (Nstage j) (nstage j) :=
  zcFreeFoxCoordinatesStageMap
    (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j) (stageCoeff j)

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
@[simp]
theorem zcFreeFoxCoordinatesBifilteredStageMap_apply
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (j : J)
    (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (x : X) :
    zcFreeFoxCoordinatesBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff j v x =
      stageCoeff j (v x) :=
  rfl

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [∀ (j : J), Fact (0 < nstage j)] in
/-- Coefficient-map transition compatibility implies transition compatibility for coordinate
vectors. -/
theorem zcFreeFoxCoordinatesBifilteredStageMap_transition
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H,
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    {i j : J} (hij : i ≤ j)
    (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)) :
    finiteFoxStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij)
        (zcFreeFoxCoordinatesBifilteredStageMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff j v) =
      zcFreeFoxCoordinatesBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff i v := by
  funext x
  exact hcoeff hij (v x)

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/-- Group-like compatibility for coefficient maps gives scalar compatibility for the induced
coordinate maps. -/
theorem zcFreeFoxCoordinatesBifilteredStageMap_smul_groupLike
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike ProC.finiteQuotientClass H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (j : J) (h : H)
    (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)) :
    zcFreeFoxCoordinatesBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff j
        (zcGroupLike ProC.finiteQuotientClass H h • v) =
      (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
        (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
        zcFreeFoxCoordinatesBifilteredStageMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff j v :=
  zcFreeFoxCoordinatesStageMap_smul_groupLike
    (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
    (stageCoeff j) (stageRight j) (hgroupLike j) h v

/-- Completed-to-finite semidirect maps induced by coefficient maps. -/
def freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike ProC.finiteQuotientClass H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (j : J) :
    ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
      FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j) :=
  freeProCZCCompletedFoxSemidirectStageMapOfCoeff
    (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
    (stageCoeff j) (stageRight j) (hgroupLike j)

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [∀ (j : J), Fact (0 < nstage j)] in
/-- Transition compatibility of semidirect stage maps induced by coefficient maps. -/
theorem freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff_transition
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike ProC.finiteQuotientClass H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H,
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    {i j : J} (hij : i ≤ j) :
    (finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp
      (freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike j) =
    freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
      (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike i := by
  exact
    freeProCZCCompletedFoxSemidirectStageMap_bifilteredFamilyTransition
      (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn
      (fun k => zcFreeFoxCoordinatesBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff k)
      stageRight
      (fun k => zcFreeFoxCoordinatesBifilteredStageMap_smul_groupLike
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike k)
      (fun hij v => zcFreeFoxCoordinatesBifilteredStageMap_transition
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn stageCoeff hcoeff hij v)
      hright hij

/-- The coefficient-map stage family assembled as a map into the bifiltered finite semidirect
inverse limit. -/
def freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike ProC.finiteQuotientClass H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H,
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h) :
    ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
      FiniteFoxStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn :=
  freeProCZCCompletedFoxSemidirectBifilteredLimitMap
    (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn
    (fun j =>
      freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike j)
    (fun hij =>
      freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff_transition
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn stageCoeff stageRight
        hgroupLike hcoeff hright hij)

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
@[simp 900]
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff_projection
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike ProC.finiteQuotientClass H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H,
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (j : J) (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    finiteFoxStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff
          (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn
          stageCoeff stageRight hgroupLike hcoeff hright y) =
      freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike j y :=
  rfl

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Boundary-cycle preservation for the bifiltered limit map induced by coefficient maps. -/
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff_mem_boundaryCycleSet
    [Fintype X] (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike ProC.finiteQuotientClass H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H,
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    {y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H}
    (hy : y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ) :
    freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn
        stageCoeff stageRight hgroupLike hcoeff hright y ∈
      finiteFoxStageBifilteredSemidirectLimitBoundaryCycleSet
        (X := X) Nstage nstage hN hn := by
  intro j
  simpa [freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff_projection]
    using
      freeProCZCCompletedFoxSemidirectStageMapOfCoeff_mem_finiteBoundaryCycleSet
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j) φ
        (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) hy

omit [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Kernel-word preservation for the bifiltered limit map induced by coefficient maps. -/
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff_kernelWordPoint
    (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike ProC.finiteQuotientClass H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H,
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      finiteFoxStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (hright_generators : ∀ j : J, ∀ i : X,
      stageRight j (φ i) = QuotientGroup.mk' (Nstage j) (FreeGroup.of i))
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfCoeff
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn
        stageCoeff stageRight hgroupLike hcoeff hright
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w) =
      finiteFoxStageBifilteredSemidirectKernelWordPointLimit
        (X := X) Nstage nstage hN hn w := by
  apply Subtype.ext
  funext j
  exact
    freeProCZCCompletedFoxSemidirectStageMapOfCoeff_kernelWordPoint
      (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j) φ
      (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) w

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Completed density from coefficient-map finite stages.  This theorem packages the whole finite
relation-ideal derivative route after the completed projections have been reduced to coefficient
maps and target quotient maps. -/
theorem freeProCZCFoxBoundaryCycles_subset_kernelCycles_of_biCoeff_relDeriv
    [Fintype X] (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike ProC.finiteQuotientClass H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H,
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
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
            stageCoeff stageRight hgroupLike j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  exact
    boundaryCycles_subset_kernelClosure_of_biStageMaps
      (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn φ
      (fun j => zcFreeFoxCoordinatesBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff j)
      stageRight
      (fun j => zcFreeFoxCoordinatesBifilteredStageMap_smul_groupLike
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike j)
      (fun hij v => zcFreeFoxCoordinatesBifilteredStageMap_transition
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn stageCoeff hcoeff hij v)
      hright
      hidentity_basis
      (fun j => (stageCoeff j).toAddMonoidHom)
      (fun j v => finiteFoxStageFoxBoundary_zcFreeFoxCoordinatesStageMap_of_groupLike
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j) φ
        (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) v)
      hNstage_kernel
      (fun j w => zcFreeFoxCoordinatesStageMap_derivativeVector_of_generators
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j) φ
        (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) w)

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Completed graph-word density from coefficient-map finite stages.

This is the finite-quotient-safe version of the preceding kernel-word density theorem: words in
`Nstage j` are used only to make the finite right coordinate trivial, not as genuine kernel words
for the completed target map. -/
theorem boundaryCycles_subset_graphWordClosure_of_biCoeffStages
    [Fintype X] (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike ProC.finiteQuotientClass H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (_hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H,
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
    (_hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
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
            stageCoeff stageRight hgroupLike j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (ProC := ProC) φ) := by
  exact
    boundaryCycles_subset_graphWordClosure_of_stageMaps
      (ProC := ProC) (X := X) (H := H) φ Nstage nstage
      (fun j => zcFreeFoxCoordinatesBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff j)
      stageRight
      (fun j => zcFreeFoxCoordinatesBifilteredStageMap_smul_groupLike
        (ProC := ProC) (X := X) (H := H) Nstage nstage stageCoeff stageRight hgroupLike j)
      hidentity_basis
      (fun j => (stageCoeff j).toAddMonoidHom)
      (fun j v => finiteFoxStageFoxBoundary_zcFreeFoxCoordinatesStageMap_of_groupLike
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j) φ
        (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) v)
      (fun j w => finiteStageRight_comp_lift_eq_quotientMk
        (X := X) (H := H) (Nstage j) φ
        (stageRight j) (hright_generators j) w)
      (fun j w => zcFreeFoxCoordinatesStageMap_derivativeVector_of_generators
        (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j) φ
        (stageCoeff j) (stageRight j) (hgroupLike j) (hright_generators j) w)

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Closed-generated-target membership from coefficient-map finite stages, without a completed
kernel-word hypothesis. -/
theorem boundaryCycles_subset_closedGenTarget_of_biCoeffGraph
    [Fintype X] (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike ProC.finiteQuotientClass H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H,
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
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
            stageCoeff stageRight hgroupLike j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density
      (ProC := ProC) φ
      (boundaryCycles_subset_graphWordClosure_of_biCoeffStages
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn φ stageCoeff stageRight
        hgroupLike hcoeff hright hright_generators hidentity_basis)

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Closed-generated target membership from coefficient-map finite stages. -/
theorem boundaryCycles_subset_closedGenTarget_of_biCoeffStages
    [Fintype X] (φ : X → H)
    (stageCoeff : ∀ j : J,
      ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
        finiteFoxStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hgroupLike : ∀ j : J, ∀ h : H,
      stageCoeff j (zcGroupLike ProC.finiteQuotientClass H h) =
        MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
          (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h))
    (hcoeff : ∀ {i j : J} (hij : i ≤ j), ∀ a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H,
      finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
        (stageCoeff j a) = stageCoeff i a)
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
            stageCoeff stageRight hgroupLike j))
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
      (freeProCZCFoxBoundaryCycles_subset_kernelCycles_of_biCoeff_relDeriv
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn φ
        stageCoeff stageRight hgroupLike hcoeff hright hright_generators hidentity_basis
        hNstage_kernel)

end BifilteredCoefficientMaps

end

end FoxDifferential
