import FoxDifferential.Completed.FreeProC.ProCIntegerBifilteredStageProjection
import FoxDifferential.Completed.FreeProC.QuotientKernelBasis

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/ProCIntegerBifilteredStageRightProjection.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Right-coordinate maps for `Z_C[[H]]` bifiltered Fox stages

The right coordinate of a finite Fox stage is obtained from the same finite quotient of `H`
that defines the `Z_C[[H]]` coefficient projection.  Given the quotient map out of the
`Z_C[[H]]` stage quotient, this file defines the right coordinate by composition with
`H -> H/U_j`, proves its transition law, and packages the completed-to-finite semidirect stage maps.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v

section BifilteredRightMaps

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

/-- The right quotient map attached to a bifiltered `Z_C[[H]]` stage.

It is not independent data: it is the quotient map `H -> H/U_j` followed by the chosen map
`H/U_j -> F/N_j`. -/
def zcCompletedGroupAlgebraBifilteredStageRightMap
    (j : J) :
    H →* finiteFoxStageTargetQuotient (X := X) (Nstage j) where
  toFun h := qmap j (QuotientGroup.mk h)
  map_one' := by
    simp only [QuotientGroup.mk_one, map_one]
  map_mul' h₁ h₂ := by
    simp only [QuotientGroup.mk_mul, map_mul]

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] in
@[simp]
theorem zcCompletedGroupAlgebraBifilteredStageRightMap_apply
    (j : J) (h : H) :
    zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j h =
      qmap j (QuotientGroup.mk h) :=
  rfl

/-- The intermediate quotient map `H -> H/U_j` used by a bifiltered `Z_C[[H]]` stage.

The automatically defined right map factors as this quotient map followed by `qmap j`.  Naming the
quotient map separately lets the kernel-basis proof for the target coordinate use the usual finite
quotient neighbourhood basis of `H`, before applying the map to the Fox relation quotient. -/
def zcCompletedGroupAlgebraBifilteredStageQuotientMap
    (j : J) :
    H →* CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2 :=
  openNormalSubgroupInClassProj
    (C := ProC.finiteQuotientClass) (G := H) (zcIndex j).2

omit [Preorder J] in
@[simp]
theorem zcCompletedGroupAlgebraBifilteredStageQuotientMap_apply
    (j : J) (h : H) :
    zcCompletedGroupAlgebraBifilteredStageQuotientMap
        (ProC := ProC) (H := H) (zcIndex := zcIndex) j h =
      QuotientGroup.mk h :=
  rfl

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] in
/-- The automatically defined right map is `qmap` after the underlying `H/U_j` quotient map. -/
theorem zcCompletedGroupAlgebraBifilteredStageRightMap_eq_comp_stageQuotientMap
    (j : J) :
    zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j =
      (qmap j).comp
        (zcCompletedGroupAlgebraBifilteredStageQuotientMap
          (ProC := ProC) (H := H) (zcIndex := zcIndex) j) := by
  ext h
  rfl

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] in
/-- If the kernels of the underlying `H -> H/U_j` quotients form an identity-neighbourhood
basis, and the maps `H/U_j -> F/N_j` are injective, then the automatically defined right
coordinate maps `H -> F/N_j` also have identity-neighbourhood kernel basis.

This is the target-coordinate analogue of the coefficient-kernel reduction on the left coordinate.
It isolates exactly the remaining target-side input: choose the finite stages so that `H/U_j` is
identified with the finite quotient `F/N_j`, or at least injects into it through `qmap j`. -/
theorem zcCompletedGABifilteredStageRightMap_identity_basis_of_stageQuotient_basis
    (hquotient_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := H)
        (fun j : J =>
          zcCompletedGroupAlgebraBifilteredStageQuotientMap
            (ProC := ProC) (H := H) (zcIndex := zcIndex) j))
    (hqmap_injective : ∀ j : J, Function.Injective (qmap j)) :
    HasIdentityQuotientKernelNeighbourhoodBasis
      (Y := H)
      (fun j : J =>
        zcCompletedGroupAlgebraBifilteredStageRightMap
          (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j) := by
  intro U hU hUone
  rcases hquotient_basis U hU hUone with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  intro h hh
  have hh_eq :
      zcCompletedGroupAlgebraBifilteredStageRightMap
          (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j h = 1 := by
    simpa [MonoidHom.mem_ker] using hh
  have hq :
      zcCompletedGroupAlgebraBifilteredStageQuotientMap
          (ProC := ProC) (H := H) (zcIndex := zcIndex) j h = 1 := by
    apply hqmap_injective j
    change qmap j
        (zcCompletedGroupAlgebraBifilteredStageQuotientMap
          (ProC := ProC) (H := H) (zcIndex := zcIndex) j h) = qmap j 1
    simpa [zcCompletedGroupAlgebraBifilteredStageRightMap_eq_comp_stageQuotientMap]
      using hh_eq
  exact hj h (by simpa [MonoidHom.mem_ker] using hq)

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/-- The group-like formula for coefficient maps, with the right map defined from the same
`Z_C[[H]]` stage quotient. -/
theorem zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_autoRight
    (j : J) (h : H) :
    zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j
        (zcGroupLike ProC.finiteQuotientClass H h) =
      MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
        (finiteFoxStageTargetQuotient (X := X) (Nstage j))
        (zcCompletedGroupAlgebraBifilteredStageRightMap
          (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j h) := by
  rw [zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike]
  rfl

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Transition compatibility for the right maps follows from transition compatibility of the
quotient maps out of the `Z_C[[H]]` stage quotients. -/
theorem zcCompletedGroupAlgebraBifilteredStageRightMap_transition
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    {i j : J} (hij : i ≤ j) (h : H) :
    finiteFoxStageTargetQuotientMap (X := X) (hN hij)
        (zcCompletedGroupAlgebraBifilteredStageRightMap
          (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j h) =
      zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap i h := by
  simpa [zcCompletedGroupAlgebraBifilteredStageRightMap,
    OpenNormalSubgroupInClass.map] using
    (hqmap_transition hij
      (QuotientGroup.mk h :
        CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2)).symm


omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Homomorphism-level transition compatibility for the automatically defined right maps. -/
theorem zcCompletedGroupAlgebraBifilteredStageRightMap_transition_hom
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    {i j : J} (hij : i ≤ j) :
    (finiteFoxStageTargetQuotientMap (X := X) (hN hij)).comp
        (zcCompletedGroupAlgebraBifilteredStageRightMap
          (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j) =
      zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap i := by
  ext h
  exact zcCompletedGroupAlgebraBifilteredStageRightMap_transition
    (ProC := ProC) (X := X) (H := H) (Nstage := Nstage) (hN := hN)
    (zcIndex := zcIndex) (hzcIndex := hzcIndex) (qmap := qmap)
    hqmap_transition hij h

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] in
/-- Generator formula for the automatically defined right map. -/
theorem zcCompletedGroupAlgebraBifilteredStageRightMap_generators
    {φ : X → H}
    (hgenerators : ∀ j : J, ∀ x : X,
      qmap j (QuotientGroup.mk (φ x)) =
        QuotientGroup.mk' (Nstage j) (FreeGroup.of x))
    (j : J) (x : X) :
    zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j (φ x) =
      QuotientGroup.mk' (Nstage j) (FreeGroup.of x) := by
  exact hgenerators j x

/-- The completed-to-finite semidirect stage map with both coordinates produced from the same
`Z_C[[H]]` stage projection data. -/
def freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
    (j : J) :
    ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
      FiniteFoxStageSemidirect (X := X) (Nstage j) (nstage j) :=
  freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff
    (ProC := ProC) (X := X) (H := H) Nstage nstage
    (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
      (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
    (zcCompletedGroupAlgebraBifilteredStageRightMap
      (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap)
    (fun k h => zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_autoRight
      (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k h)
    j

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
@[simp]
theorem freeProCZCCompletedFoxSemidirectZCBifilteredStageMap_left
    (j : J) (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    (freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j y).left =
      zcFreeFoxCoordinatesBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage
        (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
        j y.left :=
  rfl

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [Preorder J] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
@[simp]
theorem freeProCZCCompletedFoxSemidirectZCBifilteredStageMap_right
    (j : J) (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    (freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j y).right =
      zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j y.right :=
  rfl

omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Transition law for the automatically defined completed-to-finite semidirect maps. -/
theorem freeProCZCCompletedFoxSemidirectZCBifilteredStageMap_transition
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
    {i j : J} (hij : i ≤ j) :
    (finiteFoxStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp
      (freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j) =
    freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
      (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap i := by
  exact
    freeProCZCCompletedFoxSemidirectBifilteredStageMapOfCoeff_transition
      (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn
      (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
      (zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap)
      (fun k h => zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_autoRight
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k h)
      (fun hij a => zcCompletedGroupAlgebraBifilteredStageCoeffMap_transition
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex hmod qmap
        hcoeff_mod hqmap_transition hij a)
      (fun hij h => zcCompletedGroupAlgebraBifilteredStageRightMap_transition
        (ProC := ProC) (X := X) (H := H) (Nstage := Nstage) (hN := hN)
        (zcIndex := zcIndex) (hzcIndex := hzcIndex) (qmap := qmap) hqmap_transition hij h)
      hij


/-- The automatically defined `Z_C[[H]]` bifiltered stage maps assembled into the finite
semidirect inverse limit. -/
def freeProCZCCompletedFoxSemidirectZCBifilteredLimitMap
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
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q)) :
    ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →*
      FiniteFoxStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn :=
  freeProCZCCompletedFoxSemidirectBifilteredLimitMap
    (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn
    (fun j => freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
      (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j)
    (fun hij => freeProCZCCompletedFoxSemidirectZCBifilteredStageMap_transition
      (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
      hmod qmap hcoeff_mod hqmap_transition hij)

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
@[simp 900]
theorem freeProCZCCompletedFoxSemidirectZCBifilteredLimitMap_projection
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
    (j : J) (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    finiteFoxStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (freeProCZCCompletedFoxSemidirectZCBifilteredLimitMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
          hmod qmap hcoeff_mod hqmap_transition y) =
      freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j y :=
  rfl

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Completed density from actual `Z_C[[H]]` finite-stage projections, with the right maps
constructed from the same stage quotients rather than passed as separate data. -/
theorem boundaryCycles_subset_kernelClosure_of_zcBiStageProj
    [Fintype X] (φ : X → H)
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
    (hgenerators : ∀ j : J, ∀ x : X,
      qmap j (QuotientGroup.mk (φ x)) =
        QuotientGroup.mk' (Nstage j) (FreeGroup.of x))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
            (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_zcBiStageProj_relDeriv
      (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex hmod qmap φ
      (zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap)
      (fun _ _ => rfl)
      hcoeff_mod hqmap_transition
      (fun hij h => zcCompletedGroupAlgebraBifilteredStageRightMap_transition
        (ProC := ProC) (X := X) (H := H) (Nstage := Nstage) (hN := hN)
        (zcIndex := zcIndex) (hzcIndex := hzcIndex) (qmap := qmap) hqmap_transition hij h)
      (fun j x => zcCompletedGroupAlgebraBifilteredStageRightMap_generators
        (ProC := ProC) (X := X) (H := H) (Nstage := Nstage)
        (zcIndex := zcIndex) (qmap := qmap) hgenerators j x)
      hidentity_basis hNstage_kernel

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Completed graph-word density from actual `Z_C[[H]]` projections and automatic right maps.

This is the auto-right analogue of the graph-word density route; it removes the unsafe completed
kernel-word hypothesis from the finite-stage approximation step. -/
theorem boundaryCycles_subset_graphWordClosure_of_zcBiStageProj
    [Fintype X] (φ : X → H)
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
    (hgenerators : ∀ j : J, ∀ x : X,
      qmap j (QuotientGroup.mk (φ x)) =
        QuotientGroup.mk' (Nstage j) (FreeGroup.of x))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
            (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (ProC := ProC) φ) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_zcBiStageProj_relDeriv
      (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex hmod qmap φ
      (zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap)
      (fun _ _ => rfl)
      hcoeff_mod hqmap_transition
      (fun hij h => zcCompletedGroupAlgebraBifilteredStageRightMap_transition
        (ProC := ProC) (X := X) (H := H) (Nstage := Nstage) (hN := hN)
        (zcIndex := zcIndex) (hzcIndex := hzcIndex) (qmap := qmap) hqmap_transition hij h)
      (fun j x => zcCompletedGroupAlgebraBifilteredStageRightMap_generators
        (ProC := ProC) (X := X) (H := H) (Nstage := Nstage)
        (zcIndex := zcIndex) (qmap := qmap) hgenerators j x)
      hidentity_basis

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Closed-generated target membership from actual `Z_C[[H]]` projections and automatic right
maps, via graph-word density. -/
theorem boundaryCycles_subset_closedGenTarget_of_zcBiGraph
    [Fintype X] (φ : X → H)
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
    (hgenerators : ∀ j : J, ∀ x : X,
      qmap j (QuotientGroup.mk (φ x)) =
        QuotientGroup.mk' (Nstage j) (FreeGroup.of x))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
            (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j)) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density
      (ProC := ProC) φ
      (boundaryCycles_subset_graphWordClosure_of_zcBiStageProj
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
        hmod qmap φ hcoeff_mod hqmap_transition hgenerators hidentity_basis)

omit [∀ (j : J), Fact (0 < nstage j)] in
/-- Closed-generated target membership from actual `Z_C[[H]]` projections and automatic right
maps. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_zcBiStageProj_autoRight_relDeriv
    [Fintype X] (φ : X → H)
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
    (hgenerators : ∀ j : J, ∀ x : X,
      qmap j (QuotientGroup.mk (φ x)) =
        QuotientGroup.mk' (Nstage j) (FreeGroup.of x))
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
            (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j))
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
      (boundaryCycles_subset_kernelClosure_of_zcBiStageProj
        (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
        hmod qmap φ hcoeff_mod hqmap_transition hgenerators hidentity_basis hNstage_kernel)

end BifilteredRightMaps

end

end FoxDifferential
