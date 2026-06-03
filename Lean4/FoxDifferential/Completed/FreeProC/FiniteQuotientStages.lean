import FoxDifferential.Completed.FreeProC.ProCIntegerBifilteredStageRightProjection
import ProCGroups.FiniteGeneration.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/FiniteQuotientStages.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite quotient stages for the completed Crowell approximation route

This file packages the honest finite quotient stages used by the graph-word density route.  Given
a finite quotient `H/U` and a family `X -> H`, the corresponding finite Fox relation subgroup is
the kernel of the free-group map `F_X -> H/U`.  When the family topologically generates `H`, this
map is surjective on every discrete quotient, so `H/U` is canonically identified with `F_X / ker`.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC
open ProCGroups.Completion

universe u v

section OneStage

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable {X H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The free-group map to a finite quotient of `H` induced by a family `X -> H`. -/
def freeProCFiniteQuotientStageHom
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C) :
    FreeGroup X →* CompletedGroupAlgebraQuotientInClass H C U :=
  FreeGroup.lift fun x : X =>
    openNormalSubgroupInClassProj (C := C) (G := H) U (φ x)

@[simp]
theorem freeProCFiniteQuotientStageHom_of
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C) (x : X) :
    freeProCFiniteQuotientStageHom (C := C) φ U (FreeGroup.of x) =
      (QuotientGroup.mk (φ x) :
        CompletedGroupAlgebraQuotientInClass H C U) := by
  simp only [freeProCFiniteQuotientStageHom, openNormalSubgroupInClassProj, QuotientGroup.mk'_apply,
  FreeGroup.lift_apply_of]

/-- The free quotient-stage map is the quotient projection after the original free-group map. -/
theorem freeProCFiniteQuotientStageHom_eq_comp
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C) :
    freeProCFiniteQuotientStageHom (C := C) φ U =
      (openNormalSubgroupInClassProj (C := C) (G := H) U).comp (FreeGroup.lift φ) := by
  ext x
  unfold freeProCFiniteQuotientStageHom
  rw [FreeGroup.lift_apply_of]
  change
    openNormalSubgroupInClassProj (C := C) (G := H) U (φ x) =
      openNormalSubgroupInClassProj (C := C) (G := H) U
        (FreeGroup.lift φ (FreeGroup.of x))
  rw [FreeGroup.lift_apply_of]

/-- Compatibility of finite quotient-stage maps under quotient refinement. -/
theorem freeProCFiniteQuotientStageHom_transition
    (φ : X → H) {U V : CompletedGroupAlgebraIndexInClass H C} (hUV : U ≤ V)
    (w : FreeGroup X) :
    (OpenNormalSubgroupInClass.map
      (C := C) (G := H)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (freeProCFiniteQuotientStageHom (C := C) φ V w) =
      freeProCFiniteQuotientStageHom (C := C) φ U w := by
  rw [freeProCFiniteQuotientStageHom_eq_comp,
    freeProCFiniteQuotientStageHom_eq_comp]
  exact congrFun
    (openNormalSubgroupInClassProj_compatible (C := C) (G := H) U V hUV)
    (FreeGroup.lift φ w)

/-- The finite-stage relation subgroup `ker(F_X -> H/U)`. -/
def freeProCFiniteQuotientStageKernel
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C) :
    Subgroup (FreeGroup X) :=
  (freeProCFiniteQuotientStageHom (C := C) φ U).ker

instance freeProCFiniteQuotientStageKernel_normal
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C) :
    (freeProCFiniteQuotientStageKernel (C := C) φ U).Normal := by
  dsimp [freeProCFiniteQuotientStageKernel]
  infer_instance

/-- The finite-stage relation kernels are antitone with respect to quotient refinement. -/
theorem freeProCFiniteQuotientStageKernel_antitone
    (φ : X → H) {U V : CompletedGroupAlgebraIndexInClass H C} (hUV : U ≤ V) :
    freeProCFiniteQuotientStageKernel (C := C) φ V ≤
      freeProCFiniteQuotientStageKernel (C := C) φ U := by
  intro w hw
  change freeProCFiniteQuotientStageHom (C := C) φ U w = 1
  calc
    freeProCFiniteQuotientStageHom (C := C) φ U w
        =
          (OpenNormalSubgroupInClass.map
            (C := C) (G := H)
            (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
            (freeProCFiniteQuotientStageHom (C := C) φ V w) :=
          (freeProCFiniteQuotientStageHom_transition (C := C) φ hUV w).symm
    _ = 1 := by
      rw [show freeProCFiniteQuotientStageHom (C := C) φ V w = 1 from hw]
      exact map_one _

/-- If the original family topologically generates `H`, then its image generates every discrete
finite quotient `H/U`, so the corresponding free-group map is surjective. -/
theorem freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    [DiscreteTopology (CompletedGroupAlgebraQuotientInClass H C U)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U) := by
  let π : H →ₜ* CompletedGroupAlgebraQuotientInClass H C U :=
    { toMonoidHom := openNormalSubgroupInClassProj (C := C) (G := H) U
      continuous_toFun := by
        change Continuous
          (QuotientGroup.mk'
            (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H))
        exact continuous_quotient_mk' }
  have hπsurj : Function.Surjective π :=
    openNormalSubgroupInClassProj_surjective (C := C) (G := H) U
  have hgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := CompletedGroupAlgebraQuotientInClass H C U)
        (Set.range (π ∘ φ)) :=
    ProCGroups.FiniteGeneration.topologicallyGenerates_range_comp_of_surjective
      (G := H) (H := CompletedGroupAlgebraQuotientInClass H C U)
      π hπsurj φ hφgen
  simpa [π, freeProCFiniteQuotientStageHom, Function.comp] using
    ProCGroups.FiniteGeneration.freeGroup_lift_surjective_of_topologicallyGenerates_discrete
      (G := CompletedGroupAlgebraQuotientInClass H C U)
      (g := fun x : X => π (φ x)) hgen

/-- The canonical identification `F_X / ker(F_X -> H/U) ≃ H/U`. -/
def freeProCFiniteQuotientStageTargetEquiv
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    (hsurj : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U)) :
    finiteFoxStageTargetQuotient
        (X := X) (freeProCFiniteQuotientStageKernel (C := C) φ U) ≃*
      CompletedGroupAlgebraQuotientInClass H C U :=
  QuotientGroup.quotientKerEquivOfSurjective
    (freeProCFiniteQuotientStageHom (C := C) φ U) hsurj

@[simp]
theorem freeProCFiniteQuotientStageTargetEquiv_mk
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    (hsurj : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U))
    (w : FreeGroup X) :
    freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurj
        (QuotientGroup.mk'
          (freeProCFiniteQuotientStageKernel (C := C) φ U) w) =
      freeProCFiniteQuotientStageHom (C := C) φ U w := by
  rfl

/-- The map `H/U -> F_X / ker(F_X -> H/U)` used as `qmap` in the bifiltered stage API. -/
def freeProCFiniteQuotientStageQMap
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    (hsurj : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U)) :
    CompletedGroupAlgebraQuotientInClass H C U →*
      finiteFoxStageTargetQuotient
        (X := X) (freeProCFiniteQuotientStageKernel (C := C) φ U) :=
  (freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurj).symm.toMonoidHom

theorem freeProCFiniteQuotientStageQMap_injective
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    (hsurj : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U)) :
    Function.Injective (freeProCFiniteQuotientStageQMap (C := C) φ U hsurj) :=
  (freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurj).symm.injective

@[simp]
theorem freeProCFiniteQuotientStageQMap_generator
    (φ : X → H) (U : CompletedGroupAlgebraIndexInClass H C)
    (hsurj : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U))
    (x : X) :
    freeProCFiniteQuotientStageQMap (C := C) φ U hsurj
        (QuotientGroup.mk (φ x)) =
      QuotientGroup.mk'
        (freeProCFiniteQuotientStageKernel (C := C) φ U) (FreeGroup.of x) := by
  apply (freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurj).injective
  rw [freeProCFiniteQuotientStageTargetEquiv_mk]
  simp only [freeProCFiniteQuotientStageQMap, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
  MulEquiv.apply_symm_apply, freeProCFiniteQuotientStageHom_of]

/-- Compatibility between the canonical `F_X/ker -> H/U` equivalences and quotient refinement. -/
theorem freeProCFiniteQuotientStageTargetEquiv_transition
    (φ : X → H) {U V : CompletedGroupAlgebraIndexInClass H C} (hUV : U ≤ V)
    (hsurjU : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U))
    (hsurjV : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ V))
    (y : finiteFoxStageTargetQuotient
      (X := X) (freeProCFiniteQuotientStageKernel (C := C) φ V)) :
    freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurjU
        (finiteFoxStageTargetQuotientMap
          (X := X) (freeProCFiniteQuotientStageKernel_antitone (C := C) φ hUV) y) =
      (OpenNormalSubgroupInClass.map
        (C := C) (G := H)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (freeProCFiniteQuotientStageTargetEquiv (C := C) φ V hsurjV y) := by
  rcases QuotientGroup.mk'_surjective
      (freeProCFiniteQuotientStageKernel (C := C) φ V) y with ⟨w, rfl⟩
  rw [finiteFoxStageTargetQuotientMap_mk,
    freeProCFiniteQuotientStageTargetEquiv_mk,
    freeProCFiniteQuotientStageTargetEquiv_mk,
    freeProCFiniteQuotientStageHom_transition]

/-- The canonical `qmap`s commute with quotient refinement. -/
theorem freeProCFiniteQuotientStageQMap_transition
    (φ : X → H) {U V : CompletedGroupAlgebraIndexInClass H C} (hUV : U ≤ V)
    (hsurjU : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ U))
    (hsurjV : Function.Surjective (freeProCFiniteQuotientStageHom (C := C) φ V))
    (q : CompletedGroupAlgebraQuotientInClass H C V) :
    freeProCFiniteQuotientStageQMap (C := C) φ U hsurjU
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := H)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) =
      finiteFoxStageTargetQuotientMap
        (X := X) (freeProCFiniteQuotientStageKernel_antitone (C := C) φ hUV)
        (freeProCFiniteQuotientStageQMap (C := C) φ V hsurjV q) := by
  apply (freeProCFiniteQuotientStageTargetEquiv (C := C) φ U hsurjU).injective
  rw [freeProCFiniteQuotientStageTargetEquiv_transition
    (C := C) φ hUV hsurjU hsurjV]
  simp only [freeProCFiniteQuotientStageQMap, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
  MulEquiv.apply_symm_apply]

end OneStage

section StageFamily

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable {X H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {J : Type v}

/-- The finite relation subgroup family attached to a family of `Z_C[[H]]` stage indices. -/
def freeProCFiniteQuotientStageKernelFamily
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H) :
    J → Subgroup (FreeGroup X) :=
  fun j => freeProCFiniteQuotientStageKernel (C := C) φ (zcIndex j).2

instance freeProCFiniteQuotientStageKernelFamily_normal
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H) (j : J) :
    (freeProCFiniteQuotientStageKernelFamily (C := C) φ zcIndex j).Normal := by
  dsimp [freeProCFiniteQuotientStageKernelFamily]
  infer_instance

/-- The finite relation subgroup family is antitone under refinement of the `Z_C[[H]]` stages. -/
theorem freeProCFiniteQuotientStageKernelFamily_antitone
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
    [Preorder J]
    (hzcIndex : ∀ {i j : J}, i ≤ j → zcIndex i ≤ zcIndex j) :
    ∀ {i j : J}, i ≤ j →
      freeProCFiniteQuotientStageKernelFamily (C := C) φ zcIndex j ≤
        freeProCFiniteQuotientStageKernelFamily (C := C) φ zcIndex i := by
  intro i j hij
  exact freeProCFiniteQuotientStageKernel_antitone (C := C) φ (hzcIndex hij).2

/-- The canonical `H/U_j -> F/N_j` comparison maps for a finite quotient stage family. -/
def freeProCFiniteQuotientStageQMapFamily
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
    [∀ j, DiscreteTopology (CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    ∀ j : J,
      CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2 →*
        finiteFoxStageTargetQuotient
          (X := X) (freeProCFiniteQuotientStageKernelFamily (C := C) φ zcIndex j) :=
  fun j =>
    freeProCFiniteQuotientStageQMap (C := C) φ (zcIndex j).2
      (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
        (C := C) φ (zcIndex j).2 hφgen)

theorem freeProCFiniteQuotientStageQMapFamily_injective
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
    [∀ j, DiscreteTopology (CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    ∀ j : J,
      Function.Injective
        (freeProCFiniteQuotientStageQMapFamily (C := C) φ zcIndex hφgen j) := by
  intro j
  exact freeProCFiniteQuotientStageQMap_injective (C := C) φ (zcIndex j).2
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := C) φ (zcIndex j).2 hφgen)

@[simp]
theorem freeProCFiniteQuotientStageQMapFamily_generator
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
    [∀ j, DiscreteTopology (CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ))
    (j : J) (x : X) :
    freeProCFiniteQuotientStageQMapFamily (C := C) φ zcIndex hφgen j
        (QuotientGroup.mk (φ x)) =
      QuotientGroup.mk'
        (freeProCFiniteQuotientStageKernelFamily (C := C) φ zcIndex j)
        (FreeGroup.of x) := by
  exact freeProCFiniteQuotientStageQMap_generator (C := C) φ (zcIndex j).2
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := C) φ (zcIndex j).2 hφgen) x

/-- The canonical comparison maps commute with refinement of the `Z_C[[H]]` stage family. -/
theorem freeProCFiniteQuotientStageQMapFamily_transition
    (φ : X → H) (zcIndex : J → ZCCompletedGroupAlgebraIndex C H)
    [Preorder J]
    (hzcIndex : ∀ {i j : J}, i ≤ j → zcIndex i ≤ zcIndex j)
    [∀ j, DiscreteTopology (CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H C (zcIndex j).2,
        freeProCFiniteQuotientStageQMapFamily (C := C) φ zcIndex hφgen i
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap
            (X := X)
            (freeProCFiniteQuotientStageKernelFamily_antitone
              (C := C) φ zcIndex hzcIndex hij)
            (freeProCFiniteQuotientStageQMapFamily (C := C) φ zcIndex hφgen j q) := by
  intro i j hij q
  exact freeProCFiniteQuotientStageQMap_transition (C := C) φ (hzcIndex hij).2
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := C) φ (zcIndex i).2 hφgen)
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := C) φ (zcIndex j).2 hφgen)
    q

end StageFamily

section BifilteredFiniteQuotientStages

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable {J : Type v} [Preorder J]

/-- The completed-to-finite coefficient map for the actual finite quotient stages
`F_X -> H/U_j`. -/
def freeProCZCBifilteredFiniteQuotientStageCoeffMap
    (φ : X → H) (nstage : J → ℕ) [∀ j, Fact (0 < nstage j)]
    (zcIndex : J → ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H)
    (hmod : ∀ j : J, nstage j ∣ (zcIndex j).1.modulus)
    [∀ j, DiscreteTopology
      (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2)]
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ))
    (j : J) :
    ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
      finiteFoxStageTargetGroupAlgebra
        (X := X)
        (freeProCFiniteQuotientStageKernelFamily
          (C := ProC.finiteQuotientClass) φ zcIndex j)
        (nstage j) :=
  zcCompletedGroupAlgebraBifilteredStageCoeffMap
    (ProC := ProC) (X := X) (H := H)
    (freeProCFiniteQuotientStageKernelFamily
      (C := ProC.finiteQuotientClass) φ zcIndex)
    nstage zcIndex hmod
    (freeProCFiniteQuotientStageQMapFamily
      (C := ProC.finiteQuotientClass) φ zcIndex hφgen) j

/-- The completed-to-finite coefficient map for the standard all-stage family
`j : ZCCompletedGroupAlgebraIndex C H`, with finite relation subgroup
`ker(F_X -> H/U_j)` and coefficient modulus `j.1.modulus`. -/
def freeProCZCBifilteredAllFiniteQuotientStageCoeffMap
    (φ : X → H)
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ))
    (j : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) :
    ZCCompletedGroupAlgebra ProC.finiteQuotientClass H →+*
      finiteFoxStageTargetGroupAlgebra
        (X := X)
        (freeProCFiniteQuotientStageKernelFamily
          (C := ProC.finiteQuotientClass) φ
          (id : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H →
            ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H) j)
        j.1.modulus := by
  letI :
      ∀ j : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H,
        Fact (0 < j.1.modulus) :=
    fun j => ProCIntegerIndex.positiveFact j.1
  letI :
      ∀ j : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H,
        DiscreteTopology
          (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.2) :=
    fun j =>
      QuotientGroup.discreteTopology
        (ProCGroups.openNormalSubgroup_isOpen (G := H)
          ((OrderDual.ofDual j.2).1 : OpenNormalSubgroup H))
  exact
    freeProCZCBifilteredFiniteQuotientStageCoeffMap
      (ProC := ProC) (X := X) (H := H) φ (fun j => j.1.modulus)
      (id : ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H →
        ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H)
      (fun _ => dvd_rfl) hφgen j

end BifilteredFiniteQuotientStages

section FullStageQuotientBasis

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable {H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [IsTopologicalGroup H] in
/-- The full family of quotient maps `H -> H/U` indexed by
`ZCCompletedGroupAlgebraIndex C H` has identity-neighbourhood kernels for any pro-`C` group `H`.

The coefficient coordinate of the index is irrelevant here; it is filled with the terminal
coefficient quotient. -/
theorem zcCompletedGroupAlgebraAllStageQuotientMap_identity_basis_of_isProCGroup
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hH : IsProCGroup C H) :
    HasIdentityQuotientKernelNeighbourhoodBasis
      (Y := H)
      (fun j : ZCCompletedGroupAlgebraIndex C H =>
        openNormalSubgroupInClassProj (C := C) (G := H) j.2) := by
  intro U hU hUone
  rcases hH.hasOpenNormalBasisInClass U hU hUone with ⟨V, hVU, hCV⟩
  let Vc : OpenNormalSubgroupInClass C H := ⟨V, hCV⟩
  refine ⟨(ProCIntegerIndex.terminal (C := C) inferInstance, OrderDual.toDual Vc), ?_⟩
  intro z hz
  apply hVU
  exact
    (QuotientGroup.eq_one_iff
      (N := ((V : OpenNormalSubgroup H) : Subgroup H)) z).1 hz

end FullStageQuotientBasis

end

end FoxDifferential
