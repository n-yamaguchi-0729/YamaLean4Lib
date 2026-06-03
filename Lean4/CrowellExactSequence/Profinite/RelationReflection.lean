import FoxDifferential.Completed.FreeProC.FiniteQuotientStages
import FoxDifferential.Completed.Continuous.Universal.NaturalTopology
import CrowellExactSequence.Profinite.FreeProCSourceData

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/RelationReflection.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free-source finite relation reflection

This file isolates the non-circular finite-relation reflection route for finite-rank free
pro-`C` sources.  The root Crowell exactness file should only import this once the reflection
frontier theorem is proved here.
-/

namespace CrowellExactSequence

noncomputable section

open scoped Topology
open ProCGroups.InverseSystems
open ProCGroups.ProC
open FoxDifferential

universe u v


/-- A pre-stage reduction is a finite relation exactly when its finite universal-module class is
zero. -/
theorem zcCompletedDifferentialModulePreStageMap_relation_iff_stage_mkQ_eq_zero
    (C : ProCGroups.FiniteGroupClass.{u})
    {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (ψ : G →* H)
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :
    zcCompletedDifferentialModulePreStageMap C ψ i x ∈
        crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i) ↔
      ((crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
        (zcCompletedDifferentialModulePreStageMap C ψ i x) = 0) := by
  constructor
  · intro hx
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i))
        (x := zcCompletedDifferentialModulePreStageMap C ψ i x)).2 hx
  · intro hx
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i))
        (x := zcCompletedDifferentialModulePreStageMap C ψ i x)).1 hx


section FreeRelationReflection

variable {ProC : ProCGroups.ProC.ProCGroupPredicate.{u}}
variable {H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [T2Space H]
variable [ProC.HasFiniteQuotientFormation]
variable [ProC.HasFiniteQuotientFinite]
variable [ProC.HasFiniteQuotientHereditary]
variable [ProC.HasFiniteQuotientMelnikovFormation]
variable [ProC.DeterminedByFiniteQuotients]

omit [T2Space H] [ProC.HasFiniteQuotientFinite] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients] in
/-- Nonempty finite stage index set for a continuous map out of a free pro-`C` group. -/
theorem freeProC_zcCompletedDifferentialModuleIndex_nonempty
    (sourceData : FreeProCSourceData ProC)
    (psi : ContinuousMonoidHom sourceData.carrier H) :
    Nonempty
      (ZCCompletedDifferentialModuleIndex
        ProC.finiteQuotientClass psi.toMonoidHom) := by
  exact ⟨zcCompletedDifferentialModuleComapIndex
    (C := ProC.finiteQuotientClass) (G := sourceData.carrier) (H := H)
    (ProCGroupPredicate.finiteQuotientHereditary ProC) psi
    ((ProCGroups.Completion.ProCIntegerIndex.terminal
        (C := ProC.finiteQuotientClass) inferInstance),
      zcCompletedGroupAlgebraTopIndex ProC.finiteQuotientClass H)⟩

omit [T2Space H] [ProC.HasFiniteQuotientFinite] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients] in
/-- Directedness of source/target/coefficient finite stages. -/
theorem freeProC_directed_zcCompletedDifferentialModuleIndex
    (sourceData : FreeProCSourceData ProC)
    (psi : ContinuousMonoidHom sourceData.carrier H) :
    Directed (· ≤ ·)
      (id :
        ZCCompletedDifferentialModuleIndex
            ProC.finiteQuotientClass psi.toMonoidHom →
          ZCCompletedDifferentialModuleIndex
            ProC.finiteQuotientClass psi.toMonoidHom) :=
  directed_zcCompletedDifferentialModuleIndex
    (C := ProC.finiteQuotientClass) (G := sourceData.carrier) (H := H)
    (ProCGroupPredicate.finiteQuotientFormation ProC)
    (ProCGroupPredicate.finiteQuotientHereditary ProC) psi

/-- Chosen universe-lifted finite free basis. Use this exact family in reflection proofs. -/
abbrev freeProCReflectionFamily
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r) : ULift.{u} (Fin r) → sourceData.carrier :=
  freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis

omit [T2Space H] [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients] in
/-- The target images of the chosen basis topologically generate a surjective target. -/
theorem freeProCReflectionFamily_target_generates
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    ProCGroups.Generation.TopologicallyGenerates
      (G := H)
      (Set.range (fun i : ULift.{u} (Fin r) =>
        psi (freeProCReflectionFamily (ProC := ProC) sourceData hbasis i))) := by
  simpa [freeProCReflectionFamily] using
    freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
      (ProC := ProC) sourceData hbasis psi hpsi

/-- The free-group map onto the source quotient used by a differential-module finite stage. -/
def freeProCRelationReflectionStageSourceHom
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom) :
    FreeGroup (ULift.{u} (Fin r)) →*
      zcCompletedDifferentialModuleStageSource
        ProC.finiteQuotientClass psi.toMonoidHom i :=
  (zcCompletedDifferentialModuleStageSourceProj
      ProC.finiteQuotientClass psi.toMonoidHom i).comp
    (FreeGroup.lift (freeProCReflectionFamily (ProC := ProC) sourceData hbasis))

/-- The source kernel used by a differential-module stage, pulled back to the abstract free group
on the chosen basis. -/
def freeProCRelationReflectionStageKernel
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom) :
    Subgroup (FreeGroup (ULift.{u} (Fin r))) :=
  MonoidHom.ker
    (freeProCRelationReflectionStageSourceHom (ProC := ProC) sourceData hbasis psi i)

instance freeProCRelationReflectionStageKernel_normal
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom) :
    (freeProCRelationReflectionStageKernel (ProC := ProC) sourceData hbasis psi i).Normal := by
  dsimp [freeProCRelationReflectionStageKernel]
  infer_instance

omit [IsTopologicalGroup H] [T2Space H] [ProC.HasFiniteQuotientFormation]
    [ProC.HasFiniteQuotientFinite] [ProC.HasFiniteQuotientHereditary]
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.DeterminedByFiniteQuotients] in
/-- The chosen free basis surjects onto every finite source quotient stage. -/
theorem freeProCRelationReflectionStageSourceHom_surjective
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom) :
    Function.Surjective
      (freeProCRelationReflectionStageSourceHom (ProC := ProC) sourceData hbasis psi i) := by
  classical
  let X : Type u := ULift.{u} (Fin r)
  let ι : X → sourceData.carrier := freeProCReflectionFamily (ProC := ProC) sourceData hbasis
  let Q : Type u :=
    zcCompletedDifferentialModuleStageSource
      ProC.finiteQuotientClass psi.toMonoidHom i
  letI : DiscreteTopology Q :=
    QuotientGroup.discreteTopology i.source.1.toOpenSubgroup.isOpen'
  let g : X → Q := fun x =>
    zcCompletedDifferentialModuleStageSourceProj
      ProC.finiteQuotientClass psi.toMonoidHom i (ι x)
  have hsource :
      ProCGroups.Generation.TopologicallyGenerates
        (G := sourceData.carrier) (Set.range ι) := by
    simpa [ι, freeProCReflectionFamily] using
      freeProCChosenULiftFamilyOfBasisCard_generates (ProC := ProC) sourceData hbasis
  have hquot_image :
      ProCGroups.Generation.TopologicallyGenerates
        (G := Q)
        ((QuotientGroup.mk' (i.source.1 : Subgroup sourceData.carrier)) '' Set.range ι) := by
    simpa [Q] using
      ProCGroups.Generation.topologicallyGenerates_quotient_image
        (G := sourceData.carrier) (N := (i.source.1 : Subgroup sourceData.carrier)) hsource
  have hrange :
      ((QuotientGroup.mk' (i.source.1 : Subgroup sourceData.carrier)) '' Set.range ι) =
        Set.range g := by
    ext y
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨ι a, ⟨a, rfl⟩, rfl⟩
  have hg :
      ProCGroups.Generation.TopologicallyGenerates (G := Q) (Set.range g) := by
    rw [← hrange]
    exact hquot_image
  have hsurj : Function.Surjective (FreeGroup.lift g) :=
    ProCGroups.FiniteGeneration.freeGroup_lift_surjective_of_topologicallyGenerates_discrete
      (G := Q) g hg
  have hlift :
      FreeGroup.lift g =
        freeProCRelationReflectionStageSourceHom (ProC := ProC) sourceData hbasis psi i := by
    apply FreeGroup.ext_hom
    intro x
    rw [FreeGroup.lift_apply_of]
    change
      zcCompletedDifferentialModuleStageSourceProj
        ProC.finiteQuotientClass psi.toMonoidHom i (ι x) =
      zcCompletedDifferentialModuleStageSourceProj
        ProC.finiteQuotientClass psi.toMonoidHom i
        ((FreeGroup.lift (freeProCReflectionFamily (ProC := ProC) sourceData hbasis))
          (FreeGroup.of x))
    rw [FreeGroup.lift_apply_of]
  simpa [hlift] using hsurj

/-- Identification of the source quotient stage with the corresponding free-group quotient. -/
def freeProCRelationReflectionStageSourceEquiv
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom) :
    finiteFoxStageTargetQuotient
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionStageKernel (ProC := ProC) sourceData hbasis psi i) ≃*
      zcCompletedDifferentialModuleStageSource
        ProC.finiteQuotientClass psi.toMonoidHom i :=
  QuotientGroup.quotientKerEquivOfSurjective
    (freeProCRelationReflectionStageSourceHom (ProC := ProC) sourceData hbasis psi i)
    (freeProCRelationReflectionStageSourceHom_surjective
      (ProC := ProC) sourceData hbasis psi i)

omit [IsTopologicalGroup H] [T2Space H] [ProC.HasFiniteQuotientFormation]
    [ProC.HasFiniteQuotientFinite] [ProC.HasFiniteQuotientHereditary]
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.DeterminedByFiniteQuotients] in
@[simp]
theorem freeProCRelationReflectionStageSourceEquiv_mk
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom)
    (w : FreeGroup (ULift.{u} (Fin r))) :
    freeProCRelationReflectionStageSourceEquiv (ProC := ProC) sourceData hbasis psi i
        (QuotientGroup.mk'
          (freeProCRelationReflectionStageKernel (ProC := ProC) sourceData hbasis psi i) w) =
      freeProCRelationReflectionStageSourceHom (ProC := ProC) sourceData hbasis psi i w :=
  rfl

/-- The target finite Fox relation kernel attached to the target quotient of a
`ZCCompletedDifferentialModuleIndex`. -/
abbrev freeProCRelationReflectionTargetStageKernel
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom) :
    Subgroup (FreeGroup (ULift.{u} (Fin r))) :=
  freeProCFiniteQuotientStageKernel
    (C := ProC.finiteQuotientClass)
    (fun x : ULift.{u} (Fin r) =>
      psi (freeProCReflectionFamily (ProC := ProC) sourceData hbasis x))
    i.target.2

instance freeProCRelationReflectionTargetStageKernel_normal
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom) :
    (freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i).Normal :=
  inferInstance

omit [T2Space H] [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients] in
/-- Target finite Fox kernels are antitone along differential-module stage refinement. -/
theorem freeProCRelationReflectionTargetStageKernel_antitone
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    {i j : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom} (hij : i ≤ j) :
    freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi j ≤
      freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i := by
  exact freeProCFiniteQuotientStageKernel_antitone
    (C := ProC.finiteQuotientClass)
    (fun x : ULift.{u} (Fin r) =>
      psi (freeProCReflectionFamily (ProC := ProC) sourceData hbasis x))
    hij.2.2

/-- The canonical target quotient comparison map `H/U_i -> F_X/N_i`. -/
def freeProCRelationReflectionTargetStageQMap
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom) :
    CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.target.2 →*
      finiteFoxStageTargetQuotient
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i) := by
  let φ : ULift.{u} (Fin r) → H := fun x =>
    psi (freeProCReflectionFamily (ProC := ProC) sourceData hbasis x)
  have hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ) := by
    simpa [φ] using
      freeProCReflectionFamily_target_generates (ProC := ProC) sourceData hbasis psi hpsi
  letI : DiscreteTopology
      (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.target.2) :=
    QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen (G := H)
        ((OrderDual.ofDual i.target.2).1 : OpenNormalSubgroup H))
  exact freeProCFiniteQuotientStageQMap
    (C := ProC.finiteQuotientClass) φ i.target.2
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := ProC.finiteQuotientClass) φ i.target.2 hφgen)

omit [T2Space H] [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients] in
@[simp 900]
theorem freeProCRelationReflectionTargetStageQMap_generator
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom)
    (x : ULift.{u} (Fin r)) :
    freeProCRelationReflectionTargetStageQMap (ProC := ProC) sourceData hbasis psi hpsi i
        (QuotientGroup.mk
          (psi (freeProCReflectionFamily (ProC := ProC) sourceData hbasis x))) =
      QuotientGroup.mk'
        (freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i)
        (FreeGroup.of x) := by
  let φ : ULift.{u} (Fin r) → H := fun x =>
    psi (freeProCReflectionFamily (ProC := ProC) sourceData hbasis x)
  change
    freeProCRelationReflectionTargetStageQMap
        (ProC := ProC) sourceData hbasis psi hpsi i (QuotientGroup.mk (φ x)) =
      QuotientGroup.mk'
        (freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i)
        (FreeGroup.of x)
  unfold freeProCRelationReflectionTargetStageQMap
  simp only [freeProCFiniteQuotientStageQMap_generator,
    freeProCRelationReflectionTargetStageKernel, ContinuousMonoidHom.coe_toMonoidHom,
    QuotientGroup.mk'_apply, φ]

omit [T2Space H] [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients] in
/-- Target quotient comparison maps commute with differential-module stage refinement. -/
theorem freeProCRelationReflectionTargetStageQMap_transition
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    {i j : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom} (hij : i ≤ j)
    (q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.target.2) :
    freeProCRelationReflectionTargetStageQMap (ProC := ProC) sourceData hbasis psi hpsi i
        ((OpenNormalSubgroupInClass.map
          (C := ProC.finiteQuotientClass) (G := H)
          (U := OrderDual.ofDual i.target.2)
          (V := OrderDual.ofDual j.target.2) hij.2.2) q) =
      finiteFoxStageTargetQuotientMap
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionTargetStageKernel_antitone
          (ProC := ProC) sourceData hbasis psi hij)
        (freeProCRelationReflectionTargetStageQMap
          (ProC := ProC) sourceData hbasis psi hpsi j q) := by
  let φ : ULift.{u} (Fin r) → H := fun x =>
    psi (freeProCReflectionFamily (ProC := ProC) sourceData hbasis x)
  have hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ) := by
    simpa [φ] using
      freeProCReflectionFamily_target_generates (ProC := ProC) sourceData hbasis psi hpsi
  letI : DiscreteTopology
      (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass i.target.2) :=
    QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen (G := H)
        ((OrderDual.ofDual i.target.2).1 : OpenNormalSubgroup H))
  letI : DiscreteTopology
      (CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass j.target.2) :=
    QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen (G := H)
        ((OrderDual.ofDual j.target.2).1 : OpenNormalSubgroup H))
  unfold freeProCRelationReflectionTargetStageQMap
  exact freeProCFiniteQuotientStageQMap_transition
    (C := ProC.finiteQuotientClass) φ hij.2.2
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := ProC.finiteQuotientClass) φ i.target.2 hφgen)
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := ProC.finiteQuotientClass) φ j.target.2 hφgen)
    q

/-- The target component map used by finite Fox semidirect stages. -/
def freeProCRelationReflectionTargetStageRight
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom) :
    H →* finiteFoxStageTargetQuotient
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i) :=
  (freeProCRelationReflectionTargetStageQMap
    (ProC := ProC) sourceData hbasis psi hpsi i).comp
    (openNormalSubgroupInClassProj
      (C := ProC.finiteQuotientClass) (G := H) i.target.2)

omit [T2Space H] [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients] in
@[simp 900]
theorem freeProCRelationReflectionTargetStageRight_generator
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom)
    (x : ULift.{u} (Fin r)) :
    freeProCRelationReflectionTargetStageRight (ProC := ProC) sourceData hbasis psi hpsi i
        (psi (freeProCReflectionFamily (ProC := ProC) sourceData hbasis x)) =
      QuotientGroup.mk'
        (freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i)
        (FreeGroup.of x) := by
  change
    freeProCRelationReflectionTargetStageQMap
        (ProC := ProC) sourceData hbasis psi hpsi i
        (QuotientGroup.mk
          (psi (freeProCReflectionFamily (ProC := ProC) sourceData hbasis x))) =
      QuotientGroup.mk'
        (freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i)
        (FreeGroup.of x)
  exact freeProCRelationReflectionTargetStageQMap_generator
    (ProC := ProC) sourceData hbasis psi hpsi i x

/-- The finite Fox semidirect projection attached to one target quotient stage. -/
def freeProCRelationReflectionTargetStageMap
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom) :
    ZCCompletedFoxSemidirect ProC.finiteQuotientClass (ULift.{u} (Fin r)) H →*
      FiniteFoxStageSemidirect
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i)
        i.target.1.modulus := by
  letI : ∀ j : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom,
      Fact (0 < j.target.1.modulus) :=
    fun j => ProCGroups.Completion.ProCIntegerIndex.positiveFact j.target.1
  exact
    freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
      (ProC := ProC) (X := ULift.{u} (Fin r)) (H := H)
      (Nstage := fun j =>
        freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi j)
      (nstage := fun j => j.target.1.modulus)
      (zcIndex := fun j => j.target)
      (hmod := fun _ => dvd_rfl)
      (qmap := fun j =>
        freeProCRelationReflectionTargetStageQMap
          (ProC := ProC) sourceData hbasis psi hpsi j)
      i

omit [T2Space H] [ProC.HasFiniteQuotientFormation] [ProC.HasFiniteQuotientFinite]
    [ProC.HasFiniteQuotientHereditary] [ProC.HasFiniteQuotientMelnikovFormation]
    [ProC.DeterminedByFiniteQuotients] in
/-- Each target finite stage attached to the chosen free pro-`C` basis satisfies the finite Fox
relation-boundary module exactness needed by the approximation theorem. -/
theorem freeProCRelationReflection_finiteStage_relationBoundaryModuleExact
    (sourceData : FreeProCSourceData ProC) {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      ProC.finiteQuotientClass psi.toMonoidHom) :
    finiteFoxStageRelationBoundaryModuleExact
      (X := ULift.{u} (Fin r))
      (freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i)
      i.target.1.modulus := by
  exact
    finiteFoxStageRelationBoundaryModuleExact_of_sourceBoundaryRelReduction
      (X := ULift.{u} (Fin r))
      (freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i)
      i.target.1.modulus
      (finiteFoxStageSourceBoundaryRelationIdealReduction_of_relationIdeal_derivatives
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionTargetStageKernel (ProC := ProC) sourceData hbasis psi i)
        i.target.1.modulus)

end FreeRelationReflection

end

end CrowellExactSequence
