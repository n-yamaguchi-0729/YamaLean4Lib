import FoxDifferential.Completed.Continuous.Topology
import FoxDifferential.Completed.ProCIntegerCoefficients.AugmentationIdeal.FiniteStage
import ProCGroups.InverseSystems.ProjectionImageSystems

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/ProCIntegerCoefficients/AugmentationIdeal/Closure.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed group algebra coefficients

This module records augmentation-ideal statements for pro-\(C\) integer completed coefficient rings, including closure, finite-stage membership, and kernel descriptions.
-/
namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.Completion
open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

section Closure

variable (C : ProCGroups.FiniteGroupClass.{u})
variable [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
  [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] [IsTopologicalGroup H] in
/-- The `Z_C[[H]]` finite-stage index is directed when both the coefficient and group-quotient
classes are directed by formation closure. -/
theorem directed_zcCompletedGroupAlgebraIndex
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    Directed (· ≤ ·) (id : ZCCompletedGroupAlgebraIndex C H → ZCCompletedGroupAlgebraIndex C H) := by
  intro i j
  rcases ProCIntegerIndex.directed_of_formation hForm i.1 j.1 with
    ⟨n, hin, hjn⟩
  rcases directed_openNormalSubgroupInClass
      (C := C) (G := H) hForm i.2 j.2 with
    ⟨U, hiU, hjU⟩
  exact ⟨(n, U), ⟨hin, hiU⟩, ⟨hjn, hjU⟩⟩

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
  [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] in
/-- Every finite-stage augmentation-ideal element is the projection of an element of the algebraic
standard augmentation ideal. -/
theorem zcCompletedGroupAlgebraStageAugmentationIdeal_mem_projection_standard
    (i : ZCCompletedGroupAlgebraIndex C H)
    (x : zcCompletedGroupAlgebraStageAugmentationIdeal C H i) :
    ∃ y ∈ zcCompletedGroupAlgebraStandardAugmentationIdeal C H,
      zcCompletedGroupAlgebraProjection C H i y = (x : ZCCompletedGroupAlgebraStage C H i) := by
  let P : zcCompletedGroupAlgebraStageAugmentationIdeal C H i → Prop := fun x =>
    ∃ y ∈ zcCompletedGroupAlgebraStandardAugmentationIdeal C H,
      zcCompletedGroupAlgebraProjection C H i y =
        (x : ZCCompletedGroupAlgebraStage C H i)
  have hxSpan :
      x ∈ Submodule.span (ZCCompletedGroupAlgebraStage C H i)
        (Set.range (zcCompletedGroupAlgebraStageAugmentationGeneratorSubtype C H i)) := by
    rw [zcCompletedGroupAlgebraStageAugmentationIdeal_span_standardGenerators_eq_top
      (C := C) (H := H) i]
    simp only [Submodule.mem_top]
  refine Submodule.span_induction (p := fun z _ => P z) ?_ ?_ ?_ ?_ hxSpan
  · rintro _ ⟨q, rfl⟩
    rcases QuotientGroup.mk'_surjective
        ((((OrderDual.ofDual i.2).1 : OpenNormalSubgroup H) : Subgroup H)) q with
      ⟨h, rfl⟩
    refine ⟨zcGroupLike C H h - 1,
      zcGroupLike_sub_one_mem_standardAugmentationIdeal C H h, ?_⟩
    simp only [zcCompletedGroupAlgebraProjection_sub, zcCompletedGroupAlgebraProjection_groupLike,
  MonoidAlgebra.of_apply, zcCompletedGroupAlgebraProjection_one,
  zcCompletedGroupAlgebraStageAugmentationGeneratorSubtype, zcCompletedGroupAlgebraStageAugmentationGenerator,
  QuotientGroup.mk'_apply]
  · exact ⟨0, (zcCompletedGroupAlgebraStandardAugmentationIdeal C H).zero_mem, by simp only [zcCompletedGroupAlgebraProjection_zero, ZeroMemClass.coe_zero]⟩
  · intro x y _ _ hx hy
    rcases hx with ⟨x', hx'mem, hx'proj⟩
    rcases hy with ⟨y', hy'mem, hy'proj⟩
    refine ⟨x' + y',
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C H).add_mem hx'mem hy'mem, ?_⟩
    simp only [zcCompletedGroupAlgebraProjection_add, hx'proj, hy'proj, Submodule.coe_add]
  · intro a x _ hx
    rcases hx with ⟨x', hx'mem, hx'proj⟩
    rcases zcCompletedGroupAlgebraProjection_surjective C H i a with ⟨a', ha'⟩
    refine ⟨a' * x',
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C H).mul_mem_left a' hx'mem, ?_⟩
    rw [zcCompletedGroupAlgebraProjection_mul, ha', hx'proj]
    rfl

/-- The completed augmentation ideal is the closure of the algebraic standard-generator ideal. -/
theorem closure_zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_augmentationIdeal
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    closure
        ((zcCompletedGroupAlgebraStandardAugmentationIdeal C H :
          Ideal (ZCCompletedGroupAlgebra C H)) : Set (ZCCompletedGroupAlgebra C H)) =
      ((zcCompletedGroupAlgebraAugmentationIdeal C H :
        Ideal (ZCCompletedGroupAlgebra C H)) : Set (ZCCompletedGroupAlgebra C H)) := by
  let S := zcCompletedGroupAlgebraSystem C H
  let Y : Set (ZCCompletedGroupAlgebra C H) :=
    (zcCompletedGroupAlgebraStandardAugmentationIdeal C H :
      Set (ZCCompletedGroupAlgebra C H))
  let Z : Set (ZCCompletedGroupAlgebra C H) :=
    (zcCompletedGroupAlgebraAugmentationIdeal C H :
      Set (ZCCompletedGroupAlgebra C H))
  letI : Nonempty (ZCCompletedGroupAlgebraIndex C H) :=
    ⟨(ProCIntegerIndex.terminal (C := C) inferInstance, zcCompletedGroupAlgebraTopIndex C H)⟩
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C H, TopologicalSpace (S.X i) := fun _ =>
    inferInstance
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C H, CompactSpace (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    infer_instance
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C H, T2Space (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    infer_instance
  have hdir : Directed (· ≤ ·) (id : ZCCompletedGroupAlgebraIndex C H →
      ZCCompletedGroupAlgebraIndex C H) :=
    directed_zcCompletedGroupAlgebraIndex (C := C) (H := H) hForm
  have hclosedZ : IsClosed Z := by
    simpa [Z] using isClosed_zcCompletedGroupAlgebraAugmentationIdeal (C := C) (G := H)
  refine le_antisymm ?_ ?_
  · exact closure_minimal
      (by
        intro x hx
        exact zcCompletedGroupAlgebraStandardAugmentationIdeal_le_augmentationIdeal C H hx)
      hclosedZ
  · intro z hz
    have hzClosure :
        z ∈ closure Y := by
      rw [S.mem_isClosed_iff_forall_projection_mem hdir isClosed_closure]
      intro i
      have hzi :
          zcCompletedGroupAlgebraProjection C H i z ∈
            zcCompletedGroupAlgebraStageAugmentationIdeal C H i := by
        let zAug : ZCCompletedGroupAlgebraAugmentationIdeal C H := ⟨z, by simpa [Z] using hz⟩
        simpa using
          (zcCompletedGroupAlgebraAugmentationIdealProjection C H i zAug).2
      rcases
        zcCompletedGroupAlgebraStageAugmentationIdeal_mem_projection_standard
          (C := C) (H := H) i
          ⟨zcCompletedGroupAlgebraProjection C H i z, hzi⟩ with
        ⟨y, hy, hyproj⟩
      refine ⟨y, subset_closure (by simpa [Y] using hy), ?_⟩
      exact hyproj
    simpa [Y] using hzClosure

end Closure

end

end FoxDifferential
