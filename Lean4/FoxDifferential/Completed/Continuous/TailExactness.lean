import FoxDifferential.Completed.ProCIntegerCoefficients.AugmentationIdeal.Closure

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Continuous/TailExactness.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Continuous crossed differentials

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.Generation

universe u v

section TailExactness

variable (C : ProCGroups.FiniteGroupClass.{u})
variable [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
variable [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
variable {X : Type v} [Fintype X] [DecidableEq X]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- If a finite family topologically generates `H`, the corresponding completed finite Fox
boundary is exact at `Z_C[[H]]`. -/
theorem exact_foxBoundaryMap_zcGroupLike_sub_one_of_topologicallyGenerates
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (φ : X → H) (hφ : TopologicallyGenerates (G := H) (Set.range φ)) :
    Function.Exact
      (foxBoundaryMap (fun x : X => zcGroupLike C H (φ x) - 1) :
        (X → ZCCompletedGroupAlgebra C H) → ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H → ZCCoeff C) := by
  let L : (X → ZCCompletedGroupAlgebra C H) →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebra C H :=
    foxBoundaryMap (fun x : X => zcGroupLike C H (φ x) - 1)
  have hclosedRange :
      IsClosed ((LinearMap.range L : Submodule (ZCCompletedGroupAlgebra C H)
        (ZCCompletedGroupAlgebra C H)) : Set (ZCCompletedGroupAlgebra C H)) := by
    change IsClosed (Set.range L)
    have hrange :
        Set.range L = (fun v : X → ZCCompletedGroupAlgebra C H => L v) '' Set.univ := by
      ext y
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨v, trivial, rfl⟩
      · rintro ⟨v, _hv, rfl⟩
        exact ⟨v, rfl⟩
    rw [hrange]
    simpa [L] using
      (isCompact_univ.image (continuous_foxBoundaryMap
        (fun x : X => zcGroupLike C H (φ x) - 1))).isClosed
  let K : Subgroup H :=
    { carrier := {h | zcGroupLike C H h - 1 ∈ LinearMap.range L}
      one_mem' := by
        change zcCompletedGroupAlgebraBoundary C (MonoidHom.id H) (1 : H) ∈
          LinearMap.range L
        simp only [MonoidHom.id_apply, zcCompletedGroupAlgebraBoundary_eq_zero_of_mem_ker, zero_mem]
      mul_mem' := by
        intro a b ha hb
        change zcCompletedGroupAlgebraBoundary C (MonoidHom.id H) (a * b) ∈
          LinearMap.range L
        rw [zcCompletedGroupAlgebraBoundary_mul]
        exact (LinearMap.range L).add_mem ha ((LinearMap.range L).smul_mem _ hb)
      inv_mem' := by
        intro a ha
        change zcCompletedGroupAlgebraBoundary C (MonoidHom.id H) a⁻¹ ∈
          LinearMap.range L
        rw [zcCompletedGroupAlgebraBoundary_inv]
        exact (LinearMap.range L).neg_mem ((LinearMap.range L).smul_mem _ ha) }
  have hKclosed : IsClosed ((K : Subgroup H) : Set H) := by
    change IsClosed {h : H | zcGroupLike C H h - 1 ∈
      (LinearMap.range L : Submodule (ZCCompletedGroupAlgebra C H)
        (ZCCompletedGroupAlgebra C H))}
    exact hclosedRange.preimage
      ((continuous_zcGroupLike (C := C) (G := H)).sub continuous_const)
  have hsub : Subgroup.closure (Set.range φ) ≤ K := by
    rw [Subgroup.closure_le]
    rintro h ⟨x, rfl⟩
    change zcGroupLike C H (φ x) - 1 ∈ LinearMap.range L
    exact ⟨Pi.single x (1 : ZCCompletedGroupAlgebra C H), by
      simp only [foxBoundaryMap_single, L]⟩
  have htop : (⊤ : Subgroup H) ≤ K := by
    have hcl : (Subgroup.closure (Set.range φ)).topologicalClosure ≤ K :=
      Subgroup.topologicalClosure_minimal _ hsub hKclosed
    rw [TopologicallyGenerates] at hφ
    simpa [hφ] using hcl
  have hstandard_le_range :
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C H :
        Submodule (ZCCompletedGroupAlgebra C H) (ZCCompletedGroupAlgebra C H)) ≤
        LinearMap.range L := by
    rw [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    simpa [K, zcCompletedGroupAlgebraBoundary] using
      htop (show h ∈ (⊤ : Subgroup H) from by simp only [Subgroup.mem_top])
  have hrange_le_standard :
      LinearMap.range L ≤
        (zcCompletedGroupAlgebraStandardAugmentationIdeal C H :
          Submodule (ZCCompletedGroupAlgebra C H) (ZCCompletedGroupAlgebra C H)) := by
    rintro y ⟨v, rfl⟩
    rw [zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span]
    change L v ∈ Submodule.span (ZCCompletedGroupAlgebra C H)
      (Set.range fun h : H => zcGroupLike C H h - 1)
    rw [show L v =
        ∑ x : X, v x * (zcGroupLike C H (φ x) - 1) from rfl]
    exact Submodule.sum_mem _ fun x _ =>
      Submodule.smul_mem _ (v x)
        (Submodule.subset_span ⟨φ x, rfl⟩)
  have haugmentation_le_range :
      zcCompletedGroupAlgebraAugmentationIdeal C H ≤
        (LinearMap.range L : Submodule (ZCCompletedGroupAlgebra C H)
          (ZCCompletedGroupAlgebra C H)) := by
    intro z hz
    have hzClosure :
        z ∈ closure
          ((zcCompletedGroupAlgebraStandardAugmentationIdeal C H :
            Ideal (ZCCompletedGroupAlgebra C H)) : Set (ZCCompletedGroupAlgebra C H)) := by
      rw [closure_zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_augmentationIdeal
        (C := C) (H := H) hForm]
      exact hz
    exact closure_minimal
      (by intro y hy; exact hstandard_le_range hy) hclosedRange hzClosure
  intro z
  constructor
  · intro hz
    exact haugmentation_le_range
      ((mem_zcCompletedGroupAlgebraAugmentationIdeal_iff
        (C := C) (H := H) (x := z)).2 hz)
  · rintro ⟨x, rfl⟩
    have hstd :
        L x ∈ zcCompletedGroupAlgebraStandardAugmentationIdeal C H :=
      hrange_le_standard ⟨x, rfl⟩
    have haug :
        L x ∈ zcCompletedGroupAlgebraAugmentationIdeal C H :=
      zcCompletedGroupAlgebraStandardAugmentationIdeal_le_augmentationIdeal C H hstd
    exact (mem_zcCompletedGroupAlgebraAugmentationIdeal_iff
      (C := C) (H := H) (x := L x)).1 haug

variable {X₀ : Type u} [Fintype X₀] [DecidableEq X₀]

/-- Source-shaped version of
`exact_foxBoundaryMap_zcGroupLike_sub_one_of_topologicallyGenerates`. -/
theorem exact_freeProCZCCompletedFoxBoundary_of_topologicallyGenerates
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (φ : X₀ → H) (hφ : TopologicallyGenerates (G := H) (Set.range φ)) :
    Function.Exact
      (freeProCZCCompletedFoxBoundary C φ :
        (X₀ → ZCCompletedGroupAlgebra C H) → ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraAugmentation C H :
        ZCCompletedGroupAlgebra C H → ZCCoeff C) := by
  simpa [freeProCZCCompletedFoxBoundary] using
    (exact_foxBoundaryMap_zcGroupLike_sub_one_of_topologicallyGenerates
      (C := C) (X := X₀) (H := H) hForm φ hφ)

end TailExactness

end

end FoxDifferential
