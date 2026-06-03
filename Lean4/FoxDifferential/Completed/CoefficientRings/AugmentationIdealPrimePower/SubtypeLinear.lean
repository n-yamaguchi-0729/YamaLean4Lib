import FoxDifferential.Completed.CoefficientRings.AugmentationIdealPrimePower.Augmentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/AugmentationIdealPrimePower/SubtypeLinear.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed coefficient algebras

Coefficient algebras, residue stages, and completed group-algebra maps are kept as the scalar layer for completed Fox calculus.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems

universe u


variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The inverse-limit augmentation ideal is additively equivalent to the additive kernel of the
canonical prime-power augmentation. -/
def primePowerCompletedGroupAlgebraAugmentationIdealAddEquivAddSubgroup :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G ≃+
      primePowerCompletedGroupAlgebraAugmentationAddSubgroup (ℓ := ℓ) (G := G) where
  toFun x := by
    refine ⟨(ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
      (ℓ := ℓ) (G := G) x).1, ?_⟩
    simp only [SetLike.coe_mem]
  invFun x :=
    toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) <|
      ⟨x.1, by
        simp only [Subtype.coe_prop]⟩
  left_inv := by
    intro x
    exact toPrimePowerCompletedGroupAlgebraAugmentationIdeal_of
      (ℓ := ℓ) (G := G) x
  right_inv := by
    intro x
    apply Subtype.ext
    let y : PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) :=
      ⟨x.1, by
        simp only [Subtype.coe_prop]⟩
    exact congrArg Subtype.val
      (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal_to
        (ℓ := ℓ) (G := G) y)
  map_add' x y := by
    apply Subtype.ext
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    rfl

/-- The inverse-limit augmentation ideal is linearly equivalent to the additive kernel of the
canonical prime-power augmentation. -/
def primePowerCompletedGroupAlgebraAugmentationIdealLinearEquivAddSubgroup :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G ≃ₗ[ℤ]
      primePowerCompletedGroupAlgebraAugmentationAddSubgroup (ℓ := ℓ) (G := G) :=
  (primePowerCompletedGroupAlgebraAugmentationIdealAddEquivAddSubgroup
    (ℓ := ℓ) (G := G)).toIntLinearEquiv

/-- The canonical inclusion of the inverse-limit augmentation ideal into the prime-power completed
group algebra. -/
def primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G →ₗ[ℤ]
      PrimePowerCompletedGroupAlgebra ℓ G :=
  (primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
    (ℓ := ℓ) (G := G)).comp
      (primePowerCompletedGroupAlgebraAugmentationIdealLinearEquivAddSubgroup
        (ℓ := ℓ) (G := G)).toLinearMap

omit [Fact (0 < ℓ)] in
/-- Evaluation formula for primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_apply. -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_apply
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
        (ℓ := ℓ) (G := G) x =
      (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
        (ℓ := ℓ) (G := G) x).1 := by
  rfl

/-- The canonical inclusion of the inverse-limit augmentation ideal into the prime-power completed
group algebra, viewed over the completed coefficient ring. -/
def primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G →ₗ[PrimePowerCompletedCoeff ℓ G]
      PrimePowerCompletedGroupAlgebra ℓ G where
  toFun := fun x =>
    (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x).1
  map_add' := by
    intro x y
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change (((primePowerCompletedGroupAlgebraAugmentationIdealProjection
        (ℓ := ℓ) (G := G) i x +
          primePowerCompletedGroupAlgebraAugmentationIdealProjection
            (ℓ := ℓ) (G := G) i y :
          primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) :
            PrimePowerCompletedGroupAlgebraStage ℓ G i)) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        ((ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
          (ℓ := ℓ) (G := G) x).1 +
          (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
            (ℓ := ℓ) (G := G) y).1)
    rw [primePowerCompletedGroupAlgebraProjection_add,
      primePowerCompletedGroupAlgebraProjection_ofAugmentationIdeal,
      primePowerCompletedGroupAlgebraProjection_ofAugmentationIdeal]
    rfl
  map_smul' := by
    intro a x
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change (((primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        primePowerCompletedGroupAlgebraAugmentationIdealProjection
          (ℓ := ℓ) (G := G) i x :
          primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) :
            PrimePowerCompletedGroupAlgebraStage ℓ G i) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (a • (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
          (ℓ := ℓ) (G := G) x).1)
    rw [primePowerCompletedGroupAlgebraProjection_smul,
      primePowerCompletedGroupAlgebraProjection_ofAugmentationIdeal]
    rfl

omit [Fact (0 < ℓ)] in
/-- Evaluation formula for primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear_apply. -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear_apply
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
        (ℓ := ℓ) (G := G) x =
      (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
        (ℓ := ℓ) (G := G) x).1 := rfl

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が標準包含または係数写像が単射であることを述べる。 -/
theorem primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_injective :
    Function.Injective
      (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
        (ℓ := ℓ) (G := G)) := by
  intro x y hxy
  apply (primePowerCompletedGroupAlgebraAugmentationIdealLinearEquivAddSubgroup
    (ℓ := ℓ) (G := G)).injective
  exact
    (primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear_injective
      (ℓ := ℓ) (G := G)) hxy

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
theorem exact_primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear :
    Function.Exact
      (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
        (ℓ := ℓ) (G := G))
      (primePowerCompletedGroupAlgebraAugmentationLinear (ℓ := ℓ) (G := G)) := by
  intro x
  constructor
  · intro hx
    rcases
        (exact_primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
          (ℓ := ℓ) (G := G) x).1 hx with
      ⟨y, hy⟩
    refine ⟨(primePowerCompletedGroupAlgebraAugmentationIdealLinearEquivAddSubgroup
      (ℓ := ℓ) (G := G)).symm y, ?_⟩
    simpa [primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear] using hy
  · rintro ⟨y, rfl⟩
    let z :=
      (primePowerCompletedGroupAlgebraAugmentationIdealLinearEquivAddSubgroup
        (ℓ := ℓ) (G := G)) y
    exact
      (exact_primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
        (ℓ := ℓ) (G := G)
        ((primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
          (ℓ := ℓ) (G := G)) z)).2
        ⟨z, rfl⟩

omit [Fact (0 < ℓ)] in
/-- Injectivity, kernel identification, and surjectivity for the canonical inverse-limit
augmentation-ideal inclusion followed by the canonical prime-power augmentation. -/
theorem primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_shortExact :
    Function.Injective
        (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
          (ℓ := ℓ) (G := G)) ∧
      Function.Exact
        (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
          (ℓ := ℓ) (G := G))
        (primePowerCompletedGroupAlgebraAugmentationLinear (ℓ := ℓ) (G := G)) ∧
      Function.Surjective
        (primePowerCompletedGroupAlgebraAugmentationLinear (ℓ := ℓ) (G := G)) := by
  refine ⟨
    primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_injective
      (ℓ := ℓ) (G := G),
    exact_primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
      (ℓ := ℓ) (G := G),
    primePowerCompletedGroupAlgebraAugmentationLinear_surjective (ℓ := ℓ) (G := G)⟩

omit [Fact (0 < ℓ)] in
/-- Surjectivity lemma primePowerCompletedGroupAlgebraAugmentationCoeffLinear_surjective. -/
theorem primePowerCompletedGroupAlgebraAugmentationCoeffLinear_surjective :
    Function.Surjective
      (primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ℓ) (G := G)) := by
  simpa [primePowerCompletedGroupAlgebraAugmentationCoeffLinear] using
    primePowerCompletedGroupAlgebraAugmentation_surjective (ℓ := ℓ) (G := G)

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が標準包含または係数写像が単射であることを述べる。 -/
theorem primePowerCompletedGAAugmentationIdealToGACoeffLinear_inj :
    Function.Injective
      (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
        (ℓ := ℓ) (G := G)) := by
  intro x y hxy
  apply primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_injective
    (ℓ := ℓ) (G := G)
  simpa [primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear,
    primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear] using hxy

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
theorem exact_primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear :
    Function.Exact
      (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
        (ℓ := ℓ) (G := G))
      (primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ℓ) (G := G)) := by
  simpa [primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear,
    primePowerCompletedGroupAlgebraAugmentationCoeffLinear,
    primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear,
    primePowerCompletedGroupAlgebraAugmentationLinear]
    using
      exact_primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
        (ℓ := ℓ) (G := G)

omit [Fact (0 < ℓ)] in
/-- Injectivity, kernel identification, and surjectivity for the canonical inverse-limit
augmentation-ideal inclusion followed by the completed-coefficient prime-power augmentation. -/
theorem primePowerCompletedGAAugmentationIdealToGACoeffLinear_shortExact :
    Function.Injective
        (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
          (ℓ := ℓ) (G := G)) ∧
      Function.Exact
        (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
          (ℓ := ℓ) (G := G))
        (primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ℓ) (G := G)) ∧
      Function.Surjective
        (primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ℓ) (G := G)) := by
  refine ⟨
    primePowerCompletedGAAugmentationIdealToGACoeffLinear_inj
      (ℓ := ℓ) (G := G),
    exact_primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
      (ℓ := ℓ) (G := G),
    primePowerCompletedGroupAlgebraAugmentationCoeffLinear_surjective (ℓ := ℓ) (G := G)⟩

end

end FoxDifferential
