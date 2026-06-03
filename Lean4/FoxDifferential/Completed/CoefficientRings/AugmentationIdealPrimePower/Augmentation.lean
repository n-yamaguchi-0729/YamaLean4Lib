import FoxDifferential.Completed.CoefficientRings.AugmentationIdealPrimePower.LimitEquiv

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/AugmentationIdealPrimePower/Augmentation.lean
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

omit [Fact (0 < ℓ)] in
/-- Composition lemma primePowerCompletedGroupAlgebraAugmentation_comp_coeffToGroupAlgebra. -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentation_comp_coeffToGroupAlgebra
    (x : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G)
        (primePowerCompletedCoeffToGroupAlgebra (ℓ := ℓ) (G := G) x) = x := by
  apply (primePowerCompletedCoeffSystem ℓ G).ext
  intro i
  change modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
      (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (primePowerCompletedCoeffToGroupAlgebra (ℓ := ℓ) (G := G) x)) = x.1 i
  change modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
      (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i) (x.1 i)) = x.1 i
  exact primePowerCompletedGroupAlgebraStageAugmentation_algebraMap (ℓ := ℓ) (G := G) i (x.1 i)

/-- The canonical prime-power augmentation as an additive homomorphism. -/
def primePowerCompletedGroupAlgebraAugmentationAddHom :
    PrimePowerCompletedGroupAlgebra ℓ G →+ PrimePowerCompletedCoeff ℓ G where
  toFun := primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G)
  map_zero' := by
    apply (primePowerCompletedCoeffSystem ℓ G).ext
    intro i
    change modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i 0) = 0
    rw [primePowerCompletedGroupAlgebraProjection_zero]
    exact map_zero
      (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2)
  map_add' x y := by
    apply (primePowerCompletedCoeffSystem ℓ G).ext
    intro i
    change modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (x + y)) =
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x) +
        modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i y)
    rw [primePowerCompletedGroupAlgebraProjection_add]
    exact map_add
      (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2)
      _ _

/-- Definition of primePowerCompletedGroupAlgebraAugmentationRingHom. -/
def primePowerCompletedGroupAlgebraAugmentationRingHom :
    PrimePowerCompletedGroupAlgebra ℓ G →+* PrimePowerCompletedCoeff ℓ G where
  toFun := primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G)
  map_one' := by
    apply (primePowerCompletedCoeffSystem ℓ G).ext
    intro i
    change modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i 1) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i 1
    rw [primePowerCompletedGroupAlgebraProjection_one,
      primePowerCompletedCoeffProjection_one]
    exact map_one (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2)
  map_mul' := by
    intro x y
    apply (primePowerCompletedCoeffSystem ℓ G).ext
    intro i
    change modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (x * y)) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x *
          primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) y)
    rw [primePowerCompletedGroupAlgebraProjection_mul,
      primePowerCompletedCoeffProjection_mul]
    exact map_mul (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2)
      _ _
  map_zero' := by
    exact map_zero (primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G))
  map_add' := by
    intro x y
    exact map_add (primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G)) x y

abbrev primePowerCompletedGroupAlgebraAugmentationIdealAsIdeal :
    Ideal (PrimePowerCompletedGroupAlgebra ℓ G) :=
  RingHom.ker (primePowerCompletedGroupAlgebraAugmentationRingHom (ℓ := ℓ) (G := G))

variable {ℓ G} in
omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が所属条件を対応する augmentation または射影の消滅条件として特徴づけることを述べる。 -/
@[simp]
theorem mem_primePowerCompletedGroupAlgebraAugmentationIdealAsIdeal_iff
    {x : PrimePowerCompletedGroupAlgebra ℓ G} :
    x ∈ primePowerCompletedGroupAlgebraAugmentationIdealAsIdeal (ℓ := ℓ) (G := G) ↔
      primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x =
        (0 : PrimePowerCompletedCoeff ℓ G) := by
  rw [primePowerCompletedGroupAlgebraAugmentationIdealAsIdeal, RingHom.mem_ker]
  rfl

variable {ℓ G} in
omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
theorem mem_primePowerCompletedGroupAlgebraAugmentationIdealAsIdeal_iff_forall
    {x : PrimePowerCompletedGroupAlgebra ℓ G} :
    x ∈ primePowerCompletedGroupAlgebraAugmentationIdealAsIdeal (ℓ := ℓ) (G := G) ↔
      ∀ i : PrimePowerCompletedGroupAlgebraIndex G,
        modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x) = 0 := by
  rw [mem_primePowerCompletedGroupAlgebraAugmentationIdealAsIdeal_iff,
    ← mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff_forall]
  rfl

/-- The additive kernel of the prime-power augmentation. -/
def primePowerCompletedGroupAlgebraAugmentationAddSubgroup :
    AddSubgroup (PrimePowerCompletedGroupAlgebra ℓ G) :=
  { carrier := {x |
      primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G) x = 0}
    zero_mem' := by
      exact map_zero (primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G))
    add_mem' := by
      intro x y hx hy
      change primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G) (x + y) = 0
      rw [map_add, hx, hy]
      simp only [add_zero]
    neg_mem' := by
      intro x hx
      change primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G) (-x) = 0
      rw [map_neg, hx]
      simp only [neg_zero]}

omit [Fact (0 < ℓ)] in
/-- Surjectivity lemma primePowerCompletedGroupAlgebraAugmentation_surjective. -/
theorem primePowerCompletedGroupAlgebraAugmentation_surjective :
    Function.Surjective (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G)) := by
  intro x
  refine ⟨primePowerCompletedCoeffToGroupAlgebra (ℓ := ℓ) (G := G) x, ?_⟩
  exact primePowerCompletedGroupAlgebraAugmentation_comp_coeffToGroupAlgebra
    (ℓ := ℓ) (G := G) x

omit [Fact (0 < ℓ)] in
/-- Surjectivity lemma primePowerCompletedGroupAlgebraAugmentationAddHom_surjective. -/
theorem primePowerCompletedGroupAlgebraAugmentationAddHom_surjective :
    Function.Surjective (primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G)) := by
  simpa [primePowerCompletedGroupAlgebraAugmentationAddHom] using
    primePowerCompletedGroupAlgebraAugmentation_surjective (ℓ := ℓ) (G := G)

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
theorem exact_primePowerCompletedGroupAlgebraAugmentationAddSubgroup_subtype :
    Function.Exact
      (primePowerCompletedGroupAlgebraAugmentationAddSubgroup (ℓ := ℓ) (G := G)).subtype
      (primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G)) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が標準包含または係数写像が単射であることを述べる。 -/
theorem primePowerCompletedGroupAlgebraAugmentationAddSubgroup_subtype_injective :
    Function.Injective
      (primePowerCompletedGroupAlgebraAugmentationAddSubgroup (ℓ := ℓ) (G := G)).subtype := by
  intro x y hxy
  exact Subtype.ext hxy

omit [Fact (0 < ℓ)] in
/-- Injectivity, kernel identification, and surjectivity for the additive prime-power
augmentation map. -/
theorem primePowerCompletedGroupAlgebraAugmentationAdd_shortExact :
    Function.Injective
        (primePowerCompletedGroupAlgebraAugmentationAddSubgroup (ℓ := ℓ) (G := G)).subtype ∧
      Function.Exact
        (primePowerCompletedGroupAlgebraAugmentationAddSubgroup (ℓ := ℓ) (G := G)).subtype
        (primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G)) ∧
      Function.Surjective
        (primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G)) := by
  refine ⟨primePowerCompletedGroupAlgebraAugmentationAddSubgroup_subtype_injective
      (ℓ := ℓ) (G := G), ?_, ?_⟩
  · exact exact_primePowerCompletedGroupAlgebraAugmentationAddSubgroup_subtype
      (ℓ := ℓ) (G := G)
  · exact primePowerCompletedGroupAlgebraAugmentationAddHom_surjective (ℓ := ℓ) (G := G)

/-- The canonical prime-power augmentation viewed as a `ℤ`-linear map. -/
def primePowerCompletedGroupAlgebraAugmentationLinear :
    PrimePowerCompletedGroupAlgebra ℓ G →ₗ[ℤ] PrimePowerCompletedCoeff ℓ G :=
  (primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G)).toIntLinearMap

/-- The canonical prime-power augmentation viewed as a
`PrimePowerCompletedCoeff ℓ G`-linear map. -/
def primePowerCompletedGroupAlgebraAugmentationCoeffLinear :
    PrimePowerCompletedGroupAlgebra ℓ G →ₗ[PrimePowerCompletedCoeff ℓ G]
      PrimePowerCompletedCoeff ℓ G where
  toFun := primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G)
  map_add' := by
    intro x y
    exact map_add (primePowerCompletedGroupAlgebraAugmentationAddHom (ℓ := ℓ) (G := G)) x y
  map_smul' := by
    intro a x
    apply (primePowerCompletedCoeffSystem ℓ G).ext
    intro i
    change modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (a • x)) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a *
        modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x)
    rw [primePowerCompletedGroupAlgebraProjection_smul, Algebra.smul_def, map_mul,
      primePowerCompletedGroupAlgebraStageAugmentation_algebraMap]

/-- Evaluation formula for primePowerCompletedGroupAlgebraAugmentationCoeffLinear_of. -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationCoeffLinear_of
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (h : H) :
    primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ell) (G := H)
        (primePowerCompletedGroupAlgebraOf (ell := ell) h) =
      1 := by
  apply (primePowerCompletedCoeffSystem ell H).ext
  intro i
  change modNCompletedGroupAlgebraStageAugmentation (ell ^ i.1) H i.2
      (primePowerCompletedGroupAlgebraProjection (ℓ := ell) (G := H) i
        (primePowerCompletedGroupAlgebraOf (ell := ell) h)) =
    primePowerCompletedCoeffProjection (ℓ := ell) (G := H) i
      (1 : PrimePowerCompletedCoeff ell H)
  rw [primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedCoeffProjection_one]
  exact modNCompletedGroupAlgebraStageAugmentation_of (n := ell ^ i.1) (G := H) i.2
    (QuotientGroup.mk h)

/-- 素冪係数段階で、係数側の線形射影は単位元を単位元へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationCoeffLinear_one
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ell) (G := H)
        (1 : PrimePowerCompletedGroupAlgebra ell H) =
      1 := by
  change primePowerCompletedGroupAlgebraAugmentation (ℓ := ell) (G := H)
      (1 : PrimePowerCompletedGroupAlgebra ell H) = 1
  exact map_one (primePowerCompletedGroupAlgebraAugmentationRingHom (ℓ := ell) (G := H))

/-- 素冪係数段階で、係数側の線形射影は積を積へ送る。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationCoeffLinear_mul
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (x y : PrimePowerCompletedGroupAlgebra ell H) :
    primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ell) (G := H) (x * y) =
      primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ell) (G := H) x *
        primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ell) (G := H) y := by
  change primePowerCompletedGroupAlgebraAugmentation (ℓ := ell) (G := H) (x * y) =
    primePowerCompletedGroupAlgebraAugmentation (ℓ := ell) (G := H) x *
      primePowerCompletedGroupAlgebraAugmentation (ℓ := ell) (G := H) y
  exact map_mul (primePowerCompletedGroupAlgebraAugmentationRingHom (ℓ := ell) (G := H)) x y

/-- The kernel inclusion of the prime-power augmentation, viewed as a `ℤ`-linear map. -/
def primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear :
    primePowerCompletedGroupAlgebraAugmentationAddSubgroup (ℓ := ℓ) (G := G) →ₗ[ℤ]
      PrimePowerCompletedGroupAlgebra ℓ G :=
  (primePowerCompletedGroupAlgebraAugmentationAddSubgroup
    (ℓ := ℓ) (G := G)).subtype.toIntLinearMap

omit [Fact (0 < ℓ)] in
/-- Surjectivity lemma primePowerCompletedGroupAlgebraAugmentationLinear_surjective. -/
theorem primePowerCompletedGroupAlgebraAugmentationLinear_surjective :
    Function.Surjective
      (primePowerCompletedGroupAlgebraAugmentationLinear (ℓ := ℓ) (G := G)) := by
  simpa [primePowerCompletedGroupAlgebraAugmentationLinear, AddMonoidHom.coe_toIntLinearMap] using
    primePowerCompletedGroupAlgebraAugmentationAddHom_surjective (ℓ := ℓ) (G := G)

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が標準包含または係数写像が単射であることを述べる。 -/
theorem primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear_injective :
    Function.Injective
      (primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
        (ℓ := ℓ) (G := G)) := by
  exact primePowerCompletedGroupAlgebraAugmentationAddSubgroup_subtype_injective
    (ℓ := ℓ) (G := G)

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
theorem exact_primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear :
    Function.Exact
      (primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
        (ℓ := ℓ) (G := G))
      (primePowerCompletedGroupAlgebraAugmentationLinear (ℓ := ℓ) (G := G)) := by
  simpa [primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear,
      primePowerCompletedGroupAlgebraAugmentationLinear, AddMonoidHom.coe_toIntLinearMap] using
    exact_primePowerCompletedGroupAlgebraAugmentationAddSubgroup_subtype
      (ℓ := ℓ) (G := G)

omit [Fact (0 < ℓ)] in
/-- Injectivity, kernel identification, and surjectivity for the prime-power augmentation map in
`ℤ`-linear form. -/
theorem primePowerCompletedGroupAlgebraAugmentationLinear_shortExact :
    Function.Injective
        (primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
          (ℓ := ℓ) (G := G)) ∧
      Function.Exact
        (primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
          (ℓ := ℓ) (G := G))
        (primePowerCompletedGroupAlgebraAugmentationLinear (ℓ := ℓ) (G := G)) ∧
      Function.Surjective
        (primePowerCompletedGroupAlgebraAugmentationLinear (ℓ := ℓ) (G := G)) := by
  refine ⟨primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear_injective
      (ℓ := ℓ) (G := G), ?_, ?_⟩
  · exact exact_primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
      (ℓ := ℓ) (G := G)
  · exact primePowerCompletedGroupAlgebraAugmentationLinear_surjective (ℓ := ℓ) (G := G)


end

end FoxDifferential
