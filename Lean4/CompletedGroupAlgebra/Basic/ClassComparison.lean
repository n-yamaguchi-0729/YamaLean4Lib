import CompletedGroupAlgebra.Basic.AllFinite.Topology

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Basic/ClassComparison.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed Group Algebra Class Comparisons

Comparison maps and equivalences between the all-finite and finite-class-indexed constructions.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Projection from the all-finite completed group algebra to a stage indexed by a finite-only
class `C`. -/
def completedGroupAlgebraProjectionToStageInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    Carrier R G → CompletedGroupAlgebraStageInClass C R G U :=
  completedGroupAlgebraProjection R G
    (completedGroupAlgebraIndexInClassToAllFinite G C hC U)

@[simp]
theorem completedGroupAlgebraProjectionToStageInClass_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) (x : Carrier R G) :
    completedGroupAlgebraProjectionToStageInClass (R := R) (G := G) C hC U x =
      completedGroupAlgebraProjection R G
        (completedGroupAlgebraIndexInClassToAllFinite G C hC U) x :=
  rfl

theorem completedGroupAlgebraProjectionToStageInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V)
    (x : Carrier R G) :
    completedGroupAlgebraTransitionInClass C R G hUV
        (completedGroupAlgebraProjectionToStageInClass (R := R) (G := G) C hC V x) =
      completedGroupAlgebraProjectionToStageInClass (R := R) (G := G) C hC U x := by
  change completedGroupAlgebraTransition R G
      (completedGroupAlgebraIndexInClassToAllFinite_le (G := G) C hC hUV)
      (completedGroupAlgebraProjection R G
        (completedGroupAlgebraIndexInClassToAllFinite G C hC V) x) =
    completedGroupAlgebraProjection R G
      (completedGroupAlgebraIndexInClassToAllFinite G C hC U) x
  exact completedGroupAlgebraProjection_compatible (R := R) (G := G) x
    (completedGroupAlgebraIndexInClassToAllFinite_le (G := G) C hC hUV)

/-- The comparison map from the ordinary all-finite completed group algebra to the inverse limit
over any finite-only quotient class. -/
def completedGroupAlgebraToInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    Carrier R G → CompletedGroupAlgebraInClass C hC R G :=
  (completedGroupAlgebraSystemInClass C hC R G).inverseLimitLift
    (fun U => completedGroupAlgebraProjectionToStageInClass (R := R) (G := G) C hC U)
    (by
      intro U V hUV
      funext x
      exact completedGroupAlgebraProjectionToStageInClass_compatible
        (R := R) (G := G) C hC hUV x)

@[simp]
theorem completedGroupAlgebraToInClass_projection
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) (x : Carrier R G) :
    completedGroupAlgebraProjectionInClass C hC R G U
        (completedGroupAlgebraToInClass (R := R) (G := G) C hC x) =
      completedGroupAlgebraProjectionToStageInClass (R := R) (G := G) C hC U x :=
  rfl

/-- The comparison from the all-finite completed group algebra to the `C`-indexed inverse limit,
as a ring homomorphism. -/
def completedGroupAlgebraToInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    Carrier R G →+* CompletedGroupAlgebraInClass C hC R G where
  toFun := completedGroupAlgebraToInClass (R := R) (G := G) C hC
  map_zero' := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    rfl
  map_one' := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    rfl
  map_add' x y := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    rfl
  map_mul' x y := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    rfl

@[simp]
theorem completedGroupAlgebraToInClassRingHom_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (x : Carrier R G) :
    completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC x =
      completedGroupAlgebraToInClass (R := R) (G := G) C hC x :=
  rfl

/-- The comparison from the all-finite completed group algebra to the `C`-indexed inverse limit,
as an `R`-algebra homomorphism. -/
def completedGroupAlgebraToInClassAlgHom
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    Carrier R G →ₐ[R] CompletedGroupAlgebraInClass C hC R G where
  toRingHom := completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC
  commutes' := by
    intro r
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    rfl

@[simp]
theorem completedGroupAlgebraToInClassAlgHom_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (x : Carrier R G) :
    completedGroupAlgebraToInClassAlgHom (R := R) (G := G) C hC x =
      completedGroupAlgebraToInClass (R := R) (G := G) C hC x :=
  rfl

theorem continuous_completedGroupAlgebraToInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    Continuous (completedGroupAlgebraToInClass (R := R) (G := G) C hC) := by
  let S := completedGroupAlgebraSystemInClass C hC R G
  letI : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      TopologicalSpace (CompletedGroupAlgebraStageInClass C R G U) :=
    fun U => S.topologicalSpace U
  have hval : Continuous fun x : Carrier R G =>
      fun U : CompletedGroupAlgebraIndexInClass G C =>
        (show CompletedGroupAlgebraStageInClass C R G U from
          (completedGroupAlgebraToInClass (R := R) (G := G) C hC x).1 U) := by
    apply continuous_pi
    intro U
    change Continuous
      (completedGroupAlgebraProjectionToStageInClass (R := R) (G := G) C hC U)
    simpa [completedGroupAlgebraProjectionToStageInClass] using
      (completedGroupAlgebraSystem R G).continuous_projection
        (completedGroupAlgebraIndexInClassToAllFinite G C hC U)
  exact Continuous.subtype_mk hval fun x =>
    (completedGroupAlgebraToInClass (R := R) (G := G) C hC x).2

/-- For a pro-`C` group, the `C`-indexed inverse limit maps back to the ordinary all-finite
completed group algebra by reading the same open-normal quotient stages. -/
def completedGroupAlgebraFromInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    CompletedGroupAlgebraInClass C hC R G → Carrier R G :=
  (completedGroupAlgebraSystem R G).inverseLimitLift
    (fun U : CompletedGroupAlgebraIndex G =>
      completedGroupAlgebraProjectionInClass C hC R G
        (completedGroupAlgebraIndexToInClass G C hForm hG U))
    (by
      intro U V hUV
      funext x
      change completedGroupAlgebraTransitionInClass C R G
          (completedGroupAlgebraIndexToInClass_le (G := G) C hForm hG hUV)
          (completedGroupAlgebraProjectionInClass C hC R G
            (completedGroupAlgebraIndexToInClass G C hForm hG V) x) =
        completedGroupAlgebraProjectionInClass C hC R G
          (completedGroupAlgebraIndexToInClass G C hForm hG U) x
      exact completedGroupAlgebraProjectionInClass_compatible
        (R := R) (G := G) C hC
        (completedGroupAlgebraIndexToInClass_le (G := G) C hForm hG hUV) x)

@[simp]
theorem completedGroupAlgebraFromInClass_projection
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (U : CompletedGroupAlgebraIndex G)
    (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x) =
      completedGroupAlgebraProjectionInClass C hC R G
        (completedGroupAlgebraIndexToInClass G C hForm hG U) x :=
  rfl

/-- Ring-homomorphism form of `completedGroupAlgebraFromInClass`. -/
def completedGroupAlgebraFromInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    CompletedGroupAlgebraInClass C hC R G →+* Carrier R G where
  toFun := completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG
  map_zero' := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG 0) =
      completedGroupAlgebraProjection R G U (0 : Carrier R G)
    rw [completedGroupAlgebraFromInClass_projection]
    exact map_zero (completedGroupAlgebraProjectionRingHomInClass C hC R G
      (completedGroupAlgebraIndexToInClass G C hForm hG U))
  map_one' := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG 1) =
      completedGroupAlgebraProjection R G U (1 : Carrier R G)
    rw [completedGroupAlgebraFromInClass_projection]
    exact map_one (completedGroupAlgebraProjectionRingHomInClass C hC R G
      (completedGroupAlgebraIndexToInClass G C hForm hG U))
  map_add' x y := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG (x + y)) =
      completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x +
          completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG y)
    rw [completedGroupAlgebraFromInClass_projection]
    exact map_add (completedGroupAlgebraProjectionRingHomInClass C hC R G
      (completedGroupAlgebraIndexToInClass G C hForm hG U)) x y
  map_mul' x y := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG (x * y)) =
      completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x *
          completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG y)
    rw [completedGroupAlgebraFromInClass_projection]
    exact map_mul (completedGroupAlgebraProjectionRingHomInClass C hC R G
      (completedGroupAlgebraIndexToInClass G C hForm hG U)) x y

@[simp]
theorem completedGroupAlgebraFromInClassRingHom_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG x =
      completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x :=
  rfl

/-- Algebra-homomorphism form of `completedGroupAlgebraFromInClass`. -/
def completedGroupAlgebraFromInClassAlgHom
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    CompletedGroupAlgebraInClass C hC R G →ₐ[R] Carrier R G where
  toRingHom := completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG
  commutes' := by
    intro r
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change completedGroupAlgebraProjection R G U
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG
          (algebraMap R (CompletedGroupAlgebraInClass C hC R G) r)) =
      completedGroupAlgebraProjection R G U (algebraMap R (Carrier R G) r)
    rw [completedGroupAlgebraFromInClass_projection]
    change completedGroupAlgebraProjectionInClass C hC R G
        (completedGroupAlgebraIndexToInClass G C hForm hG U)
        (algebraMap R (CompletedGroupAlgebraInClass C hC R G) r) =
      algebraMap R (CompletedGroupAlgebraStage R G U) r
    exact completedGroupAlgebraProjectionInClass_algebraMap (R := R) (G := G) C hC
      (completedGroupAlgebraIndexToInClass G C hForm hG U) r

@[simp]
theorem completedGroupAlgebraFromInClassAlgHom_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraFromInClassAlgHom (R := R) (G := G) C hC hForm hG x =
      completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x :=
  rfl

theorem continuous_completedGroupAlgebraFromInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    Continuous (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG) := by
  let S := completedGroupAlgebraSystem R G
  letI : ∀ U : CompletedGroupAlgebraIndex G, TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    fun U => S.topologicalSpace U
  have hval : Continuous fun x : CompletedGroupAlgebraInClass C hC R G =>
      fun U : CompletedGroupAlgebraIndex G =>
        (show CompletedGroupAlgebraStage R G U from
          (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x).1 U) := by
    apply continuous_pi
    intro U
    letI : TopologicalSpace
        (CompletedGroupAlgebraStageInClass C R G (completedGroupAlgebraIndexToInClass G C hForm hG U)) :=
      (completedGroupAlgebraSystemInClass C hC R G).topologicalSpace
        (completedGroupAlgebraIndexToInClass G C hForm hG U)
    change Continuous (completedGroupAlgebraProjectionInClass C hC R G
      (completedGroupAlgebraIndexToInClass G C hForm hG U))
    simpa using continuous_completedGroupAlgebraProjectionInClass
      (R := R) (G := G) C hC (completedGroupAlgebraIndexToInClass G C hForm hG U)
  exact Continuous.subtype_mk hval fun x =>
    (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x).2

@[simp]
theorem completedGroupAlgebraFromInClass_toInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (x : Carrier R G) :
    completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG
        (completedGroupAlgebraToInClass (R := R) (G := G) C hC x) = x := by
  apply (completedGroupAlgebraSystem R G).ext
  intro U
  change completedGroupAlgebraProjection R G U
      (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG
        (completedGroupAlgebraToInClass (R := R) (G := G) C hC x)) =
    completedGroupAlgebraProjection R G U x
  rw [completedGroupAlgebraFromInClass_projection, completedGroupAlgebraToInClass_projection]
  change x.1
      (completedGroupAlgebraIndexInClassToAllFinite G C hC
        (completedGroupAlgebraIndexToInClass G C hForm hG U)) = x.1 U
  cases U
  rfl

@[simp]
theorem completedGroupAlgebraToInClass_fromInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraToInClass (R := R) (G := G) C hC
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x) = x := by
  apply (completedGroupAlgebraSystemInClass C hC R G).ext
  intro U
  change completedGroupAlgebraProjectionInClass C hC R G U
      (completedGroupAlgebraToInClass (R := R) (G := G) C hC
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x)) =
    completedGroupAlgebraProjectionInClass C hC R G U x
  rw [completedGroupAlgebraToInClass_projection]
  change completedGroupAlgebraProjection R G
      (completedGroupAlgebraIndexInClassToAllFinite G C hC U)
      (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x) =
    completedGroupAlgebraProjectionInClass C hC R G U x
  rw [completedGroupAlgebraFromInClass_projection]
  change x.1
      (completedGroupAlgebraIndexToInClass G C hForm hG
        (completedGroupAlgebraIndexInClassToAllFinite G C hC U)) = x.1 U
  cases U
  rfl

@[simp]
theorem completedGroupAlgebraFromInClassRingHom_comp_toInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG).comp
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC) =
      RingHom.id (Carrier R G) := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraFromInClass_toInClass (R := R) (G := G) C hC hForm hG x

@[simp]
theorem completedGroupAlgebraToInClassRingHom_comp_fromInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC).comp
        (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG) =
      RingHom.id (CompletedGroupAlgebraInClass C hC R G) := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraToInClass_fromInClass (R := R) (G := G) C hC hForm hG x

/-- For a pro-`C` group, the all-finite and `C`-indexed completed group algebras are the same
ring, via the comparison maps. -/
def completedGroupAlgebraInClassRingEquiv
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    Carrier R G ≃+* CompletedGroupAlgebraInClass C hC R G where
  toFun := completedGroupAlgebraToInClass (R := R) (G := G) C hC
  invFun := completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG
  left_inv := by
    intro x
    exact completedGroupAlgebraFromInClass_toInClass (R := R) (G := G) C hC hForm hG x
  right_inv := by
    intro x
    exact completedGroupAlgebraToInClass_fromInClass (R := R) (G := G) C hC hForm hG x
  map_mul' := by
    intro x y
    exact map_mul (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC) x y
  map_add' := by
    intro x y
    exact map_add (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC) x y

@[simp]
theorem completedGroupAlgebraInClassRingEquiv_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (x : Carrier R G) :
    completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hC hForm hG x =
      completedGroupAlgebraToInClass (R := R) (G := G) C hC x :=
  rfl

@[simp]
theorem completedGroupAlgebraInClassRingEquiv_symm_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (x : CompletedGroupAlgebraInClass C hC R G) :
    (completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hC hForm hG).symm x =
      completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x :=
  rfl

/-- For a pro-`C` group, the all-finite and `C`-indexed completed group algebras are the same
`R`-algebra. -/
def completedGroupAlgebraInClassAlgEquiv
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    Carrier R G ≃ₐ[R] CompletedGroupAlgebraInClass C hC R G :=
  AlgEquiv.ofRingEquiv (f := completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hC hForm hG)
    (by
      intro r
      rfl)

@[simp]
theorem completedGroupAlgebraInClassAlgEquiv_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (x : Carrier R G) :
    completedGroupAlgebraInClassAlgEquiv (R := R) (G := G) C hC hForm hG x =
      completedGroupAlgebraToInClass (R := R) (G := G) C hC x :=
  rfl

@[simp]
theorem completedGroupAlgebraInClassAlgEquiv_symm_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (x : CompletedGroupAlgebraInClass C hC R G) :
    (completedGroupAlgebraInClassAlgEquiv (R := R) (G := G) C hC hForm hG).symm x =
      completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x :=
  rfl

/-- The comparison equivalence is an equivalence of topological spaces. -/
def completedGroupAlgebraInClassHomeomorph
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    Carrier R G ≃ₜ CompletedGroupAlgebraInClass C hC R G where
  toEquiv := (completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hC hForm hG).toEquiv
  continuous_toFun := continuous_completedGroupAlgebraToInClass (R := R) (G := G) C hC
  continuous_invFun := continuous_completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG

@[simp]
theorem completedGroupAlgebraInClassHomeomorph_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (x : Carrier R G) :
    completedGroupAlgebraInClassHomeomorph (R := R) (G := G) C hC hForm hG x =
      completedGroupAlgebraToInClass (R := R) (G := G) C hC x :=
  rfl

@[simp]
theorem completedGroupAlgebraInClassHomeomorph_symm_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) (x : CompletedGroupAlgebraInClass C hC R G) :
    (completedGroupAlgebraInClassHomeomorph (R := R) (G := G) C hC hForm hG).symm x =
      completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x :=
  rfl

theorem completedGroupAlgebraToInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    Function.Surjective (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC) := by
  intro x
  refine ⟨completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG x, ?_⟩
  exact completedGroupAlgebraToInClass_fromInClass (R := R) (G := G) C hC hForm hG x

theorem completedGroupAlgebraFromInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    Function.Surjective (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG) := by
  intro x
  refine ⟨completedGroupAlgebraToInClass (R := R) (G := G) C hC x, ?_⟩
  exact completedGroupAlgebraFromInClass_toInClass (R := R) (G := G) C hC hForm hG x

end

end CompletedGroupAlgebra
