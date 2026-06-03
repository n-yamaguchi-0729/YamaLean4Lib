import CompletedGroupAlgebra.Basic.InClass.System

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Basic/InClass/LimitAlgebra.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Class-Indexed Completed Group Algebras

Finite-class-indexed inverse systems and inverse limits for completed group algebras.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v w

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]


/-- The `C`-indexed completed group algebra as an inverse limit of finite-stage group algebras. -/
abbrev CompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Type (max u v) :=
  (completedGroupAlgebraSystemInClass C hC R G).inverseLimit

instance instRingCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    Ring (CompletedGroupAlgebraInClass C hC R G) := by
  change Ring (completedGroupAlgebraSystemInClass C hC R G).inverseLimit
  infer_instance

/-- Change coefficients on the `C`-indexed completed group algebra stagewise. -/
def completedGroupAlgebraCoeffMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (S : Type w) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) :
    CompletedGroupAlgebraInClass C hC R G →+* CompletedGroupAlgebraInClass C hC S G where
  toFun x := ⟨fun U =>
      completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U (x.1 U), by
    intro U V hUV
    have hcompat := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraStageCoeffMapInClass_compatible
          (R := R) (G := G) C S f hUV))
      (x.1 V)
    calc
      completedGroupAlgebraTransitionInClass C S G hUV
          (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f V (x.1 V))
          =
        completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U
          (completedGroupAlgebraTransitionInClass C R G hUV (x.1 V)) := hcompat.symm
      _ =
        completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U (x.1 U) := by
          exact congrArg (completedGroupAlgebraStageCoeffMapInClass
            (R := R) (G := G) C S f U) (x.2 U V hUV)⟩
  map_zero' := by
    apply Subtype.ext
    funext U
    exact map_zero (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U)
  map_one' := by
    apply Subtype.ext
    funext U
    exact map_one (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U)
  map_add' x y := by
    apply Subtype.ext
    funext U
    exact map_add (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U)
      (x.1 U) (y.1 U)
  map_mul' x y := by
    apply Subtype.ext
    funext U
    exact map_mul (completedGroupAlgebraStageCoeffMapInClass (R := R) (G := G) C S f U)
      (x.1 U) (y.1 U)

instance instSMulCoeffCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    SMul R (CompletedGroupAlgebraInClass C hC R G) where
  smul r x := ⟨fun U =>
      r • (show CompletedGroupAlgebraStageInClass C R G U from x.1 U), by
    intro U V hUV
    change completedGroupAlgebraTransitionInClass C R G hUV
        (r • (show CompletedGroupAlgebraStageInClass C R G V from x.1 V)) =
      r • (show CompletedGroupAlgebraStageInClass C R G U from x.1 U)
    rw [completedGroupAlgebraTransitionInClass_smul]
    exact congrArg (r • ·) (x.2 U V hUV)⟩

/-- Scalar multiplication in the inverse-limit algebra is computed stagewise. -/
@[simp]
theorem coe_smul_completedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (r : R) (x : CompletedGroupAlgebraInClass C hC R G) :
    ((r • x : CompletedGroupAlgebraInClass C hC R G) :
      (U : CompletedGroupAlgebraIndexInClass G C) →
        (completedGroupAlgebraSystemInClass C hC R G).X U) =
      fun U => r • (show CompletedGroupAlgebraStageInClass C R G U from x.1 U) := by
  funext U
  rfl

/-- Evaluation of a `C`-indexed completed group algebra element as a compatible family,
bundled as an additive monoid homomorphism. -/
def completedGroupAlgebraInClassValAddMonoidHom
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    CompletedGroupAlgebraInClass C hC R G →+
      ((U : CompletedGroupAlgebraIndexInClass G C) →
        CompletedGroupAlgebraStageInClass C R G U) where
  toFun x := fun U => (show CompletedGroupAlgebraStageInClass C R G U from x.1 U)
  map_zero' := by
    funext U
    rfl
  map_add' x y := by
    funext U
    rfl

instance instModuleCoeffCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    Module R (CompletedGroupAlgebraInClass C hC R G) :=
  Function.Injective.module R
    (completedGroupAlgebraInClassValAddMonoidHom (R := R) (G := G) C hC)
    (fun x y h => by
      apply Subtype.ext
      funext U
      exact congrFun h U)
    (fun r x => by
      funext U
      rfl)

/-- The coefficient-ring map into the `C`-indexed completed group algebra. -/
def completedGroupAlgebraAlgebraMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    R →+* CompletedGroupAlgebraInClass C hC R G where
  toFun r := ⟨fun U => algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r, by
    intro U V hUV
    exact completedGroupAlgebraTransitionInClass_algebraMap (R := R) (G := G) C hUV r⟩
  map_zero' := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    exact map_zero (algebraMap R (CompletedGroupAlgebraStageInClass C R G U))
  map_one' := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    exact map_one (algebraMap R (CompletedGroupAlgebraStageInClass C R G U))
  map_add' r s := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    exact map_add (algebraMap R (CompletedGroupAlgebraStageInClass C R G U)) r s
  map_mul' r s := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    exact map_mul (algebraMap R (CompletedGroupAlgebraStageInClass C R G U)) r s

instance instAlgebraCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    Algebra R (CompletedGroupAlgebraInClass C hC R G) where
  algebraMap := completedGroupAlgebraAlgebraMapInClass (R := R) (G := G) C hC
  commutes' := by
    intro r x
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    change algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r *
        (show CompletedGroupAlgebraStageInClass C R G U from x.1 U) =
      (show CompletedGroupAlgebraStageInClass C R G U from x.1 U) *
        algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r
    exact Algebra.commutes r (show CompletedGroupAlgebraStageInClass C R G U from x.1 U)
  smul_def' := by
    intro r x
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    change r • (show CompletedGroupAlgebraStageInClass C R G U from x.1 U) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r *
        (show CompletedGroupAlgebraStageInClass C R G U from x.1 U)
    rw [Algebra.smul_def]


end

end CompletedGroupAlgebra
