import CompletedGroupAlgebra.Basic.InClass.Stage

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Basic/InClass/System.lean
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


/-- The `C`-indexed inverse system `U ↦ R[G/U]`.  The hypothesis says that `C` really is a
finite quotient class, so every stage carries the finite-product topology. -/
def completedGroupAlgebraSystemInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ProCGroups.InverseSystems.InverseSystem (I := CompletedGroupAlgebraIndexInClass G C) where
  X := CompletedGroupAlgebraStageInClass C R G
  topologicalSpace := fun U => by
    letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
      finite_completedGroupAlgebraQuotientInClass G C hC U
    exact finiteGroupAlgebraTopology R (CompletedGroupAlgebraQuotientInClass G C U)
  map := fun {U V} hUV => completedGroupAlgebraTransitionInClass C R G hUV
  continuous_map := by
    intro U V hUV
    letI : Finite (CompletedGroupAlgebraQuotientInClass G C V) :=
      finite_completedGroupAlgebraQuotientInClass G C hC V
    letI : Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
      finite_completedGroupAlgebraQuotientInClass G C hC U
    exact finiteGroupAlgebra_mapDomainRingHom_continuous R
      (CompletedGroupAlgebraQuotientInClass G C V) (CompletedGroupAlgebraQuotientInClass G C U)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G) (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
  map_id := by
    intro U
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraTransitionInClass_id (R := R) (G := G) C U)) x
  map_comp := by
    intro U V W hUV hVW
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraTransitionInClass_comp (R := R) (G := G) C hUV hVW)) x

instance instRingCompletedGroupAlgebraSystemInClassX
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    Ring ((completedGroupAlgebraSystemInClass C hC R G).X U) := by
  dsimp [completedGroupAlgebraSystemInClass, CompletedGroupAlgebraStageInClass,
    CompletedGroupAlgebraQuotientInClass]
  infer_instance

instance instIsRingSystemCompletedGroupAlgebraSystemInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    IsRingSystem (completedGroupAlgebraSystemInClass C hC R G) where
  map_zero := by
    intro U V hUV
    exact map_zero (completedGroupAlgebraTransitionInClass C R G hUV)
  map_one := by
    intro U V hUV
    exact map_one (completedGroupAlgebraTransitionInClass C R G hUV)
  map_add := by
    intro U V hUV x y
    exact map_add (completedGroupAlgebraTransitionInClass C R G hUV) x y
  map_mul := by
    intro U V hUV x y
    exact map_mul (completedGroupAlgebraTransitionInClass C R G hUV) x y


end

end CompletedGroupAlgebra
