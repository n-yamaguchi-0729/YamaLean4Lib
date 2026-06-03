import CompletedGroupAlgebra.ProfiniteModules.FiniteGroupAlgebra.UnitRepresentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Basic/InClass/Index.lean
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

section InClass

/-- The `C`-indexed open-normal quotient tower for a completed group algebra.  The order is
chosen so that larger indices give finer quotients. -/
abbrev CompletedGroupAlgebraIndexInClass (C : ProCGroups.FiniteGroupClass.{v}) :=
  OrderDual (OpenNormalSubgroupInClass C G)

/-- The finite quotient `G/U` at one `C`-indexed stage. -/
abbrev CompletedGroupAlgebraQuotientInClass (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) : Type v :=
  (openNormalSubgroupInClassSystem C G).X U

/-- Quotients appearing in a finite-only class are finite. -/
theorem finite_completedGroupAlgebraQuotientInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    Finite (CompletedGroupAlgebraQuotientInClass G C U) :=
  hC (OrderDual.ofDual U).2

/-- The terminal `C`-indexed completed-group-algebra quotient, corresponding to `G/G`. -/
def terminalCompletedGroupAlgebraIndexInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    CompletedGroupAlgebraIndexInClass G C :=
  OrderDual.toDual (OpenNormalSubgroupInClass.top (C := C) (G := G))

omit [IsTopologicalGroup G] in
/-- The terminal in-class completed-group-algebra index is below every in-class index. -/
theorem terminalCompletedGroupAlgebraIndexInClass_le
    (C : ProCGroups.FiniteGroupClass.{v})
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    terminalCompletedGroupAlgebraIndexInClass (G := G) C ≤ U := by
  change ((OrderDual.ofDual U).1 : Subgroup G) ≤ (⊤ : Subgroup G)
  exact le_top

variable (R : Type u) [CommRing R]

end InClass

end

end CompletedGroupAlgebra
