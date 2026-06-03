import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.Category.TopCat.Basic
import ProCGroups.InverseSystems.CompatibilityAndSurjectivity

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/InverseSystems/CategoryBridge.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Category bridge for concrete inverse systems

The inverse-system API is a concrete, calculation-oriented wrapper for
stagewise topological inverse limits.  This file exposes the associated
`TopCat` diagram without replacing the concrete API by a categorical one.
-/

open CategoryTheory

namespace ProCGroups
namespace InverseSystems

universe u v

section

variable {I : Type u} [Preorder I]

namespace InverseSystem

variable (S : InverseSystem.{u, v} (I := I))

/-- The categorical `TopCat` diagram associated to a concrete inverse system. -/
def toFunctor : Iᵒᵖ ⥤ TopCat.{v} where
  obj i := TopCat.of (S.X i.unop)
  map {i j} hij := TopCat.ofHom ⟨S.map hij.unop.le, S.continuous_map hij.unop.le⟩
  map_id i := by
    ext x
    exact S.map_id_apply i.unop x
  map_comp {i j k} hij hjk := by
    ext x
    exact (S.map_comp_apply hjk.unop.le hij.unop.le x).symm

@[simp] theorem toFunctor_map_apply {i j : Iᵒᵖ} (hij : i ⟶ j)
    (x : S.X i.unop) :
    S.toFunctor.map hij x = S.map hij.unop.le x :=
  rfl

namespace Morphism

variable {S}
variable {T : InverseSystem.{u, v} (I := I)}

/-- A concrete morphism of inverse systems gives a natural transformation of
the associated `TopCat` diagrams. -/
def toNatTrans (Θ : S.Morphism T) : S.toFunctor ⟶ T.toFunctor where
  app i := TopCat.ofHom ⟨Θ.map i.unop, Θ.continuous_map i.unop⟩
  naturality {i j} hij := by
    ext x
    exact (Θ.comm_apply hij.unop.le x).symm

@[simp] theorem toNatTrans_app_apply (Θ : S.Morphism T) (i : Iᵒᵖ)
    (x : S.X i.unop) :
    Θ.toNatTrans.app i x = Θ.map i.unop x :=
  rfl

end Morphism

end InverseSystem

end

end InverseSystems
end ProCGroups
