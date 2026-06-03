import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/TopologicalGroups.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# ProCGroups / TopologicalGroups / Category

Focused module in the public source tree. It contains declarations used by the library roots and by downstream proof modules.
-/

open CategoryTheory
open scoped Topology

universe u

/-- Bundled topological groups with continuous homomorphisms. -/
@[pp_with_univ]
structure TopGrp where
  carrier : Type u
  [group : Group carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalGroup : IsTopologicalGroup carrier]

attribute [instance] TopGrp.group TopGrp.topologicalSpace TopGrp.isTopologicalGroup

namespace TopGrp

instance instCoeSort : CoeSort TopGrp (Type u) where
  coe G := G.carrier

/-- Bundle an unbundled topological group. -/
abbrev of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : TopGrp where
  carrier := G

/-- Morphisms of topological groups are continuous homomorphisms. -/
@[ext]
structure Hom (G H : TopGrp.{u}) where
  hom' : G →ₜ* H

instance instCategory : Category TopGrp where
  Hom G H := Hom G H
  id G := ⟨ContinuousMonoidHom.id G⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance instConcreteCategory : ConcreteCategory TopGrp (fun G H => G →ₜ* H) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying continuous homomorphism of a morphism. -/
abbrev Hom.hom {G H : TopGrp.{u}} (f : G ⟶ H) : G →ₜ* H :=
  ConcreteCategory.hom (C := TopGrp) f

instance instCoeFunHom {G H : TopGrp.{u}} : CoeFun (G ⟶ H) (fun _ => G → H) where
  coe f := f.hom

@[simp] theorem hom_id {G : TopGrp.{u}} :
    (𝟙 G : G ⟶ G).hom = ContinuousMonoidHom.id G :=
  rfl

@[simp] theorem hom_comp {G H K : TopGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) :
    (f ≫ g).hom = g.hom.comp f.hom :=
  rfl

@[simp] theorem comp_apply {G H K : TopGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) (x : G) :
    (f ≫ g) x = g (f x) :=
  rfl

/-- Morphisms of topological groups are extensional in their underlying continuous homomorphism. -/
@[ext] theorem hom_ext {G H : TopGrp.{u}} {f g : G ⟶ H} (h : f.hom = g.hom) :
    f = g :=
  Hom.ext h

/-- Typecheck a continuous homomorphism as a bundled topological-group morphism. -/
abbrev ofHom {G H : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →ₜ* H) : of G ⟶ of H :=
  ConcreteCategory.ofHom f

end TopGrp

/-- Bundled commutative topological groups with continuous homomorphisms. -/
@[pp_with_univ]
structure CommTopGrp where
  carrier : Type u
  [commGroup : CommGroup carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalGroup : IsTopologicalGroup carrier]

attribute [instance] CommTopGrp.commGroup CommTopGrp.topologicalSpace
  CommTopGrp.isTopologicalGroup

namespace CommTopGrp

instance instCoeSort : CoeSort CommTopGrp (Type u) where
  coe G := G.carrier

/-- Bundle an unbundled commutative topological group. -/
abbrev of (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] :
    CommTopGrp where
  carrier := G

/-- Morphisms of commutative topological groups are continuous homomorphisms. -/
@[ext]
structure Hom (G H : CommTopGrp.{u}) where
  hom' : G →ₜ* H

instance instCategory : Category CommTopGrp where
  Hom G H := Hom G H
  id G := ⟨ContinuousMonoidHom.id G⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance instConcreteCategory : ConcreteCategory CommTopGrp (fun G H => G →ₜ* H) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying continuous homomorphism of a morphism. -/
abbrev Hom.hom {G H : CommTopGrp.{u}} (f : G ⟶ H) : G →ₜ* H :=
  ConcreteCategory.hom (C := CommTopGrp) f

instance instCoeFunHom {G H : CommTopGrp.{u}} : CoeFun (G ⟶ H) (fun _ => G → H) where
  coe f := f.hom

@[simp] theorem hom_id {G : CommTopGrp.{u}} :
    (𝟙 G : G ⟶ G).hom = ContinuousMonoidHom.id G :=
  rfl

@[simp] theorem hom_comp {G H K : CommTopGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) :
    (f ≫ g).hom = g.hom.comp f.hom :=
  rfl

@[simp] theorem comp_apply {G H K : CommTopGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) (x : G) :
    (f ≫ g) x = g (f x) :=
  rfl

/-- Morphisms of commutative topological groups are extensional in their underlying continuous
homomorphism. -/
@[ext] theorem hom_ext {G H : CommTopGrp.{u}} {f g : G ⟶ H} (h : f.hom = g.hom) :
    f = g :=
  Hom.ext h

/-- Typecheck a continuous homomorphism as a bundled commutative topological-group morphism. -/
abbrev ofHom {G H : Type u}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →ₜ* H) : of G ⟶ of H :=
  ConcreteCategory.ofHom f

end CommTopGrp

/-- Forget the commutativity of a bundled commutative topological group. -/
def commTopGrpForgetToTopGrp : CommTopGrp.{u} ⥤ TopGrp.{u} where
  obj G := TopGrp.of G
  map f := TopGrp.ofHom f.hom
  map_id G := by
    apply TopGrp.hom_ext
    rfl
  map_comp f g := by
    apply TopGrp.hom_ext
    rfl
