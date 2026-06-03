import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
import ProCGroups.ProC.Subgroups.Closed
import ProCGroups.Profinite.MathlibBridge

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/Category/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open CategoryTheory Topology

universe u v

/-- The category of pro-`C` groups for a fixed topological pro-`C` predicate. -/
@[pp_with_univ]
structure ProCGrp (ProC : ProCGroups.ProC.ProCGroupPredicate.{u}) where
  /-- The underlying Mathlib profinite group. -/
  toProfiniteGrp : ProfiniteGrp.{u}
  /-- The pro-`C` structure on the underlying profinite group. -/
  [proCGroup : ProCGroups.ProC.ProCGroup ProC toProfiniteGrp]

attribute [instance] ProCGrp.proCGroup

namespace ProCGrp

variable {ProC : ProCGroups.ProC.ProCGroupPredicate.{u}}

/-- A bundled pro-`C` group coerces to its carrier type. -/
instance instCoeSort : CoeSort (ProCGrp ProC) (Type u) where
  coe G := G.toProfiniteGrp

/-- A bundled pro-`C` group inherits the group structure of its underlying profinite group. -/
instance instGroup (G : ProCGrp ProC) : Group G :=
  inferInstanceAs (Group G.toProfiniteGrp)

/-- A bundled pro-`C` group inherits the topology of its underlying profinite group. -/
instance instTopologicalSpace (G : ProCGrp ProC) : TopologicalSpace G :=
  inferInstanceAs (TopologicalSpace G.toProfiniteGrp)

/-- A bundled pro-`C` group inherits the topological group structure of its underlying profinite
group. -/
instance instIsTopologicalGroup (G : ProCGrp ProC) : IsTopologicalGroup G :=
  inferInstanceAs (IsTopologicalGroup G.toProfiniteGrp)

/-- A bundled pro-`C` group inherits compactness from its underlying profinite group. -/
instance instCompactSpace (G : ProCGrp ProC) : CompactSpace G :=
  inferInstanceAs (CompactSpace G.toProfiniteGrp)

/-- A bundled pro-`C` group inherits the Hausdorff property from its underlying profinite group. -/
instance instT2Space (G : ProCGrp ProC) : T2Space G :=
  inferInstanceAs (T2Space G.toProfiniteGrp)

/-- A bundled pro-`C` group inherits total disconnectedness from its underlying profinite group. -/
instance instTotallyDisconnectedSpace (G : ProCGrp ProC) : TotallyDisconnectedSpace G :=
  inferInstanceAs (TotallyDisconnectedSpace G.toProfiniteGrp)

/-- A bundled pro-`C` group carries its registered pro-`C` structure. -/
instance instProCGroup (G : ProCGrp ProC) : ProCGroups.ProC.ProCGroup ProC G :=
  inferInstanceAs (ProCGroups.ProC.ProCGroup ProC G.toProfiniteGrp)

/-- Construct a bundled pro-`C` group from an unbundled topological group with a `ProCGroup`
instance. -/
abbrev of (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ProCGroups.ProC.ProCGroup ProC G] : ProCGrp ProC where
  toProfiniteGrp := by
    letI : CompactSpace G := ProCGroups.ProC.ProCGroup.compactSpace ProC G
    letI : TotallyDisconnectedSpace G :=
      ProCGroups.ProC.ProCGroup.totallyDisconnectedSpace ProC G
    exact ProfiniteGrp.of G
  proCGroup := inferInstance

/-- The carrier of a freshly bundled pro-`C` group is the original type. -/
@[simp] theorem coe_of (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [ProCGroups.ProC.ProCGroup ProC G] :
    (of ProC G : Type u) = G :=
  rfl

/-- The type of morphisms in `ProCGrp`. -/
@[ext]
structure Hom (A B : ProCGrp ProC) where
  /-- The underlying continuous monoid homomorphism. -/
  hom' : A →ₜ* B

/-- Bundled pro-`C` groups form a category with continuous homomorphisms. -/
instance instCategory : Category (ProCGrp ProC) where
  Hom A B := Hom A B
  id A := ⟨ContinuousMonoidHom.id A⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

/-- The category of bundled pro-`C` groups is concrete via continuous homomorphisms. -/
instance instConcreteCategory : ConcreteCategory (ProCGrp ProC) (fun X Y => X →ₜ* Y) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying continuous monoid homomorphism. -/
abbrev Hom.hom {A B : ProCGrp ProC} (f : A ⟶ B) : A →ₜ* B :=
  ConcreteCategory.hom (C := ProCGrp ProC) f

/-- Morphisms of bundled pro-`C` groups coerce to functions. -/
instance instCoeFunHom {A B : ProCGrp ProC} : CoeFun (A ⟶ B) (fun _ => A → B) where
  coe f := f.hom

/-- The underlying homomorphism of the identity morphism is the identity continuous homomorphism. -/
@[simp] theorem hom_id {A : ProCGrp ProC} :
    (𝟙 A : A ⟶ A).hom = ContinuousMonoidHom.id A :=
  rfl

/-- The identity morphism acts as the identity function. -/
@[simp] theorem id_apply (A : ProCGrp ProC) (a : A) :
    (𝟙 A : A ⟶ A) a = a := by
  simp only [hom_id, ContinuousMonoidHom.id_toFun]

/-- The underlying homomorphism of a composite is the composite of underlying homomorphisms. -/
@[simp] theorem hom_comp {A B C : ProCGrp ProC} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = g.hom.comp f.hom :=
  rfl

/-- Composition of morphisms agrees with composition of functions. -/
@[simp] theorem comp_apply {A B C : ProCGrp ProC} (f : A ⟶ B) (g : B ⟶ C) (a : A) :
    (f ≫ g) a = g (f a) := by
  rfl

/-- Morphisms of pro-`C` groups are extensional in their underlying continuous homomorphisms. -/
@[ext] theorem hom_ext {A B : ProCGrp ProC} {f g : A ⟶ B} (hf : f.hom = g.hom) :
    f = g :=
  Hom.ext hf

/-- Typecheck a continuous monoid homomorphism as a morphism in `ProCGrp`. -/
abbrev ofHom {X Y : Type u}
    [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [ProCGroups.ProC.ProCGroup ProC X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    [ProCGroups.ProC.ProCGroup ProC Y]
    (f : X →ₜ* Y) : of ProC X ⟶ of ProC Y :=
  ConcreteCategory.ofHom f

/-- `ofHom` has the prescribed underlying continuous homomorphism. -/
@[simp] theorem hom_ofHom {X Y : Type u}
    [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [ProCGroups.ProC.ProCGroup ProC X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    [ProCGroups.ProC.ProCGroup ProC Y]
    (f : X →ₜ* Y) : (ofHom (ProC := ProC) f).hom = f :=
  rfl

/-- Reconstructing a morphism from its underlying continuous homomorphism gives the original
morphism. -/
@[simp] theorem ofHom_hom {A B : ProCGrp ProC} (f : A ⟶ B) :
    ConcreteCategory.ofHom (C := ProCGrp ProC) f.hom = f :=
  rfl

/-- `ofHom` sends the identity continuous homomorphism to the identity morphism. -/
@[simp] theorem ofHom_id {X : Type u}
    [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [ProCGroups.ProC.ProCGroup ProC X] :
    ofHom (ProC := ProC) (ContinuousMonoidHom.id X) = 𝟙 (of ProC X) :=
  rfl

/-- `ofHom` sends composition of continuous homomorphisms to categorical composition. -/
@[simp] theorem ofHom_comp {X Y Z : Type u}
    [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [ProCGroups.ProC.ProCGroup ProC X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    [ProCGroups.ProC.ProCGroup ProC Y]
    [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z]
    [ProCGroups.ProC.ProCGroup ProC Z]
    (f : X →ₜ* Y) (g : Y →ₜ* Z) :
    ofHom (ProC := ProC) (g.comp f) = ofHom (ProC := ProC) f ≫ ofHom (ProC := ProC) g :=
  rfl

/-- Applying a morphism built by `ofHom` is applying the original continuous homomorphism. -/
@[simp] theorem ofHom_apply {X Y : Type u}
    [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [ProCGroups.ProC.ProCGroup ProC X]
    [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y]
    [ProCGroups.ProC.ProCGroup ProC Y]
    (f : X →ₜ* Y) (x : X) :
    ofHom (ProC := ProC) f x = f x :=
  rfl

/-- Forget a bundled pro-`C` group to its underlying profinite group. -/
instance instHasForgetToProfiniteGrp : HasForget₂ (ProCGrp ProC) ProfiniteGrp where
  forget₂ :=
    { obj := fun G => G.toProfiniteGrp
      map := fun f => ProfiniteGrp.ofHom f.hom }

/-- Forget a bundled pro-`C` group to its underlying abstract group. -/
instance instHasForgetToGrpCat : HasForget₂ (ProCGrp ProC) GrpCat where
  forget₂ :=
    { obj := fun G => GrpCat.of G
      map := fun f => GrpCat.ofHom f.hom.toMonoidHom }

/-- The forgetful functor from pro-`C` groups to profinite groups is faithful. -/
instance instFaithfulForgetToProfiniteGrp : (forget₂ (ProCGrp ProC) ProfiniteGrp).Faithful where
  map_injective := by
    intro X Y f g h
    ext x
    exact CategoryTheory.congr_fun h x

/-- Every Mathlib profinite group is a pro-`C` group for the all-finite predicate. -/
instance allFiniteProCGroup (G : ProfiniteGrp.{u}) :
    ProCGroups.ProC.ProCGroup ProCGroups.ProC.allFiniteProC G :=
  ProCGroups.ProC.ProCGroup.of_isProCGroup ProCGroups.ProC.allFiniteProC G
    (ProCGroups.ProC.allFiniteProC_isProCGroup_of_profinite
      (ProCGroups.IsProfiniteGroup.of_profiniteGrp G))

/-- A finite group in the finite quotient class of `ProC`, with the discrete topology, is a
bundled pro-`C` group. -/
def ofFiniteGrp
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    (G : FiniteGrp.{u}) (hG : ProC.finiteQuotientClass G) : ProCGrp ProC := by
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  letI : IsTopologicalGroup G := inferInstance
  letI : ProCGroups.ProC.ProCGroup ProC G :=
    ProCGroups.ProC.ProCGroup.of_finite_discrete ProC hG
  exact of ProC G

/-- Closed subgroups of pro-`C` groups are pro-`C`. -/
def ofClosedSubgroup
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.HasFiniteQuotientHereditary]
    [ProC.DeterminedByFiniteQuotients]
    (G : ProCGrp ProC) (H : ClosedSubgroup G) : ProCGrp ProC where
  toProfiniteGrp := ProfiniteGrp.ofClosedSubgroup (G := G.toProfiniteGrp) H
  proCGroup := by
    simpa using
      (ProCGroups.ProC.ProCGroup.of_closedSubgroup
        (G := G) ProC H)

/-- Transport a pro-`C` group structure across a continuous multiplicative equivalence. -/
noncomputable def ofContinuousMulEquiv
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    (G : ProCGrp ProC) {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (e : G ≃ₜ* H) : ProCGrp ProC := by
  letI : ProCGroups.ProC.ProCGroup ProC H :=
    ProCGroups.ProC.ProCGroup.ofContinuousMulEquiv (G := G) ProC e
  exact of ProC H

/-- Products of pro-`C` groups are pro-`C` when the finite quotient class is a formation. -/
def pi
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    {α : Type u} (β : α → ProCGrp ProC) : ProCGrp ProC := by
  let Pβ : α → ProfiniteGrp.{u} := fun a => (β a).toProfiniteGrp
  letI : ProCGroups.ProC.ProCGroup ProC ((a : α) → β a) :=
    ProCGroups.ProC.ProCGroup.pi (β := fun a => (β a : Type u)) ProC
  exact
    { toProfiniteGrp := ProfiniteGrp.pi Pβ
      proCGroup := by
        simpa [Pβ, ProfiniteGrp.pi] using
          (inferInstance : ProCGroups.ProC.ProCGroup ProC ((a : α) → β a)) }

/-- Quotients by open normal subgroups of pro-`C` groups are pro-`C`. -/
def quotientOpenNormalSubgroup
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    (G : ProCGrp ProC) (U : OpenNormalSubgroup G) : ProCGrp ProC := by
  letI : ProCGroups.ProC.ProCGroup ProC (G ⧸ (U : Subgroup G)) :=
    ProCGroups.ProC.ProCGroup.quotient_openNormalSubgroup
      (G := G) ProC U
  exact of ProC (G ⧸ (U : Subgroup G))

/-- Quotients by open normal subgroups from the finite-quotient class family are pro-`C`. -/
def quotientOpenNormalSubgroupInClass
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    (G : ProCGrp ProC)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass ProC.finiteQuotientClass G) :
    ProCGrp ProC :=
  quotientOpenNormalSubgroup ProC G U.1

/-- Quotients by closed normal subgroups of pro-`C` groups are pro-`C`. -/
def quotientClosedNormalSubgroup
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.DeterminedByFiniteQuotients]
    (G : ProCGrp ProC) (K : Subgroup G) [K.Normal] (hK : IsClosed (K : Set G)) :
    ProCGrp ProC := by
  letI : ProCGroups.ProC.ProCGroup ProC (G ⧸ K) :=
    ProCGroups.ProC.ProCGroup.quotient_closedNormalSubgroup
      (G := G) ProC K hK
  exact of ProC (G ⧸ K)

/-- The range of a morphism of pro-`C` groups, with its induced topology, is pro-`C`. -/
def range
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientFormation] [ProC.DeterminedByFiniteQuotients]
    {A B : ProCGrp ProC} (f : A ⟶ B) : ProCGrp ProC := by
  letI : ProCGroups.ProC.ProCGroup ProC f.hom.toMonoidHom.range :=
    ProCGroups.ProC.ProCGroup.range
      (G := A) (H := B) ProC f.hom
  exact of ProC f.hom.toMonoidHom.range

/-- The kernel subgroup of a morphism of pro-`C` groups, with its induced topology, is pro-`C`. -/
def kernel
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.HasFiniteQuotientHereditary]
    [ProC.DeterminedByFiniteQuotients]
    {A B : ProCGrp ProC} (f : A ⟶ B) : ProCGrp ProC := by
  let K : Subgroup A := f.hom.toMonoidHom.ker
  have hK : IsClosed (K : Set A) := by
    dsimp [K]
    exact f.hom.isClosed_ker
  letI : ProCGroups.ProC.ProCGroup ProC K :=
    ProCGroups.ProC.ProCGroup.of_isClosed_subgroup
      (G := A) ProC K hK
  exact of ProC K

end ProCGrp
