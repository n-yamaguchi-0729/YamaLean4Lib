import ProCGroups.Topologies.OpenSubgroup
import ProCGroups.Topologies.Conjugation
import ProCGroups.TopologicalGroups
import ProCGroups.Abelian.TopologicalAbelianization

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Abelian/TopologicalAbelianizationFunctoriality.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Functoriality of topological abelianization

Develops the functorial and categorical universal property of topological abelianization, together with the conjugation action on the abelianization of an open normal subgroup.
-/

open CategoryTheory
open scoped Topology

namespace ProCGroups.Abelian

universe u

/-- Bundled commutative `T1` topological groups with continuous homomorphisms. -/
@[pp_with_univ]
structure T1CommTopGrp where
  carrier : Type u
  [commGroup : CommGroup carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalGroup : IsTopologicalGroup carrier]
  [t1Space : T1Space carrier]

attribute [instance] T1CommTopGrp.commGroup T1CommTopGrp.topologicalSpace
  T1CommTopGrp.isTopologicalGroup T1CommTopGrp.t1Space

namespace T1CommTopGrp

instance instCoeSort : CoeSort T1CommTopGrp (Type u) where
  coe G := G.carrier

/-- Bundle an unbundled commutative `T1` topological group. -/
abbrev of (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T1Space G] : T1CommTopGrp where
  carrier := G

/-- Morphisms of commutative `T1` topological groups are continuous homomorphisms. -/
@[ext]
structure Hom (G H : T1CommTopGrp.{u}) where
  hom' : G →ₜ* H

instance instCategory : Category T1CommTopGrp where
  Hom G H := Hom G H
  id G := ⟨ContinuousMonoidHom.id G⟩
  comp f g := ⟨g.hom'.comp f.hom'⟩

instance instConcreteCategory : ConcreteCategory T1CommTopGrp (fun G H => G →ₜ* H) where
  hom f := f.hom'
  ofHom f := ⟨f⟩

/-- The underlying continuous homomorphism of a morphism. -/
abbrev Hom.hom {G H : T1CommTopGrp.{u}} (f : G ⟶ H) : G →ₜ* H :=
  ConcreteCategory.hom (C := T1CommTopGrp) f

instance instCoeFunHom {G H : T1CommTopGrp.{u}} : CoeFun (G ⟶ H) (fun _ => G → H) where
  coe f := f.hom

@[simp] theorem hom_id {G : T1CommTopGrp.{u}} :
    (𝟙 G : G ⟶ G).hom = ContinuousMonoidHom.id G :=
  rfl

@[simp] theorem hom_comp {G H K : T1CommTopGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) :
    (f ≫ g).hom = g.hom.comp f.hom :=
  rfl

@[simp] theorem comp_apply {G H K : T1CommTopGrp.{u}} (f : G ⟶ H) (g : H ⟶ K) (x : G) :
    (f ≫ g) x = g (f x) :=
  rfl

/-- Morphisms of commutative `T1` topological groups are extensional in their underlying continuous
homomorphism. -/
@[ext] theorem hom_ext {G H : T1CommTopGrp.{u}} {f g : G ⟶ H} (h : f.hom = g.hom) :
    f = g :=
  Hom.ext h

/-- Typecheck a continuous homomorphism as a bundled commutative `T1` topological-group morphism. -/
abbrev ofHom {G H : Type u}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T1Space G]
    [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T1Space H]
    (f : G →ₜ* H) : of G ⟶ of H :=
  ConcreteCategory.ofHom f

end T1CommTopGrp

/-- Forget the `T1` and commutativity structure of a bundled commutative `T1` topological group. -/
def t1CommTopGrpForgetToTopGrp : T1CommTopGrp.{u} ⥤ TopGrp.{u} where
  obj G := TopGrp.of G
  map f := TopGrp.ofHom f.hom
  map_id G := by
    apply TopGrp.hom_ext
    rfl
  map_comp f g := by
    apply TopGrp.hom_ext
    rfl

/-- Forget only the `T1` structure of a bundled commutative `T1` topological group. -/
def t1CommTopGrpForgetToCommTopGrp : T1CommTopGrp.{u} ⥤ CommTopGrp.{u} where
  obj G := CommTopGrp.of G
  map f := CommTopGrp.ofHom f.hom
  map_id G := by
    apply CommTopGrp.hom_ext
    rfl
  map_comp f g := by
    apply CommTopGrp.hom_ext
    rfl

/-- Topological abelianization as a functor from topological groups to commutative topological
groups. -/
noncomputable def topologicalAbelianizationFunctor : TopGrp.{u} ⥤ CommTopGrp.{u} where
  obj G := CommTopGrp.of (TopologicalAbelianization G)
  map {G H} f := CommTopGrp.ofHom (TopologicalAbelianization.map f.hom)
  map_id G := by
    apply CommTopGrp.hom_ext
    exact TopologicalAbelianization.map_id G
  map_comp f g := by
    apply CommTopGrp.hom_ext
    exact TopologicalAbelianization.map_comp g.hom f.hom

@[simp] theorem topologicalAbelianizationFunctor_map_apply_mk
    {G H : TopGrp.{u}} (f : G ⟶ H) (x : G) :
    topologicalAbelianizationFunctor.map f (TopologicalAbelianization.mk G x) =
      TopologicalAbelianization.mk H (f x) :=
  rfl

/-- Topological abelianization as a functor from topological groups to commutative `T1`
topological groups. -/
noncomputable def topologicalAbelianizationT1Functor : TopGrp.{u} ⥤ T1CommTopGrp.{u} where
  obj G := T1CommTopGrp.of (TopologicalAbelianization G)
  map {G H} f := T1CommTopGrp.ofHom (TopologicalAbelianization.map f.hom)
  map_id G := by
    apply T1CommTopGrp.hom_ext
    exact TopologicalAbelianization.map_id G
  map_comp f g := by
    apply T1CommTopGrp.hom_ext
    exact TopologicalAbelianization.map_comp g.hom f.hom

@[simp] theorem topologicalAbelianizationT1Functor_map_apply_mk
    {G H : TopGrp.{u}} (f : G ⟶ H) (x : G) :
    topologicalAbelianizationT1Functor.map f (TopologicalAbelianization.mk G x) =
      TopologicalAbelianization.mk H (f x) :=
  rfl

/-- Category-level Hom equivalence expressing the universal property of topological
abelianization for commutative `T1` targets. -/
noncomputable def topologicalAbelianizationHomEquiv
    (G : TopGrp.{u}) (A : CommTopGrp.{u}) [T1Space A] :
    (topologicalAbelianizationFunctor.obj G ⟶ A) ≃
      (G ⟶ commTopGrpForgetToTopGrp.obj A) where
  toFun φ := TopGrp.ofHom (φ.hom.comp (TopologicalAbelianization.mkₜ G))
  invFun f := CommTopGrp.ofHom (TopologicalAbelianization.lift f.hom)
  left_inv φ := by
    apply CommTopGrp.hom_ext
    apply TopologicalAbelianization.hom_ext
    intro x
    rfl
  right_inv f := by
    apply TopGrp.hom_ext
    ext x
    rfl

@[simp] theorem topologicalAbelianizationHomEquiv_apply_hom
    (G : TopGrp.{u}) (A : CommTopGrp.{u}) [T1Space A]
    (φ : topologicalAbelianizationFunctor.obj G ⟶ A) :
    (topologicalAbelianizationHomEquiv G A φ).hom =
      φ.hom.comp (TopologicalAbelianization.mkₜ G) :=
  rfl

@[simp] theorem topologicalAbelianizationHomEquiv_symm_apply_mk
    (G : TopGrp.{u}) (A : CommTopGrp.{u}) [T1Space A]
    (f : G ⟶ commTopGrpForgetToTopGrp.obj A) (x : G) :
    (topologicalAbelianizationHomEquiv G A).symm f
      (TopologicalAbelianization.mk G x) = f x :=
  rfl

/-- The topological abelianization of the top open subgroup is canonically the same as the
topological abelianization of the ambient group. -/
noncomputable def topologicalAbelianizationTopMulEquiv
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    TopologicalAbelianization ↥((⊤ : OpenSubgroup G) : Subgroup G) ≃ₜ*
      TopologicalAbelianization G :=
  TopologicalAbelianization.congr
    (G := ↥((⊤ : OpenSubgroup G) : Subgroup G))
    (H := G)
    (OpenSubgroup.topContinuousMulEquiv G)

/-- The abelianization equivalence for a topological group equivalence sends representatives to representatives. -/
@[simp] theorem topologicalAbelianizationTopMulEquiv_apply_mk
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (x : ↥((⊤ : OpenSubgroup G) : Subgroup G)) :
    topologicalAbelianizationTopMulEquiv
        (G := G) (TopologicalAbelianization.mk ↥((⊤ : OpenSubgroup G) : Subgroup G) x) =
      TopologicalAbelianization.mk G x.1 := by
  simpa [topologicalAbelianizationTopMulEquiv] using
    (TopologicalAbelianization.congr_apply_mk
      (OpenSubgroup.topContinuousMulEquiv G) x)

/-- The quotient `G/N` acts on the topological abelianization of `N` by conjugation. -/
noncomputable def quotientConjugationTopologicalAbelianizationMap
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] :
    (G ⧸ N) →* MulAut (TopologicalAbelianization N) := by
  let K : Subgroup N := Subgroup.closedCommutator N
  have hKchar : K.TopologicallyCharacteristic :=
    Subgroup.closedCommutator_topologicallyCharacteristic (G := N)
  exact ProCGroups.Topologies.quotientConjugationOnTopologicallyCharacteristicQuotient
    (G := G) N K
    (fun n x => by
      have hcomm :
          ⁅n, x⁆ ∈ Subgroup.closedCommutator N :=
        Subgroup.commutator_le_closedCommutator N
          (Subgroup.commutator_mem_commutator (Subgroup.mem_top n) (Subgroup.mem_top x))
      have hconj : (MulAut.conjNormal (n : G)) x = n * x * n⁻¹ := by
        ext
        simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, InvMemClass.coe_inv]
      rw [hconj]
      simpa [K, commutatorElement_def, mul_assoc] using hcomm)

/-- The continuous self-equivalence of topological abelianization induced by conjugation by a
representative. -/
noncomputable def conjugationTopologicalAbelianizationContinuousAut
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (g : G) :
    TopologicalAbelianization N ≃ₜ* TopologicalAbelianization N :=
  TopologicalAbelianization.congr (Subgroup.conjNormalContinuousMulEquiv (G := G) N g)

/-- The representative-wise continuous automorphism has the same underlying algebraic action as
`quotientConjugationTopologicalAbelianizationMap`. -/
@[simp] theorem conjugationTopologicalAbelianizationContinuousAut_toMulAut_apply_mk
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (g : G) (n : N) :
    conjugationTopologicalAbelianizationContinuousAut (G := G) N g
      (TopologicalAbelianization.mk N n) =
        quotientConjugationTopologicalAbelianizationMap (G := G) (N := N)
          (QuotientGroup.mk' N g) (TopologicalAbelianization.mk N n) := by
  rfl

/-- The conjugation action on a quotient induces the expected map on topological abelianization representatives. -/
@[simp] theorem quotientConjugationTopologicalAbelianizationMap_mk_apply_mk
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (g : G) (n : N) :
    quotientConjugationTopologicalAbelianizationMap (G := G) (N := N)
      (QuotientGroup.mk' N g) (TopologicalAbelianization.mk N n) =
        TopologicalAbelianization.mk N ((MulAut.conjNormal g) n) := by
  dsimp [quotientConjugationTopologicalAbelianizationMap, TopologicalAbelianization.mk,
    TopologicalAbelianization.mkₜ]
  rfl

/-- If every commutator correction lies in the closed commutator subgroup, the induced conjugation
action on the topological abelianization is trivial. -/
theorem quotientConjugationTopologicalAbelianizationMap_mk_eq_one_of_commutator_mem_closure
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] {x : G}
    (hx :
      ∀ n : N,
        (((MulAut.conjNormal x) n) * n⁻¹ : N) ∈ Subgroup.closedCommutator N) :
    quotientConjugationTopologicalAbelianizationMap (G := G) (N := N)
      (QuotientGroup.mk' N x) = 1 := by
  ext a
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.closedCommutator N) a
  exact
    (QuotientGroup.eq_iff_div_mem (N := Subgroup.closedCommutator N)
      (x := (MulAut.conjNormal x) n) (y := n)).2 (by
        simpa [div_eq_mul_inv] using hx n)

/-- The conjugation action fixes a representative exactly when the correction term lies in the
closed commutator subgroup. -/
theorem quotientConjugationTopologicalAbelianizationMap_mk_apply_mk_eq_iff
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] {x : G} {n : N} :
    quotientConjugationTopologicalAbelianizationMap (G := G) (N := N)
        (QuotientGroup.mk' N x) (TopologicalAbelianization.mk N n) =
      TopologicalAbelianization.mk N n ↔
    (((MulAut.conjNormal x) n) * n⁻¹ : N) ∈ Subgroup.closedCommutator N := by
  rw [quotientConjugationTopologicalAbelianizationMap_mk_apply_mk]
  simpa [div_eq_mul_inv] using
    (QuotientGroup.eq_iff_div_mem
      (N := Subgroup.closedCommutator N)
      (x := (MulAut.conjNormal x) n) (y := n))

/-- The induced conjugation action is trivial exactly when every correction term lies in the
closed commutator subgroup. -/
theorem quotientConjugationTopologicalAbelianizationMap_mk_eq_one_iff
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] {x : G} :
    quotientConjugationTopologicalAbelianizationMap (G := G) (N := N)
        (QuotientGroup.mk' N x) = 1 ↔
      ∀ n : N,
        (((MulAut.conjNormal x) n) * n⁻¹ : N) ∈ Subgroup.closedCommutator N := by
  constructor
  · intro h n
    have hpoint :=
      congrArg
        (fun φ : MulAut (TopologicalAbelianization N) => φ (TopologicalAbelianization.mk N n))
        h
    exact
      (quotientConjugationTopologicalAbelianizationMap_mk_apply_mk_eq_iff
        (G := G) (N := N) (x := x) (n := n)).1 (by simpa using hpoint)
  · intro hx
    exact quotientConjugationTopologicalAbelianizationMap_mk_eq_one_of_commutator_mem_closure
      (G := G) (N := N) (x := x) hx

/-- Central elements act trivially on the topological abelianization of a normal subgroup. -/
theorem quotientConjugationTopologicalAbelianizationMap_mk_eq_one_of_mem_center
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] {x : G} (hx : x ∈ Subgroup.center G) :
    quotientConjugationTopologicalAbelianizationMap (G := G) (N := N)
      (QuotientGroup.mk' N x) = 1 := by
  apply quotientConjugationTopologicalAbelianizationMap_mk_eq_one_of_commutator_mem_closure
    (G := G) (N := N)
  intro n
  have hxn : x * (n : G) = (n : G) * x := by
    exact (Subgroup.mem_center_iff.mp hx (n : G)).symm
  have hconj : MulAut.conjNormal x n = n := by
    ext
    rw [MulAut.conjNormal_apply]
    simp only [hxn, mul_assoc, mul_inv_cancel, mul_one]
  simp only [hconj, mul_inv_cancel, one_mem]

/-- If a representative commutes with an element of `N`, then the induced action fixes its class in
the topological abelianization. -/
theorem quotientConjAbMap_apply_mk_of_commute
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] {g : G} {x : N}
    (hgx : g * (x : G) = (x : G) * g) :
    quotientConjugationTopologicalAbelianizationMap (G := G) (N := N)
      (QuotientGroup.mk' N g) (TopologicalAbelianization.mk N x) =
        TopologicalAbelianization.mk N x := by
  have hconj : (MulAut.conjNormal g) x = x := by
    ext
    rw [MulAut.conjNormal_apply]
    simp only [hgx, mul_assoc, mul_inv_cancel, mul_one]
  rw [quotientConjugationTopologicalAbelianizationMap_mk_apply_mk, hconj]

/-- The image of `S ∩ U` in the topological abelianization of `U`. -/
noncomputable def subgroupImageInTopologicalAbelianization
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (S : Subgroup Q) (U : OpenNormalSubgroup Q) :
    Subgroup (TopologicalAbelianization ↥(U : Subgroup Q)) :=
  (((S ⊓ (U : Subgroup Q)).subgroupOf (U : Subgroup Q)).map
    (TopologicalAbelianization.mk ↥(U : Subgroup Q)))

@[simp] theorem mem_subgroupImageInTopologicalAbelianization_iff
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (S : Subgroup Q) (U : OpenNormalSubgroup Q)
    (y : TopologicalAbelianization ↥(U : Subgroup Q)) :
    y ∈ subgroupImageInTopologicalAbelianization (Q := Q) S U ↔
      ∃ x : ↥(U : Subgroup Q), (x : Q) ∈ S ∧ TopologicalAbelianization.mk _ x = y := by
  simp only [subgroupImageInTopologicalAbelianization, ContinuousMonoidHom.coe_toMonoidHom,
  Subgroup.inf_subgroupOf_right, Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_coe, Subtype.exists,
  OpenSubgroup.mem_toSubgroup, exists_and_left]

/-- Enlarging the ambient subgroup `S` enlarges its image in the abelianization of `U`. -/
theorem subgroupImageInTopologicalAbelianization_mono_left
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    {S T : Subgroup Q} (hST : S ≤ T) (U : OpenNormalSubgroup Q) :
    subgroupImageInTopologicalAbelianization (Q := Q) S U ≤
      subgroupImageInTopologicalAbelianization (Q := Q) T U := by
  intro y hy
  rcases (mem_subgroupImageInTopologicalAbelianization_iff (Q := Q) S U y).1 hy with
    ⟨x, hxS, hxy⟩
  exact (mem_subgroupImageInTopologicalAbelianization_iff (Q := Q) T U y).2
    ⟨x, hST hxS, hxy⟩

/-- The map on abelianizations induced by an inclusion of open normal subgroups. -/
noncomputable def topologicalAbelianizationMapOfOpenNormalSubgroupLe
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    {U V : OpenNormalSubgroup Q} (hUV : (U : Subgroup Q) ≤ (V : Subgroup Q)) :
    TopologicalAbelianization ↥(U : Subgroup Q) →ₜ*
      TopologicalAbelianization ↥(V : Subgroup Q) :=
  TopologicalAbelianization.map
    { toMonoidHom := Subgroup.inclusion hUV
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val }

@[simp] theorem topologicalAbelianizationMapOfOpenNormalSubgroupLe_apply_mk
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    {U V : OpenNormalSubgroup Q} (hUV : (U : Subgroup Q) ≤ (V : Subgroup Q))
    (x : ↥(U : Subgroup Q)) :
    topologicalAbelianizationMapOfOpenNormalSubgroupLe (Q := Q) hUV
      (TopologicalAbelianization.mk ↥(U : Subgroup Q) x) =
        TopologicalAbelianization.mk ↥(V : Subgroup Q) ⟨x.1, hUV x.2⟩ :=
  rfl

/-- Under an inclusion `U ≤ V`, the image from `U` maps into the image from `V`. -/
theorem subgroupImageInTopologicalAbelianization_map_le_of_openNormalSubgroup_le
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (S : Subgroup Q) {U V : OpenNormalSubgroup Q}
    (hUV : (U : Subgroup Q) ≤ (V : Subgroup Q)) :
    (subgroupImageInTopologicalAbelianization (Q := Q) S U).map
        (topologicalAbelianizationMapOfOpenNormalSubgroupLe (Q := Q) hUV).toMonoidHom ≤
      subgroupImageInTopologicalAbelianization (Q := Q) S V := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rcases (mem_subgroupImageInTopologicalAbelianization_iff (Q := Q) S U x).1 hx with
    ⟨a, haS, hax⟩
  rw [← hax]
  exact (mem_subgroupImageInTopologicalAbelianization_iff (Q := Q) S V _).2
    ⟨⟨a.1, hUV a.2⟩, haS, rfl⟩

/-- Comap form of `subgroupImageInTopologicalAbelianization_map_le_of_openNormalSubgroup_le`. -/
theorem subgroupImageInTopologicalAbelianization_le_comap_of_openNormalSubgroup_le
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (S : Subgroup Q) {U V : OpenNormalSubgroup Q}
    (hUV : (U : Subgroup Q) ≤ (V : Subgroup Q)) :
    subgroupImageInTopologicalAbelianization (Q := Q) S U ≤
      (subgroupImageInTopologicalAbelianization (Q := Q) S V).comap
        (topologicalAbelianizationMapOfOpenNormalSubgroupLe (Q := Q) hUV).toMonoidHom :=
  Subgroup.map_le_iff_le_comap.mp
    (subgroupImageInTopologicalAbelianization_map_le_of_openNormalSubgroup_le
      (Q := Q) S hUV)

namespace OpenNormalAbelianizationImage

/-- The image of `S` has finite abstract index in the topological abelianization of every open
normal supergroup of `K`. -/
def FiniteAbstractIndex
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (S K : Subgroup Q) : Prop :=
  ∀ U : OpenNormalSubgroup Q, K ≤ (U : Subgroup Q) →
    Finite
      ((TopologicalAbelianization ↥(U : Subgroup Q)) ⧸
        subgroupImageInTopologicalAbelianization (Q := Q) S U)

/-- The topological closure of the image of `S ∩ U` in the topological abelianization of `U`. -/
noncomputable def closedSubgroupImageInTopologicalAbelianization
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (S : Subgroup Q) (U : OpenNormalSubgroup Q) :
    Subgroup (TopologicalAbelianization ↥(U : Subgroup Q)) :=
  (subgroupImageInTopologicalAbelianization (Q := Q) S U).topologicalClosure

@[simp] theorem closedSubgroupImageInTopologicalAbelianization_eq_topologicalClosure
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (S : Subgroup Q) (U : OpenNormalSubgroup Q) :
    closedSubgroupImageInTopologicalAbelianization (Q := Q) S U =
      (subgroupImageInTopologicalAbelianization (Q := Q) S U).topologicalClosure :=
  rfl

/-- The closed image of `S` is open in every open normal supergroup of `K`. -/
def OpenClosure
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (S K : Subgroup Q) : Prop :=
  ∀ U : OpenNormalSubgroup Q, K ≤ (U : Subgroup Q) →
    IsOpen
      ((closedSubgroupImageInTopologicalAbelianization (Q := Q) S U :
          Subgroup (TopologicalAbelianization ↥(U : Subgroup Q))) : Set
          (TopologicalAbelianization ↥(U : Subgroup Q)))

/-- The image of `S` is closed and has finite quotient in every open normal supergroup of `K`. -/
def FiniteTopologicalIndex
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (S K : Subgroup Q) : Prop :=
  ∀ U : OpenNormalSubgroup Q, K ≤ (U : Subgroup Q) →
    IsClosed
        ((subgroupImageInTopologicalAbelianization (Q := Q) S U :
            Subgroup (TopologicalAbelianization ↥(U : Subgroup Q))) : Set
            (TopologicalAbelianization ↥(U : Subgroup Q))) ∧
      Finite
        ((TopologicalAbelianization ↥(U : Subgroup Q)) ⧸
          subgroupImageInTopologicalAbelianization (Q := Q) S U)

/-- Finite topological index includes finite abstract index as its quotient-size component. -/
theorem finiteAbstractIndex_of_finiteTopologicalIndex
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    {S K : Subgroup Q}
    (h : FiniteTopologicalIndex (Q := Q) S K) :
    FiniteAbstractIndex (Q := Q) S K :=
  fun U hKU => (h U hKU).2

end OpenNormalAbelianizationImage

end ProCGroups.Abelian
