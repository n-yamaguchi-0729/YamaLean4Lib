import ProCGroups.FiniteGroups.AllFinite
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import ProCGroups.Profinite.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/OpenNormalSubgroups/ProCGroup.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Concrete pro-C groups via open normal quotient bases

For a finite quotient class `C`, `IsProCGroup C G` is the main public predicate. The basis
predicates in this file, including `HasOpenNormalBasisInClass C G` and
`HasExactOpenNormalQuotientBasisInClass C G`, are auxiliary recognition principles and
construction tools. Closure assumptions such as `FiniteGroupClass.Formation C` belong on the
finite class `C`; abstract `ProCGroupPredicate` wrappers are reserved for bundled theorem
families that need to carry those assumptions through a generic predicate parameter.
-/

namespace ProCGroups.ProC

universe u v

section

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A neighborhood-basis formulation using open normal subgroups whose quotients lie in `C`.

We isolate it as a separate predicate because it is the main usable local output for later
formalization steps. -/
def HasOpenNormalBasisInClass (C : FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ W : Set G, IsOpen W → (1 : G) ∈ W →
    ∃ U : OpenNormalSubgroup G,
      ((U : Subgroup G) : Set G) ⊆ W ∧ C (G ⧸ (U : Subgroup G))

namespace HasOpenNormalBasisInClass

/-- Enlarge the finite-group class in an open-normal basis. -/
theorem mono {C D : FiniteGroupClass.{u}} {G : Type u} [Group G] [TopologicalSpace G]
    (hbasis : HasOpenNormalBasisInClass C G)
    (hmono : ∀ {Q : Type u} [Group Q], C Q → D Q) :
    HasOpenNormalBasisInClass D G := by
  intro W hW h1W
  rcases hbasis W hW h1W with ⟨U, hUW, hCU⟩
  exact ⟨U, hUW, hmono hCU⟩

end HasOpenNormalBasisInClass

/-- Open normal subgroups whose quotient lies in the chosen class `C`.

This packages the relevant family as an actual type so later inverse-limit and basis constructions
can quantify over it directly. -/
abbrev OpenNormalSubgroupInClass (C : FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] :=
  {U : OpenNormalSubgroup G // C (G ⧸ (U : Subgroup G))}

namespace OpenNormalSubgroupInClass

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Repackage an open normal subgroup together with a proof that its quotient lies in `C`. -/
def ofOpenNormal (U : OpenNormalSubgroup G) (hU : C (G ⧸ (U : Subgroup G))) :
    OpenNormalSubgroupInClass C G :=
  ⟨U, hU⟩

/-- The defining quotient-membership proof carried by an open-normal-in-class subgroup. -/
theorem quotient_mem (U : OpenNormalSubgroupInClass C G) :
    C (G ⧸ (U.1 : Subgroup G)) :=
  U.2

/-- Move an open-normal-in-class subgroup along an inclusion of finite-group classes. -/
def of_mono {D : FiniteGroupClass.{u}}
    (hmono : ∀ {Q : Type u} [Group Q], C Q → D Q)
    (U : OpenNormalSubgroupInClass C G) :
    OpenNormalSubgroupInClass D G :=
  ⟨U.1, hmono U.2⟩

/-- The top subgroup belongs to any finite-group class containing trivial quotients. -/
def top [FiniteGroupClass.ContainsTrivialQuotients C] :
    OpenNormalSubgroupInClass C G :=
  ⟨⊤, by
    have hsub : Subsingleton (G ⧸ (⊤ : Subgroup G)) := by
      constructor
      intro x y
      rcases QuotientGroup.mk'_surjective (⊤ : Subgroup G) x with ⟨a, rfl⟩
      rcases QuotientGroup.mk'_surjective (⊤ : Subgroup G) y with ⟨b, rfl⟩
      exact QuotientGroup.eq.2 (by simp only [Subgroup.mem_top])
    exact FiniteGroupClass.ContainsTrivialQuotients.of_subsingleton hsub⟩

/-- There is an open-normal-in-class subgroup whenever the class contains trivial quotients. -/
theorem nonempty_of_containsTrivialQuotients [FiniteGroupClass.ContainsTrivialQuotients C] :
    Nonempty (OpenNormalSubgroupInClass C G) :=
  ⟨top (C := C) (G := G)⟩

/-- Every open normal quotient of a compact group lies in the all-finite class. -/
def of_allFinite [ContinuousMul G] [CompactSpace G] (U : OpenNormalSubgroup G) :
    OpenNormalSubgroupInClass FiniteGroupClass.allFinite G :=
  ⟨U, openNormalSubgroup_finiteQuotient (G := G) U⟩

/-- Pull back an open-normal-in-class subgroup along a continuous homomorphism, when the class is
hereditary. -/
noncomputable def comap {H : Type u} [Group H] [TopologicalSpace H]
    (hHer : FiniteGroupClass.Hereditary C) (f : G →ₜ* H)
    (U : OpenNormalSubgroupInClass C H) : OpenNormalSubgroupInClass C G :=
  let N : OpenNormalSubgroup G :=
    OpenNormalSubgroup.comap f.toMonoidHom f.continuous_toFun U.1
  ⟨N, by
    let qmap : G ⧸ (N : Subgroup G) →* H ⧸ (U.1 : Subgroup H) :=
      QuotientGroup.map (N := (N : Subgroup G)) (M := (U.1 : Subgroup H))
        f.toMonoidHom (by
          intro x hx
          exact hx)
    have hqmap_inj : Function.Injective qmap := by
      rw [← MonoidHom.ker_eq_bot_iff qmap]
      ext z
      constructor
      · intro hz
        rcases QuotientGroup.mk'_surjective (N : Subgroup G) z with ⟨x, rfl⟩
        have hxU : f x ∈ (U.1 : Subgroup H) := by
          apply (QuotientGroup.eq_one_iff (N := (U.1 : Subgroup H)) (f x)).1
          simpa [qmap, MonoidHom.mem_ker] using hz
        exact (QuotientGroup.eq_one_iff (N := (N : Subgroup G)) x).2 hxU
      · intro hz
        subst z
        simp only [one_mem]
    exact hHer.of_injective U.2 qmap hqmap_inj⟩

/-- Push forward an open-normal-in-class subgroup along an open surjective continuous
homomorphism, with the target quotient membership supplied explicitly.  This is the lightweight
bridge; stronger automatic versions can be derived from class closure hypotheses as needed. -/
def mapOpenNormal {H : Type u} [Group H] [TopologicalSpace H]
    (f : G →ₜ* H) (hfopen : IsOpenMap f) (hfsurj : Function.Surjective f)
    (U : OpenNormalSubgroupInClass C G)
    (hC : C (H ⧸ ((OpenNormalSubgroup.map f hfopen hfsurj U.1 : OpenNormalSubgroup H) :
      Subgroup H))) :
    OpenNormalSubgroupInClass C H :=
  ⟨OpenNormalSubgroup.map f hfopen hfsurj U.1, hC⟩

/-- Push forward an in-class open normal subgroup along an open surjective continuous
homomorphism.  Formation closure supplies the target quotient membership. -/
def mapOpenNormal_of_formation {H : Type u} [Group H] [TopologicalSpace H]
    (hForm : FiniteGroupClass.Formation C)
    (f : G →ₜ* H) (hfopen : IsOpenMap f) (hfsurj : Function.Surjective f)
    (U : OpenNormalSubgroupInClass C G) :
    OpenNormalSubgroupInClass C H :=
  mapOpenNormal (C := C) (G := G) f hfopen hfsurj U (by
    let M : OpenNormalSubgroup H := OpenNormalSubgroup.map f hfopen hfsurj U.1
    let qmap : G ⧸ (U.1 : Subgroup G) →* H ⧸ (M : Subgroup H) :=
      QuotientGroup.map (N := (U.1 : Subgroup G)) (M := (M : Subgroup H))
        f.toMonoidHom (by
          intro x hx
          exact ⟨x, hx, rfl⟩)
    have hqmap_surj : Function.Surjective qmap :=
      QuotientGroup.map_surjective_of_surjective
        (N := (U.1 : Subgroup G)) (M : Subgroup H) f.toMonoidHom (by
          intro y
          rcases QuotientGroup.mk'_surjective (M : Subgroup H) y with ⟨h, rfl⟩
          rcases hfsurj h with ⟨g, rfl⟩
          exact ⟨g, rfl⟩) (by
          intro x hx
          exact ⟨x, hx, rfl⟩)
    have hquot :
        C ((G ⧸ (U.1 : Subgroup G)) ⧸ qmap.ker) :=
      hForm.quotientClosed qmap.ker U.2
    let e :
        (G ⧸ (U.1 : Subgroup G)) ⧸ qmap.ker ≃*
          H ⧸ (M : Subgroup H) :=
      QuotientGroup.quotientKerEquivOfSurjective qmap hqmap_surj
    exact hForm.isomClosed ⟨e⟩ hquot)

/-- Finite intersections stay in class for a formation. -/
def inf (hForm : FiniteGroupClass.Formation C)
    (U V : OpenNormalSubgroupInClass C G) : OpenNormalSubgroupInClass C G :=
  ⟨U.1 ⊓ V.1,
    FiniteGroupClass.Formation.quotient_inf_mem
      (C := C) (G := G) hForm U.1 V.1 U.2 V.2⟩

/-- The quotient projection attached to an open-normal-in-class subgroup. -/
def quotientProj (U : OpenNormalSubgroupInClass C G) :
    G →ₜ* G ⧸ (U.1 : Subgroup G) :=
  OpenNormalSubgroup.quotientProj U.1

/-- The quotient projection evaluates to the quotient class of the element. -/
@[simp]
theorem quotientProj_apply (U : OpenNormalSubgroupInClass C G) (x : G) :
    quotientProj (C := C) U x = QuotientGroup.mk' (U.1 : Subgroup G) x :=
  rfl

/-- The quotient projection attached to an open-normal-in-class subgroup is surjective. -/
@[simp]
theorem quotientProj_surjective (U : OpenNormalSubgroupInClass C G) :
    Function.Surjective (quotientProj (C := C) U) :=
  OpenNormalSubgroup.quotientProj_surjective U.1

/-- The kernel predicate of the quotient projection is membership in the subgroup. -/
@[simp]
theorem quotientProj_eq_one_iff {U : OpenNormalSubgroupInClass C G} {x : G} :
    quotientProj (C := C) U x = 1 ↔ x ∈ (U.1 : Subgroup G) :=
  OpenNormalSubgroup.quotientProj_eq_one_iff (U := U.1)

/-- Equality in the quotient attached to an open-normal-in-class subgroup. -/
theorem quotientProj_eq_quotientProj_iff {U : OpenNormalSubgroupInClass C G} {x y : G} :
    quotientProj (C := C) U x = quotientProj (C := C) U y ↔
      x / y ∈ (U.1 : Subgroup G) :=
  OpenNormalSubgroup.quotientProj_eq_quotientProj_iff (U := U.1)

/-- Kernel membership for the quotient projection attached to an open-normal-in-class subgroup. -/
@[simp]
theorem mem_ker_quotientProj [ContinuousMul G] {U : OpenNormalSubgroupInClass C G} {x : G} :
    x ∈ OpenNormalSubgroup.ker (quotientProj (C := C) U) ↔
      x ∈ (U.1 : Subgroup G) :=
  OpenNormalSubgroup.mem_ker_quotientProj (U := U.1)

/-- The open-normal kernel of the quotient projection is the original subgroup. -/
@[simp]
theorem ker_quotientProj [ContinuousMul G] (U : OpenNormalSubgroupInClass C G) :
    ((OpenNormalSubgroup.ker (quotientProj (C := C) U) : OpenNormalSubgroup G) :
      Subgroup G) = (U.1 : Subgroup G) :=
  OpenNormalSubgroup.ker_quotientProj U.1

/-- The canonical transition map between quotients attached to nested open normal subgroups in the
class-indexing family. -/
def map {U V : OpenNormalSubgroupInClass C G}
    (hUV : (V.1 : Subgroup G) ≤ (U.1 : Subgroup G)) :
    G ⧸ (V.1 : Subgroup G) →* G ⧸ (U.1 : Subgroup G) :=
  QuotientGroup.map _ _ (MonoidHom.id G) hUV

/-- These transition maps are the natural quotient epimorphisms. -/
theorem map_surjective {U V : OpenNormalSubgroupInClass C G}
    (hUV : (V.1 : Subgroup G) ≤ (U.1 : Subgroup G)) :
    Function.Surjective (map (C := C) (G := G) hUV) := by
  intro x
  rcases QuotientGroup.mk'_surjective (U.1 : Subgroup G) x with ⟨g, rfl⟩
  exact ⟨QuotientGroup.mk' (V.1 : Subgroup G) g, rfl⟩

/-- The identity transition map is the identity monoid homomorphism. -/
theorem map_id (U : OpenNormalSubgroupInClass C G) :
    map (C := C) (G := G) (le_rfl : (U.1 : Subgroup G) ≤ (U.1 : Subgroup G)) = MonoidHom.id _ := by
  simp only [map, QuotientGroup.map_id]

/-- The transition maps compose as expected. -/
theorem map_comp {U V W : OpenNormalSubgroupInClass C G}
    (hUV : (V.1 : Subgroup G) ≤ (U.1 : Subgroup G))
    (hVW : (W.1 : Subgroup G) ≤ (V.1 : Subgroup G)) :
    (map (C := C) (G := G) hUV).comp (map (C := C) (G := G) hVW) =
      map (C := C) (G := G) (hVW.trans hUV) := by
  simpa [map] using QuotientGroup.map_comp_map
    (N := (W.1 : Subgroup G)) (M := (V.1 : Subgroup G)) (O := (U.1 : Subgroup G))
    (f := MonoidHom.id G) (g := MonoidHom.id G) hVW hUV

/-- The continuous transition map between quotients attached to nested open-normal-in-class
subgroups. -/
def transition [ContinuousMul G] {U V : OpenNormalSubgroupInClass C G}
    (hUV : (U.1 : Subgroup G) ≤ (V.1 : Subgroup G)) :
    G ⧸ (U.1 : Subgroup G) →ₜ* G ⧸ (V.1 : Subgroup G) :=
  OpenNormalSubgroup.transition (G := G) (U := U.1) (V := V.1) hUV

/-- Transition maps send quotient classes to the corresponding quotient classes. -/
@[simp]
theorem transition_mk [ContinuousMul G] {U V : OpenNormalSubgroupInClass C G}
    (hUV : (U.1 : Subgroup G) ≤ (V.1 : Subgroup G)) (x : G) :
    transition (C := C) (G := G) hUV (QuotientGroup.mk' (U.1 : Subgroup G) x) =
      QuotientGroup.mk' (V.1 : Subgroup G) x :=
  OpenNormalSubgroup.transition_mk (G := G) (U := U.1) (V := V.1) hUV x

/-- The transition map composed with the smaller quotient projection is the larger quotient
projection. -/
@[simp]
theorem transition_comp_quotientProj [ContinuousMul G] {U V : OpenNormalSubgroupInClass C G}
    (hUV : (U.1 : Subgroup G) ≤ (V.1 : Subgroup G)) :
    (transition (C := C) (G := G) hUV).comp (quotientProj (C := C) U) =
      quotientProj (C := C) V :=
  OpenNormalSubgroup.transition_comp_quotientProj (G := G) (U := U.1) (V := V.1) hUV

/-- Transition maps between quotients by nested open-normal-in-class subgroups are surjective. -/
theorem transition_surjective [ContinuousMul G] {U V : OpenNormalSubgroupInClass C G}
    (hUV : (U.1 : Subgroup G) ≤ (V.1 : Subgroup G)) :
    Function.Surjective (transition (C := C) (G := G) hUV) :=
  OpenNormalSubgroup.transition_surjective (G := G) (U := U.1) (V := V.1) hUV

end OpenNormalSubgroupInClass

section

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The inverse system of quotient groups indexed by open normal subgroups whose quotients lie in
`C`, ordered by reverse inclusion. -/
def openNormalSubgroupInClassSystem (C : FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    InverseSystems.InverseSystem (I := OrderDual (OpenNormalSubgroupInClass C G)) where
  X := fun U => G ⧸ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G)
  topologicalSpace := fun _ => inferInstance
  map := fun {U V} hUV =>
    OpenNormalSubgroupInClass.map (C := C) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV
  continuous_map := by
    intro U V hUV
    letI : DiscreteTopology
        (G ⧸ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G)) :=
      QuotientGroup.discreteTopology
        (openNormalSubgroup_isOpen (G := G) ((OrderDual.ofDual U).1 : OpenNormalSubgroup G))
    exact continuous_of_discreteTopology
  map_id := by
    intro U
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (OpenNormalSubgroupInClass.map_id
          (C := C) (G := G) (U := OrderDual.ofDual U))) x
  map_comp := by
    intro U V W hUV hVW
    funext x
    rcases QuotientGroup.mk'_surjective
        ((((OrderDual.ofDual W).1 : OpenNormalSubgroup G) : Subgroup G)) x with ⟨g, rfl⟩
    rfl

/-- Every coordinate of `openNormalSubgroupInClassSystem` is a quotient group. -/
instance instGroupOpenNormalSubgroupInClassSystemX
    (U : OrderDual (OpenNormalSubgroupInClass C G)) :
    Group ((openNormalSubgroupInClassSystem C G).X U) := by
  dsimp [openNormalSubgroupInClassSystem]
  infer_instance

/-- The canonical quotient homomorphisms from `G` into the inverse system from
`openNormalSubgroupInClassSystem`. -/
def openNormalSubgroupInClassProj
    (U : OrderDual (OpenNormalSubgroupInClass C G)) :
    G →* G ⧸ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G) :=
  QuotientGroup.mk' (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G)

/-- The canonical quotient homomorphisms are compatible with the transition maps. -/
theorem openNormalSubgroupInClassProj_compatible :
    (openNormalSubgroupInClassSystem C G).CompatibleMaps
      (fun U : OrderDual (OpenNormalSubgroupInClass C G) =>
        openNormalSubgroupInClassProj (C := C) (G := G) U) := by
  intro U V hUV
  funext g
  rfl

/-- The quotient system attached to the open normal subgroups in `C` is group-valued. -/
instance instIsGroupSystemOpenNormalSubgroupInClassSystem :
    InverseSystems.IsGroupSystem (openNormalSubgroupInClassSystem C G) where
  map_one := by
    intro i j hij
    change
      OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij 1 = 1
    exact
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij).map_one
  map_mul := by
    intro i j hij x y
    change
      OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij (x * y) =
          OpenNormalSubgroupInClass.map
            (C := C) (G := G)
            (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij x *
          OpenNormalSubgroupInClass.map
            (C := C) (G := G)
            (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij y
    exact
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij).map_mul x y
  map_inv := by
    intro i j hij x
    change
      OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij x⁻¹ =
          (OpenNormalSubgroupInClass.map
            (C := C) (G := G)
            (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij x)⁻¹
    exact
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij).map_inv x

omit [IsTopologicalGroup G] in
/-- Every open-normal-in-class quotient projection is surjective. -/
theorem openNormalSubgroupInClassProj_surjective
    (U : OrderDual (OpenNormalSubgroupInClass C G)) :
    Function.Surjective (openNormalSubgroupInClassProj (C := C) (G := G) U) :=
  QuotientGroup.mk'_surjective _

omit [IsTopologicalGroup G] in
/-- The open-normal-in-class index family is directed under reverse inclusion. -/
theorem directed_openNormalSubgroupInClass
    (hForm : FiniteGroupClass.Formation C) :
    Directed (α := OrderDual (OpenNormalSubgroupInClass C G)) (· ≤ ·) fun U => U := by
  intro U V
  let W : OpenNormalSubgroupInClass C G :=
    ⟨U.1 ⊓ V.1,
      FiniteGroupClass.Formation.quotient_inf_mem
        (C := C) (G := G) hForm U.1 V.1 U.2 V.2⟩
  refine ⟨OrderDual.toDual W, ?_, ?_⟩
  · change ((W.1 : Subgroup G) ≤ (U.1 : Subgroup G))
    exact inf_le_left
  · change ((W.1 : Subgroup G) ≤ (V.1 : Subgroup G))
    exact inf_le_right

end



variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every quotient by an open normal subgroup belongs to the class `C`.

This is stronger than the standard basis formulation unless `C` is quotient-closed. -/
def HasAllOpenNormalQuotientsInClass (C : FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, C (G ⧸ (U : Subgroup G))

/-- Standard pro-`C` group: profinite, with a neighborhood basis of open normal subgroups whose
quotients lie in `C`. -/
structure IsProCGroup (C : FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] : Prop where
  isProfinite : IsProfiniteGroup G
  basis : HasOpenNormalBasisInClass C G

/-- Strict pro-`C` group: profinite, and every open-normal quotient lies in `C`. -/
structure IsStrictProCGroup (C : FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] : Prop where
  isProfinite : IsProfiniteGroup G
  all_open_normal_quotients : HasAllOpenNormalQuotientsInClass C G

namespace IsStrictProCGroup

/-- A strict pro-`C` group is pro-`C` in the standard basis sense. -/
theorem to_isProCGroup (hG : IsStrictProCGroup C G) : IsProCGroup C G := by
  refine ⟨hG.isProfinite, ?_⟩
  intro W hW h1W
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG.isProfinite
  letI : T2Space G := IsProfiniteGroup.t2Space hG.isProfinite
  letI : TotallyDisconnectedSpace G :=
    IsProfiniteGroup.totallyDisconnectedSpace hG.isProfinite
  rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hW h1W with ⟨U, hUW⟩
  exact ⟨U, hUW, hG.all_open_normal_quotients U⟩

end IsStrictProCGroup

namespace IsProCGroup

omit [IsTopologicalGroup G] in
/-- The underlying profinite-group structure of a pro-`C` group. -/
theorem isProfiniteGroup (hG : IsProCGroup C G) : IsProfiniteGroup G :=
  hG.isProfinite

omit [IsTopologicalGroup G] in
/-- The topological group component of a pro-`C` group. -/
theorem isTopologicalGroup (hG : IsProCGroup C G) : IsTopologicalGroup G :=
  hG.isProfiniteGroup.isTopologicalGroup

omit [IsTopologicalGroup G] in
/-- Compactness of a pro-`C` group. -/
theorem compactSpace (hG : IsProCGroup C G) : CompactSpace G :=
  IsProfiniteGroup.compactSpace hG.isProfinite

omit [IsTopologicalGroup G] in
/-- Hausdorffness of a pro-`C` group. -/
theorem t2Space (hG : IsProCGroup C G) : T2Space G :=
  IsProfiniteGroup.t2Space hG.isProfinite

omit [IsTopologicalGroup G] in
/-- The `T1` property of a pro-`C` group. -/
theorem t1Space (hG : IsProCGroup C G) : T1Space G :=
  hG.isProfiniteGroup.t1Space

omit [IsTopologicalGroup G] in
/-- Total disconnectedness of a pro-`C` group. -/
theorem totallyDisconnectedSpace (hG : IsProCGroup C G) : TotallyDisconnectedSpace G :=
  IsProfiniteGroup.totallyDisconnectedSpace hG.isProfinite

omit [IsTopologicalGroup G] in
/-- Enlarge the finite-group class of a pro-`C` group. -/
theorem mono {D : FiniteGroupClass.{u}}
    (hG : IsProCGroup C G)
    (hmono : ∀ {Q : Type u} [Group Q], C Q → D Q) :
    IsProCGroup D G :=
  ⟨hG.isProfiniteGroup, hG.basis.mono hmono⟩

omit [IsTopologicalGroup G] in
/-- In a pro-`C` group, every open neighborhood of `1` contains an open normal subgroup whose
quotient still belongs to `C`. -/
theorem hasOpenNormalBasisInClass (hG : IsProCGroup C G) :
    HasOpenNormalBasisInClass C G :=
  hG.basis

/-- With isomorphism and quotient closure, the basis definition implies the older all-open
normal quotient condition. -/
theorem hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
    (hIso : FiniteGroupClass.IsomClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (hG : IsProCGroup C G) :
    HasAllOpenNormalQuotientsInClass C G := by
  intro U
  rcases hG.basis (((U : Subgroup G) : Set G))
      (openNormalSubgroup_isOpen (G := G) U) U.one_mem' with
    ⟨V, hVU, hCV⟩
  let q : G ⧸ (V : Subgroup G) →ₜ* G ⧸ (U : Subgroup G) :=
    OpenNormalSubgroup.transition (G := G) hVU
  have hqsurj : Function.Surjective q := OpenNormalSubgroup.transition_surjective (G := G) hVU
  have hQuot :
      C ((G ⧸ (V : Subgroup G)) ⧸ q.toMonoidHom.ker) :=
    hQuot (N := q.toMonoidHom.ker) hCV
  exact hIso ⟨QuotientGroup.quotientKerEquivOfSurjective q.toMonoidHom hqsurj⟩ hQuot

/-- In a pro-`C` group over a formation, every open-normal quotient lies in `C`. -/
theorem quotient_mem (hForm : FiniteGroupClass.Formation C)
    (hG : IsProCGroup C G) (U : OpenNormalSubgroup G) :
    C (G ⧸ (U : Subgroup G)) :=
  hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
    hForm.isomClosed hForm.quotientClosed hG U

/-- For formations, the strict and basis definitions agree. -/
theorem isStrictProCGroup_iff_isProCGroup_of_formation
    (hForm : FiniteGroupClass.Formation C) :
    IsStrictProCGroup C G ↔ IsProCGroup C G := by
  constructor
  · exact IsStrictProCGroup.to_isProCGroup
  · intro hG
    exact
      { isProfinite := hG.isProfinite
        all_open_normal_quotients :=
          hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
            hForm.isomClosed hForm.quotientClosed hG }

/-- Any quotient by an open normal subgroup of a pro-`C` group is finite. -/
theorem finite_quotient (hG : IsProCGroup C G) (U : OpenNormalSubgroup G) :
    Finite (G ⧸ (U : Subgroup G)) := by
  letI : CompactSpace G := IsProCGroup.compactSpace hG
  letI : T2Space G := IsProCGroup.t2Space hG
  exact openNormalSubgroup_finiteQuotient (G := G) U

omit [IsTopologicalGroup G] in
/-- In a pro-`C` group, every open neighborhood of `1` contains an indexed open normal subgroup
whose quotient lies in `C`. -/
theorem exists_openNormalSubgroupInClass_sub_open_nhds_of_one (hG : IsProCGroup C G)
    {W : Set G} (hW : IsOpen W) (h1W : (1 : G) ∈ W) :
    ∃ U : OpenNormalSubgroupInClass C G, (((U.1 : Subgroup G) : Set G)) ⊆ W := by
  rcases hG.hasOpenNormalBasisInClass W hW h1W with ⟨U, hUW, hCU⟩
  exact ⟨⟨U, hCU⟩, hUW⟩

section DiscreteCoset

omit [IsTopologicalGroup G] in
/-- A continuous map to a discrete target is locally fixed on a sufficiently small right coset,
with the small subgroup chosen among the open normal pro-`C` quotients. -/
theorem exists_openNormalSubgroupInClass_eq_on_right_coset_of_continuous_discrete
    (hG : IsProCGroup C G)
    {A : Type v} [TopologicalSpace A] [DiscreteTopology A]
    (f : G → A) (hf : Continuous f) (g₀ : G) :
    ∃ U : OpenNormalSubgroupInClass C G,
      ∀ g : G, g * g₀⁻¹ ∈ (U.1 : Subgroup G) → f g = f g₀ := by
  letI : IsTopologicalGroup G := hG.isTopologicalGroup
  let W : Set G := {x | f (x * g₀) = f g₀}
  have hW : IsOpen W := by
    change IsOpen ((fun x : G => f (x * g₀)) ⁻¹' ({f g₀} : Set A))
    exact isOpen_discrete _ |>.preimage (hf.comp (continuous_id.mul continuous_const))
  have h1W : (1 : G) ∈ W := by
    simp only [Set.mem_setOf_eq, one_mul, W]
  rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hW h1W with ⟨U, hUW⟩
  refine ⟨U, ?_⟩
  intro g hg
  have hmem : g * g₀⁻¹ ∈ W := hUW hg
  have hrewrite : (g * g₀⁻¹) * g₀ = g := by
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  simpa [W, hrewrite] using hmem

end DiscreteCoset

omit [IsTopologicalGroup G] in
/-- In a pro-`C` group, the open normal subgroups whose quotients lie in `C` have trivial total
intersection. -/
theorem iInf_openNormalSubgroupInClass_eq_bot (hG : IsProCGroup C G) :
    iInf (fun U : OpenNormalSubgroupInClass C G => (U.1 : Subgroup G)) = (⊥ : Subgroup G) := by
  letI : T2Space G := IsProCGroup.t2Space hG
  apply le_antisymm
  · intro x hx
    change x = 1
    by_contra hxne
    let W : Set G := ({x} : Set G)ᶜ
    have hW : IsOpen W := by
      simp only [isOpen_compl_iff, Set.finite_singleton, Set.Finite.isClosed, W]
    have h1W : (1 : G) ∈ W := by
      have hx1 : (1 : G) ≠ x := by
        intro h1x
        exact hxne h1x.symm
      simpa [W] using hx1
    rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hW h1W with ⟨U, hUW⟩
    have hxall : ∀ U : OpenNormalSubgroupInClass C G, x ∈ (U.1 : Subgroup G) := by
      simpa [Subgroup.mem_iInf] using hx
    have hxU : x ∈ (U.1 : Subgroup G) := hxall U
    have hxW : x ∈ W := hUW hxU
    exact hxW (by simp only [Set.mem_singleton_iff])
  · exact bot_le

omit [IsTopologicalGroup G] in
/-- Set-theoretic form of the trivial-intersection statement. -/
theorem iInter_openNormalSubgroupInClass_eq_singleton (hG : IsProCGroup C G) :
    (⋂ U : OpenNormalSubgroupInClass C G, (((U.1 : Subgroup G) : Set G))) = ({1} : Set G) := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ iInf (fun U : OpenNormalSubgroupInClass C G => (U.1 : Subgroup G)) := by
      simpa [Subgroup.mem_iInf, Set.mem_iInter] using hx
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hG.iInf_openNormalSubgroupInClass_eq_bot] using hx'
    simpa using hxbot
  · rintro rfl
    simp only [OpenSubgroup.coe_toSubgroup, Set.mem_iInter, SetLike.mem_coe, one_mem, implies_true]

omit [IsTopologicalGroup G] in
/-- Explicit family form of the open-normal basis and trivial-intersection package. -/
theorem exists_openNormalBasisInClassFamily (hG : IsProCGroup C G) :
    ∃ ι : Type u, ∃ U : ι → OpenNormalSubgroup G,
      (∀ i, C (G ⧸ (U i : Subgroup G))) ∧
      (∀ W : Set G, IsOpen W → (1 : G) ∈ W →
        ∃ i, (((U i : Subgroup G) : Set G)) ⊆ W) ∧
      iInf (fun i => (U i : Subgroup G)) = (⊥ : Subgroup G) := by
  refine ⟨OpenNormalSubgroupInClass C G, fun i => i.1, ?_, ?_, ?_⟩
  · intro i
    exact i.2
  · intro W hW h1W
    rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hW h1W with ⟨U, hUW⟩
    exact ⟨U, hUW⟩
  · simpa using hG.iInf_openNormalSubgroupInClass_eq_bot

omit [IsTopologicalGroup G] in
/-- Membership in every open-normal-in-class subgroup forces an element to be trivial. -/
theorem eq_one_of_mem_all_openNormalSubgroupInClass (hG : IsProCGroup C G) {x : G}
    (hx : ∀ U : OpenNormalSubgroupInClass C G, x ∈ (U.1 : Subgroup G)) :
    x = 1 := by
  have hx' : x ∈ iInf (fun U : OpenNormalSubgroupInClass C G => (U.1 : Subgroup G)) := by
    simpa [Subgroup.mem_iInf] using hx
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [hG.iInf_openNormalSubgroupInClass_eq_bot] using hx'
  simpa using hxbot

omit [IsTopologicalGroup G] in
/-- If `x ≠ 1`, then some open normal subgroup in the class-family omits `x`. -/
theorem exists_openNormalSubgroupInClass_not_mem (hG : IsProCGroup C G) {x : G} (hx : x ≠ 1) :
    ∃ U : OpenNormalSubgroupInClass C G, x ∉ (U.1 : Subgroup G) := by
  by_contra h
  apply hx
  apply hG.eq_one_of_mem_all_openNormalSubgroupInClass
  intro U
  by_contra hxU
  exact h ⟨U, hxU⟩

omit [IsTopologicalGroup G] in
/-- Two elements of a pro-`C` group are equal once they agree in every quotient by an open normal
subgroup whose quotient lies in `C`. -/
theorem eq_of_forall_openNormalSubgroupInClass_quotient_eq (hG : IsProCGroup C G) {x y : G}
    (hxy : ∀ U : OpenNormalSubgroupInClass C G,
      QuotientGroup.mk' (U.1 : Subgroup G) x = QuotientGroup.mk' (U.1 : Subgroup G) y) :
    x = y := by
  have hxy' : x⁻¹ * y = 1 := by
    apply hG.eq_one_of_mem_all_openNormalSubgroupInClass
    intro U
    exact QuotientGroup.eq.1 (hxy U)
  calc
    x = x * 1 := by simp only [mul_one]
    _ = x * (x⁻¹ * y) := by rw [hxy']
    _ = y := by simp only [mul_inv_cancel_left]

omit [IsTopologicalGroup G] in
/-- Coordinatewise equality in the canonical inverse-system projections already forces equality in
the ambient pro-`C` group. -/
theorem eq_of_forall_openNormalSubgroupInClassProj_eq (hG : IsProCGroup C G) {x y : G}
    (hxy : ∀ U : OrderDual (OpenNormalSubgroupInClass C G),
      openNormalSubgroupInClassProj (C := C) (G := G) U x =
        openNormalSubgroupInClassProj (C := C) (G := G) U y) :
    x = y := by
  apply hG.eq_of_forall_openNormalSubgroupInClass_quotient_eq
  intro U
  simpa [openNormalSubgroupInClassProj] using hxy (OrderDual.toDual U)

/-- A direct constructor for `IsProCGroup` from the stronger open-normal quotient criterion. -/
theorem of_allOpenNormalQuotients (hprof : IsProfiniteGroup G)
    (hquot : HasAllOpenNormalQuotientsInClass C G) :
    IsProCGroup C G :=
  (IsStrictProCGroup.mk hprof hquot).to_isProCGroup

omit [IsTopologicalGroup G] in
/-- In a pro-`C` group there is at least one open normal subgroup with quotient in `C`. -/
theorem openNormalSubgroupInClass_nonempty (hG : IsProCGroup C G) :
    Nonempty (OpenNormalSubgroupInClass C G) := by
  rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one
      (W := Set.univ) isOpen_univ (by simp only [Set.mem_univ]) with ⟨U, _⟩
  exact ⟨U⟩

end IsProCGroup

/-- The chosen Lean definition of a pro-`C` group matches the open-normal basis condition. -/
theorem isProCGroup_iff {C : FiniteGroupClass.{u}}
    {G : Type u} [Group G] [TopologicalSpace G] :
    IsProCGroup C G ↔
      IsProfiniteGroup G ∧ HasOpenNormalBasisInClass C G := by
  constructor
  · intro hG
    exact ⟨hG.isProfinite, hG.basis⟩
  · rintro ⟨hprof, hbasis⟩
    exact ⟨hprof, hbasis⟩

/-- The strict pro-`C` definition matches the all-open-normal-quotient condition. -/
theorem isStrictProCGroup_iff {C : FiniteGroupClass.{u}}
    {G : Type u} [Group G] [TopologicalSpace G] :
    IsStrictProCGroup C G ↔
      IsProfiniteGroup G ∧ HasAllOpenNormalQuotientsInClass C G := by
  constructor
  · intro hG
    exact ⟨hG.isProfinite, hG.all_open_normal_quotients⟩
  · rintro ⟨hprof, hall⟩
    exact ⟨hprof, hall⟩

end

end ProCGroups.ProC
