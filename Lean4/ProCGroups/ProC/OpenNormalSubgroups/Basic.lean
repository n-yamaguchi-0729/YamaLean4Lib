import Mathlib.Topology.Algebra.ContinuousMonoidHom
import ProCGroups.Profinite.OpenSubgroups
import ProCGroups.Topologies.QuotientMaps

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/OpenNormalSubgroups/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open scoped Topology

namespace ProCGroups.ProC

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace OpenNormalSubgroup

/-- Open normal subgroups have a top element. -/
instance instTopOpenNormalSubgroup : Top (OpenNormalSubgroup G) :=
  ⟨{ toOpenSubgroup := ⊤
     isNormal' := by
       change (⊤ : Subgroup G).Normal
       infer_instance }⟩

/-- The kernel of a continuous homomorphism into a discrete group, as an open normal subgroup. -/
def ker {Q : Type v} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →ₜ* Q) : OpenNormalSubgroup G where
  toOpenSubgroup :=
    { toSubgroup := f.toMonoidHom.ker
      isOpen' := by
        change IsOpen (f ⁻¹' ({1} : Set Q))
        exact (isOpen_discrete _).preimage f.continuous_toFun }
  isNormal' := by
    change f.toMonoidHom.ker.Normal
    infer_instance

/-- The underlying subgroup of `OpenNormalSubgroup.ker` is the algebraic kernel. -/
@[simp, norm_cast]
theorem toSubgroup_ker {Q : Type v} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →ₜ* Q) :
    ((ker f : OpenNormalSubgroup G) : Subgroup G) = f.toMonoidHom.ker :=
  rfl

/-- Membership in the open normal kernel is exactly mapping to `1`. -/
@[simp]
theorem mem_ker {Q : Type v} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    {f : G →ₜ* Q} {x : G} :
    x ∈ ker f ↔ f x = 1 := by
  rfl

/-- Push an open normal subgroup forward along an open surjective continuous homomorphism. -/
def map {H : Type v} [Group H] [TopologicalSpace H]
    (f : G →ₜ* H) (hfopen : IsOpenMap f) (hfsurj : Function.Surjective f)
    (U : OpenNormalSubgroup G) : OpenNormalSubgroup H where
  toOpenSubgroup :=
    { toSubgroup := (U : Subgroup G).map f.toMonoidHom
      isOpen' := by
        change IsOpen (f '' ((U : Subgroup G) : Set G))
        exact hfopen _ (openNormalSubgroup_isOpen (G := G) U) }
  isNormal' := by
    change ((U : Subgroup G).map f.toMonoidHom).Normal
    exact Subgroup.Normal.map U.isNormal' f.toMonoidHom hfsurj

/-- The underlying subgroup of the image open normal subgroup is the subgroup image. -/
@[simp, norm_cast]
theorem toSubgroup_map {H : Type v} [Group H] [TopologicalSpace H]
    (f : G →ₜ* H) (hfopen : IsOpenMap f) (hfsurj : Function.Surjective f)
    (U : OpenNormalSubgroup G) :
    ((map f hfopen hfsurj U : OpenNormalSubgroup H) : Subgroup H) =
      (U : Subgroup G).map f.toMonoidHom :=
  rfl

/-- The canonical quotient projection attached to an open normal subgroup. -/
def quotientProj (U : OpenNormalSubgroup G) : G →ₜ* G ⧸ (U : Subgroup G) where
  toMonoidHom := QuotientGroup.mk' (U : Subgroup G)
  continuous_toFun := continuous_quotient_mk'

/-- Quotients by open normal subgroups of compact groups are finite. -/
instance quotientFinite [ContinuousMul G] [CompactSpace G] (U : OpenNormalSubgroup G) :
    Finite (G ⧸ (U : Subgroup G)) :=
  openNormalSubgroup_finiteQuotient (G := G) U

/-- Quotients by open normal subgroups carry the discrete topology. -/
instance quotientDiscrete [ContinuousMul G] (U : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ (U : Subgroup G)) :=
  QuotientGroup.discreteTopology (openNormalSubgroup_isOpen (G := G) U)

theorem quotientProj_toMonoidHom (U : OpenNormalSubgroup G) :
    (quotientProj U).toMonoidHom = QuotientGroup.mk' (U : Subgroup G) :=
  rfl

/-- The quotient projection sends an element to its quotient class. -/
@[simp]
theorem quotientProj_apply (U : OpenNormalSubgroup G) (x : G) :
    quotientProj U x = QuotientGroup.mk' (U : Subgroup G) x :=
  rfl

/-- The quotient projection by an open normal subgroup is surjective. -/
@[simp]
theorem quotientProj_surjective (U : OpenNormalSubgroup G) :
    Function.Surjective (quotientProj U) :=
  QuotientGroup.mk'_surjective (U : Subgroup G)

/-- The quotient projection maps an element to `1` exactly on the subgroup. -/
@[simp]
theorem quotientProj_eq_one_iff {U : OpenNormalSubgroup G} {x : G} :
    quotientProj U x = 1 ↔ x ∈ (U : Subgroup G) := by
  change (QuotientGroup.mk' (U : Subgroup G) x) = 1 ↔ x ∈ (U : Subgroup G)
  exact QuotientGroup.eq_one_iff (N := (U : Subgroup G)) x

/-- Equality under a quotient projection is membership of the quotient difference in the subgroup. -/
theorem quotientProj_eq_quotientProj_iff {U : OpenNormalSubgroup G} {x y : G} :
    quotientProj U x = quotientProj U y ↔ x / y ∈ (U : Subgroup G) := by
  change QuotientGroup.mk' (U : Subgroup G) x = QuotientGroup.mk' (U : Subgroup G) y ↔
    x / y ∈ (U : Subgroup G)
  exact QuotientGroup.eq_iff_div_mem (N := (U : Subgroup G)) (x := x) (y := y)

/-- Kernel membership for the quotient projection is subgroup membership. -/
@[simp]
theorem mem_ker_quotientProj [ContinuousMul G] {U : OpenNormalSubgroup G} {x : G} :
    x ∈ ker (quotientProj U) ↔ x ∈ (U : Subgroup G) := by
  exact quotientProj_eq_one_iff (U := U)

/-- The open normal kernel of the quotient projection is the original subgroup. -/
@[simp]
theorem ker_quotientProj [ContinuousMul G] (U : OpenNormalSubgroup G) :
    ((ker (quotientProj U) : OpenNormalSubgroup G) : Subgroup G) = (U : Subgroup G) := by
  exact QuotientGroup.ker_mk' (U : Subgroup G)

/-- Kernels commute with composition of continuous homomorphisms into discrete groups. -/
@[simp]
theorem ker_comp {H : Type v} [Group H] [TopologicalSpace H]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (g : H →ₜ* Q) (f : G →ₜ* H) :
    ker (g.comp f) =
      OpenNormalSubgroup.comap f.toMonoidHom f.continuous_toFun (ker g) := by
  ext x
  rfl

/-- The comap of a kernel is the kernel of the composite. -/
@[simp]
theorem comap_ker {H : Type v} [Group H] [TopologicalSpace H]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →ₜ* H) (g : H →ₜ* Q) :
    OpenNormalSubgroup.comap f.toMonoidHom f.continuous_toFun (ker g) =
      ker (g.comp f) := by
  simp only [ContinuousMonoidHom.coe_toMonoidHom, ker_comp]

/-- Comapping an open normal subgroup is the kernel of the composite quotient projection. -/
@[simp]
theorem comap_quotientProj {H : Type v} [Group H] [TopologicalSpace H] [ContinuousMul H]
    (f : G →ₜ* H) (U : OpenNormalSubgroup H) :
    OpenNormalSubgroup.comap f.toMonoidHom f.continuous_toFun U =
      ker ((quotientProj U).comp f) := by
  ext x
  exact (quotientProj_eq_one_iff (U := U)).symm

/-- The natural transition map between quotients by open normal subgroups `U ≤ V`. -/
def transition [ContinuousMul G] {U V : OpenNormalSubgroup G}
    (hUV : (U : Subgroup G) ≤ (V : Subgroup G)) :
    G ⧸ (U : Subgroup G) →ₜ* G ⧸ (V : Subgroup G) :=
  QuotientGroup.mapₜ (U : Subgroup G) (V : Subgroup G) (ContinuousMonoidHom.id G) (by
    intro x hx
    exact hUV hx)

/-- Transition maps send quotient classes to quotient classes. -/
@[simp]
theorem transition_mk {U V : OpenNormalSubgroup G}
    [ContinuousMul G]
    (hUV : (U : Subgroup G) ≤ (V : Subgroup G)) (x : G) :
    transition hUV (QuotientGroup.mk' (U : Subgroup G) x) =
      QuotientGroup.mk' (V : Subgroup G) x := by
  rfl

/-- A transition map composed with the smaller quotient projection is the larger quotient
projection. -/
@[simp]
theorem transition_comp_quotientProj {U V : OpenNormalSubgroup G}
    [ContinuousMul G]
    (hUV : (U : Subgroup G) ≤ (V : Subgroup G)) :
    (transition hUV).comp (quotientProj U) = quotientProj V := by
  rfl

/-- Transition maps between quotients by nested open normal subgroups are surjective. -/
theorem transition_surjective {U V : OpenNormalSubgroup G}
    [ContinuousMul G]
    (hUV : (U : Subgroup G) ≤ (V : Subgroup G)) :
    Function.Surjective (transition hUV) := by
  intro y
  rcases QuotientGroup.mk'_surjective (V : Subgroup G) y with ⟨x, rfl⟩
  exact ⟨QuotientGroup.mk' (U : Subgroup G) x, rfl⟩

/-- The kernel of the transition map is the image of the larger subgroup in the smaller
quotient. -/
@[simp]
theorem ker_transition {U V : OpenNormalSubgroup G}
    [ContinuousMul G]
    (hUV : (U : Subgroup G) ≤ (V : Subgroup G)) :
    ((ker (transition hUV) : OpenNormalSubgroup (G ⧸ (U : Subgroup G))) :
        Subgroup (G ⧸ (U : Subgroup G))) =
      (V : Subgroup G).map (QuotientGroup.mk' (U : Subgroup G)) := by
  simpa [transition] using
    (QuotientGroup.ker_map (N := (U : Subgroup G)) (M := (V : Subgroup G))
      (f := MonoidHom.id G) hUV)

/-- The normal core of an open subgroup in a compact topological group, as an open normal
subgroup. -/
def normalCore [ContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    OpenNormalSubgroup G where
  toOpenSubgroup :=
    { toSubgroup := Subgroup.normalCore (U : Subgroup G)
      isOpen' := by
        have hclosed : IsClosed ((U : Subgroup G) : Set G) :=
          openSubgroup_isClosed (G := G) U
        letI : (U : Subgroup G).FiniteIndex := by
          letI : Finite (G ⧸ (U : Subgroup G)) := openSubgroup_finiteQuotient (G := G) U
          exact Subgroup.finiteIndex_of_finite_quotient
        exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
          ((U : Subgroup G).normalCore_isClosed hclosed) }
  isNormal' := by
    change (Subgroup.normalCore (U : Subgroup G)).Normal
    infer_instance

/-- The underlying subgroup of `normalCore` is the algebraic normal core. -/
@[simp, norm_cast]
theorem toSubgroup_normalCore [ContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    ((normalCore U : OpenNormalSubgroup G) : Subgroup G) =
      Subgroup.normalCore (U : Subgroup G) :=
  rfl

/-- The normal core of an open subgroup is contained in that open subgroup. -/
theorem normalCore_le [ContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    (normalCore U : Subgroup G) ≤ (U : Subgroup G) :=
  Subgroup.normalCore_le (U : Subgroup G)

/-- The infimum of a finite family of open normal subgroups. -/
def finsetInf {ι : Type v} (s : Finset ι) (U : ι → OpenNormalSubgroup G) :
    OpenNormalSubgroup G :=
  s.fold (fun A B => A ⊓ B) ⊤ U

end OpenNormalSubgroup

end ProCGroups.ProC
