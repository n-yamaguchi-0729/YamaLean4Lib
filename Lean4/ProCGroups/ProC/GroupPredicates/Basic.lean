import ProCGroups.ProC.GroupPredicate
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import Mathlib.GroupTheory.Commutator.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/GroupPredicates/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C predicate bridge API

The primary concrete predicate is `IsProCGroup C G`, where `C` is a `FiniteGroupClass`.
The local basis predicate `HasExactOpenNormalQuotientBasisInClass C G` is a construction and
recognition tool, connected to `IsProCGroup` by bridge theorems in the open-normal-subgroup
files. `ProCGroupPredicate` and `ProCTheory` are auxiliary packaging layers for theorems that
must range over abstract pro-`C` predicates while still exposing their finite quotient class and
closure hypotheses.
-/

namespace ProCGroups.ProC

universe u v

open InverseSystems

/-- The all-finite pro-`C` predicate is profiniteness. -/
def allFiniteProC : ProCGroupPredicate.{u} where
  holds := fun {G} [_] [_] [_] => IsProfiniteGroup G

/-- The canonical topological pro-`C` predicate attached to a concrete finite-group class `C`.

This declaration is `protected` to keep unqualified resolution stable when several pro-`C`
namespaces are open at once. -/
protected def finiteGroupClassProCPredicate
    (C : FiniteGroupClass.{u}) : ProCGroupPredicate where
  holds := fun {G} [_] [_] [_] =>
    IsProCGroup C G

/-- The concrete finite-class pro-`C` predicate unfolds to `IsProCGroup`. -/
@[simp] theorem finiteGroupClassProCPredicate_holds_iff
    {C : FiniteGroupClass.{u}}
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (ProCGroups.ProC.finiteGroupClassProCPredicate C) (G := G) ↔
      IsProCGroup C G :=
  Iff.rfl

/-- A group satisfying the concrete finite-class pro-`C` predicate is profinite. -/
theorem isProfiniteGroup_of_finiteGroupClassProCPredicate
    (C : FiniteGroupClass.{u})
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : (ProCGroups.ProC.finiteGroupClassProCPredicate C) (G := G)) :
    IsProfiniteGroup G :=
  hG.isProfinite

/-- Concrete class inclusion induces monotonicity of the corresponding `ProC` predicates. -/
theorem finiteGroupClassProCPredicate_mono
    {C C' : FiniteGroupClass.{u}}
    (hmono :
      ∀ {G : Type u} [Group G], C' G → C G)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (ProCGroups.ProC.finiteGroupClassProCPredicate C') (G := G) →
      (ProCGroups.ProC.finiteGroupClassProCPredicate C) (G := G) := by
  intro hG
  exact ⟨hG.isProfinite, hG.basis.mono hmono⟩

/-- A bundled pro-`C` theory: a topological predicate, the finite quotient class that controls it,
and the formation data for that finite class.

This is the preferred package when a theorem needs to move between an abstract pro-`C` predicate
and finite quotient closure hypotheses without carrying several unrelated arguments. -/
structure ProCTheory where
  predicate : ProCGroupPredicate.{u}
  finiteQuotientClass : FiniteGroupClass.{u}
  formation : FiniteGroupClass.Formation finiteQuotientClass
  predicate_iff_isProCGroup :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      predicate (G := G) ↔ IsProCGroup finiteQuotientClass G

/-- One-directional version of `ProCTheory`, for predicates known to contain the concrete
finite-quotient pro-`C` groups but not known to be equivalent to them. -/
structure ProCTheorySound where
  predicate : ProCGroupPredicate.{u}
  finiteQuotientClass : FiniteGroupClass.{u}
  formation : FiniteGroupClass.Formation finiteQuotientClass
  sound :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      IsProCGroup finiteQuotientClass G → predicate (G := G)

namespace ProCTheory

/-- View a theory as its topological pro-`C` predicate. -/
abbrev holds (T : ProCTheory.{u})
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  T.predicate (G := G)

/-- The concrete pro-`C` group condition controlled by a theory. -/
abbrev IsProCGroup (T : ProCTheory.{u})
    (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ProCGroups.ProC.IsProCGroup T.finiteQuotientClass G

/-- A finite-group formation gives the corresponding concrete pro-`C` theory. -/
def ofFiniteFormation
    (C : FiniteGroupClass.{u}) [hC : FiniteGroupClass.IsFormation C] :
    ProCTheory.{u} where
  predicate := ProCGroups.ProC.finiteGroupClassProCPredicate C
  finiteQuotientClass := C
  formation := hC.formation
  predicate_iff_isProCGroup := by
    intro G _ _ _
    exact Iff.rfl

/-- Build a theory from an abstract predicate once the controlling finite quotient class and
equivalence theorem are explicit. -/
def ofPredicate
    (ProC : ProCGroupPredicate.{u}) (C : FiniteGroupClass.{u})
    (hForm : FiniteGroupClass.Formation C)
    (hiff :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        ProC (G := G) ↔ ProCGroups.ProC.IsProCGroup C G) :
    ProCTheory.{u} where
  predicate := ProC
  finiteQuotientClass := C
  formation := hForm
  predicate_iff_isProCGroup := hiff

/-- Build the one-directional package from an abstract predicate and a soundness theorem. -/
def ofPredicateSound
    (ProC : ProCGroupPredicate.{u}) (C : FiniteGroupClass.{u})
    (hForm : FiniteGroupClass.Formation C)
    (hsound :
      ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
        ProCGroups.ProC.IsProCGroup C G → ProC (G := G)) :
    ProCTheorySound.{u} where
  predicate := ProC
  finiteQuotientClass := C
  formation := hForm
  sound := hsound

/-- A theory predicate is equivalent to the concrete pro-`C` condition for its finite quotient
class. -/
theorem holds_iff_isProCGroup (T : ProCTheory.{u})
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    T.holds (G := G) ↔ T.IsProCGroup G :=
  T.predicate_iff_isProCGroup

/-- The predicate side of a theory implies the concrete pro-`C` condition. -/
theorem isProCGroup_of_holds (T : ProCTheory.{u})
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : T.holds (G := G)) : T.IsProCGroup G :=
  (T.holds_iff_isProCGroup).1 hG

/-- The concrete pro-`C` condition implies the predicate side of a theory. -/
theorem holds_of_isProCGroup (T : ProCTheory.{u})
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : T.IsProCGroup G) : T.holds (G := G) :=
  (T.holds_iff_isProCGroup).2 hG

/-- The finite quotient class packaged by a theory is a formation. -/
def finiteQuotientFormation (T : ProCTheory.{u}) :
    FiniteGroupClass.Formation T.finiteQuotientClass :=
  T.formation

/-- Formation data gives quotient closure for the finite quotient class of a theory. -/
def quotientClosed (T : ProCTheory.{u}) :
    FiniteGroupClass.QuotientClosed T.finiteQuotientClass :=
  T.formation.quotientClosed

/-- Formation data gives isomorphism closure for the finite quotient class of a theory. -/
def isomClosed (T : ProCTheory.{u}) :
    FiniteGroupClass.IsomClosed T.finiteQuotientClass :=
  T.formation.isomClosed

end ProCTheory

namespace ProCGroupPredicate

/-- The discrete finite-quotient class induced by a topological pro-`C` predicate. -/
def finiteQuotientClass (ProC : ProCGroupPredicate.{u}) :
    FiniteGroupClass.{u} where
  pred := fun Q [Group Q] =>
    Finite Q ∧
      letI : TopologicalSpace Q := ⊥
      letI : DiscreteTopology Q := ⟨rfl⟩
      letI : IsTopologicalGroup Q := inferInstance
      ProC (G := Q)
  finite_of_mem := fun hQ => hQ.1

/-- A topological pro-`C` predicate is determined by its finite quotient class. -/
class DeterminedByFiniteQuotients
    (ProC : ProCGroupPredicate.{u}) : Prop where
  holds_of_isProCGroup :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      IsProCGroup ProC.finiteQuotientClass G → ProC (G := G)

/-- Formation data for the finite quotient class attached to a pro-`C` predicate. -/
class HasFiniteQuotientFormation
    (ProC : ProCGroupPredicate.{u}) : Prop where
  formation : FiniteGroupClass.Formation (ProC.finiteQuotientClass)

/-- Melnikov formation data for the finite quotient class attached to a pro-`C` predicate. -/
class HasFiniteQuotientMelnikovFormation
    (ProC : ProCGroupPredicate.{u}) : Prop where
  melnikovFormation : FiniteGroupClass.MelnikovFormation (ProC.finiteQuotientClass)

/-- Full formation data for the finite quotient class attached to a pro-`C` predicate. -/
class HasFiniteQuotientFullFormation
    (ProC : ProCGroupPredicate.{u}) : Prop where
  fullFormation : FiniteGroupClass.FullFormation (ProC.finiteQuotientClass)

/-- Hereditary data for the finite quotient class attached to a pro-`C` predicate. -/
class HasFiniteQuotientHereditary
    (ProC : ProCGroupPredicate.{u}) : Prop where
  hereditary : FiniteGroupClass.Hereditary (ProC.finiteQuotientClass)

/-- Finiteness of the finite quotient class attached to a pro-`C` predicate. -/
class HasFiniteQuotientFinite
    (ProC : ProCGroupPredicate.{u}) : Prop where
  finite : ∀ {Q : Type u} [Group Q], ProC.finiteQuotientClass Q → Finite Q

/-- Extension-closure data for the finite quotient class attached to a pro-`C` predicate. -/
class HasFiniteQuotientExtensionClosed
    (ProC : ProCGroupPredicate.{u}) : Prop where
  extensionClosed : FiniteGroupClass.ExtensionClosed (ProC.finiteQuotientClass)

/-- Permanence data for quotienting a `Source` pro-`C` group by the commutator subgroup of the
kernel of a continuous homomorphism to a `Target` pro-`C` group.

The mixed source/target form is useful for maximal-quotient arguments, where the source is often
known to be pro-`C_e` while the quotient must be pro-`C`. -/
class ClosedUnderCommutatorKernelQuotientsFrom
    (Target Source : ProCGroupPredicate.{u}) : Prop where
  quotient_by_kernel_commutator :
    ∀ {E F : Type u} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
      [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      (φ : E →ₜ* F),
        Source (G := E) → Target (G := F) →
          Target (G := E ⧸ ⁅φ.toMonoidHom.ker, φ.toMonoidHom.ker⁆)

/-- Accessor for commutator-kernel quotient permanence. -/
theorem quotient_by_kernel_commutator
    (Target Source : ProCGroupPredicate.{u})
    [Target.ClosedUnderCommutatorKernelQuotientsFrom Source]
    {E F : Type u} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
    [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    (φ : E →ₜ* F)
    (hE : Source (G := E)) (hF : Target (G := F)) :
    Target (G := E ⧸ ⁅φ.toMonoidHom.ker, φ.toMonoidHom.ker⁆) :=
  ClosedUnderCommutatorKernelQuotientsFrom.quotient_by_kernel_commutator φ hE hF

/-- Accessor for finite quotient formation data. -/
def finiteQuotientFormation
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation] :
    FiniteGroupClass.Formation (ProC.finiteQuotientClass) :=
  ProCGroupPredicate.HasFiniteQuotientFormation.formation

/-- Accessor for finite quotient Melnikov formation data. -/
def finiteQuotientMelnikovFormation
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientMelnikovFormation] :
    FiniteGroupClass.MelnikovFormation (ProC.finiteQuotientClass) :=
  ProCGroupPredicate.HasFiniteQuotientMelnikovFormation.melnikovFormation

/-- Accessor for finite quotient full formation data. -/
def finiteQuotientFullFormation
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFullFormation] :
    FiniteGroupClass.FullFormation (ProC.finiteQuotientClass) :=
  ProCGroupPredicate.HasFiniteQuotientFullFormation.fullFormation

/-- Accessor for hereditary finite quotient data. -/
def finiteQuotientHereditary
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientHereditary] :
    FiniteGroupClass.Hereditary (ProC.finiteQuotientClass) :=
  ProCGroupPredicate.HasFiniteQuotientHereditary.hereditary

/-- Accessor for finiteness of finite quotient class members. -/
def finiteQuotientFinite
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFinite] :
    ∀ {Q : Type u} [Group Q], ProC.finiteQuotientClass Q → Finite Q :=
  ProCGroupPredicate.HasFiniteQuotientFinite.finite

/-- Accessor for finite quotient extension closure. -/
def finiteQuotientExtensionClosed
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientExtensionClosed] :
    FiniteGroupClass.ExtensionClosed (ProC.finiteQuotientClass) :=
  ProCGroupPredicate.HasFiniteQuotientExtensionClosed.extensionClosed

/-- Formation data supplies isomorphism closure for the induced finite quotient class. -/
def finiteQuotientIsomClosed
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation] :
    FiniteGroupClass.IsomClosed (ProC.finiteQuotientClass) :=
  ProC.finiteQuotientFormation.isomClosed

/-- Formation data supplies quotient closure for the induced finite quotient class. -/
def finiteQuotientQuotientClosed
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation] :
    FiniteGroupClass.QuotientClosed (ProC.finiteQuotientClass) :=
  ProC.finiteQuotientFormation.quotientClosed

/-- Formation data supplies finite-product closure for the induced finite quotient class. -/
def finiteQuotientFiniteProductClosed
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation] :
    FiniteGroupClass.FiniteProductClosed (ProC.finiteQuotientClass) :=
  ProC.finiteQuotientFormation.finiteProductClosed

/-- Formation data supplies the trivial-quotient condition for the induced finite quotient class. -/
def finiteQuotientContainsTrivialQuotients
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation] :
    FiniteGroupClass.ContainsTrivialQuotients (ProC.finiteQuotientClass) :=
  ProC.finiteQuotientFormation.containsTrivialQuotients

/-- Full formation data supplies quotient closure. -/
def finiteQuotientFullQuotientClosed
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFullFormation] :
    FiniteGroupClass.QuotientClosed (ProC.finiteQuotientClass) :=
  (ProC.finiteQuotientFullFormation).quotientClosed

/-- Full formation data supplies isomorphism closure. -/
def finiteQuotientFullIsomClosed
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFullFormation] :
    FiniteGroupClass.IsomClosed (ProC.finiteQuotientClass) :=
  (ProC.finiteQuotientFullFormation).isomClosed

/-- Full formation data supplies finiteness of members. -/
def finiteQuotientFullFinite
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFullFormation] :
    ∀ {Q : Type u} [Group Q], ProC.finiteQuotientClass Q → Finite Q :=
  (ProC.finiteQuotientFullFormation).finiteOnly

/-- Full formation data supplies extension closure. -/
def finiteQuotientFullExtensionClosed
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFullFormation] :
    FiniteGroupClass.ExtensionClosed (ProC.finiteQuotientClass) :=
  (ProC.finiteQuotientFullFormation).extensionClosed

/-- Full formation data supplies hereditary subgroup closure. -/
def finiteQuotientFullHereditary
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFullFormation] :
    FiniteGroupClass.Hereditary (ProC.finiteQuotientClass) :=
  (ProC.finiteQuotientFullFormation).hereditary

/-- Full formation data supplies ordinary subgroup closure. -/
theorem finiteQuotientFullSubgroupClosed
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFullFormation] :
    FiniteGroupClass.SubgroupClosed (ProC.finiteQuotientClass) :=
  (ProC.finiteQuotientFullFormation).subgroupClosed

/-- A Melnikov formation supplies the underlying formation structure. -/
@[instance 100]
def hasFiniteQuotientFormation_of_melnikovFormation
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientMelnikovFormation] :
    ProC.HasFiniteQuotientFormation where
  formation := ProC.finiteQuotientMelnikovFormation.formation

/-- Formation data supplies the trivial-quotient instance for the induced finite quotient class. -/
@[instance 100]
def finiteQuotientClass_containsTrivialQuotients_of_formation
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFormation] :
    FiniteGroupClass.ContainsTrivialQuotients ProC.finiteQuotientClass :=
  ProC.finiteQuotientFormation.containsTrivialQuotients

/-- A Melnikov formation supplies finiteness of members of the induced finite quotient class. -/
@[instance 100]
def hasFiniteQuotientFinite_of_melnikovFormation
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientMelnikovFormation] :
    ProC.HasFiniteQuotientFinite where
  finite := (ProC.finiteQuotientMelnikovFormation).finiteOnly

/-- A Melnikov formation supplies extension-closure of the induced finite quotient class. -/
@[instance 100]
def hasFiniteQuotientExtensionClosed_of_melnikovFormation
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientMelnikovFormation] :
    ProC.HasFiniteQuotientExtensionClosed where
  extensionClosed := (ProC.finiteQuotientMelnikovFormation).extensionClosed

/-- A full formation supplies the underlying Melnikov formation. -/
@[instance 100]
def hasFiniteQuotientMelnikovFormation_of_fullFormation
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFullFormation] :
    ProC.HasFiniteQuotientMelnikovFormation where
  melnikovFormation := ProC.finiteQuotientFullFormation.melnikovFormation

/-- A full formation supplies hereditary closure of the induced finite quotient class. -/
@[instance 100]
def hasFiniteQuotientHereditary_of_fullFormation
    (ProC : ProCGroupPredicate.{u}) [ProC.HasFiniteQuotientFullFormation] :
    ProC.HasFiniteQuotientHereditary where
  hereditary := (ProC.finiteQuotientFullFormation).hereditary

end ProCGroupPredicate

namespace HasOpenNormalBasisInClass

/-- Transport a `C`-quotient open-normal basis across a continuous multiplicative equivalence. -/
theorem of_mulEquiv
    {C : FiniteGroupClass.{u}} (hiso : FiniteGroupClass.IsomClosed C)
    {G K : Type u}
    [Group G] [TopologicalSpace G]
    [Group K] [TopologicalSpace K]
    (e : G ≃* K) (hcont : Continuous e) (hcontinuous_symm : Continuous e.symm)
    (hbasis : HasOpenNormalBasisInClass C K) :
    HasOpenNormalBasisInClass C G := by
  intro W hW h1W
  let V : Set K := e.symm ⁻¹' W
  have hV : IsOpen V := hW.preimage hcontinuous_symm
  have h1V : (1 : K) ∈ V := by
    simpa [V] using h1W
  rcases hbasis V hV h1V with ⟨U, hUV, hCU⟩
  let Ucomap : OpenNormalSubgroup G :=
    OpenNormalSubgroup.comap (e : G →* K) hcont U
  refine ⟨Ucomap, ?_, ?_⟩
  · intro g hg
    have heg : e g ∈ ((U : OpenNormalSubgroup K) : Subgroup K) :=
      (OpenNormalSubgroup.mem_comap
        (f := (e : G →* K)) (hf := hcont) (U := U)).1 hg
    have hVmem : e g ∈ V := hUV heg
    simpa [V] using hVmem
  · have hmap :
        ((Ucomap : OpenNormalSubgroup G) : Subgroup G).map (e : G →* K) =
          ((U : OpenNormalSubgroup K) : Subgroup K) := by
      ext k
      constructor
      · rintro ⟨g, hg, rfl⟩
        exact
          (OpenNormalSubgroup.mem_comap
            (f := (e : G →* K)) (hf := hcont) (U := U)).1 hg
      · intro hk
        refine ⟨e.symm k, ?_, by simp only [MonoidHom.coe_coe, MulEquiv.apply_symm_apply]⟩
        exact
          (OpenNormalSubgroup.mem_comap
            (f := (e : G →* K)) (hf := hcont) (U := U)).2
            (by simpa using hk)
    exact hiso ⟨(QuotientGroup.congr
      (Ucomap : Subgroup G) (U : Subgroup K) e hmap).symm⟩ hCU

end HasOpenNormalBasisInClass

/-- In a profinite group, an element lying in every open normal subgroup is trivial. -/
theorem profiniteGroup_eq_one_of_mem_all_openNormalSubgroups
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : IsProfiniteGroup G) {x : G}
    (hx : ∀ U : OpenNormalSubgroup G, x ∈ (U : Subgroup G)) :
    x = 1 := by
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
  letI : T2Space G := IsProfiniteGroup.t2Space hG
  letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
  by_contra hxne
  let W : Set G := ({x} : Set G)ᶜ
  have hW : IsOpen W := by
    simp only [isOpen_compl_iff, Set.finite_singleton, Set.Finite.isClosed, W]
  have h1W : (1 : G) ∈ W := by
    have hx1 : (1 : G) ≠ x := by
      intro h1x
      exact hxne h1x.symm
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hx1, not_false_eq_true, W]
  rcases ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (G := G) hW h1W with
    ⟨U, hUW⟩
  have hxW : x ∈ W := hUW (hx U)
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false, W] at hxW

/-- Typeclass form of belonging to an ambient topological pro-`C` predicate. -/
class ProCGroup (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop where
  isProC : ProC (G := G)
  isProCGroup : IsProCGroup ProC.finiteQuotientClass G

namespace ProCGroup

/-- A pro-`C` group is profinite. -/
theorem profiniteGroup (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] :
    IsProfiniteGroup G :=
  hG.isProCGroup.1

/-- A pro-`C` group is a topological group. -/
theorem isTopologicalGroup (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] :
    IsTopologicalGroup G :=
  hG.isProCGroup.isTopologicalGroup

/-- A pro-`C` group is compact. -/
theorem compactSpace (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] :
    CompactSpace G :=
  hG.isProCGroup.compactSpace

/-- A pro-`C` group is Hausdorff. -/
theorem t2Space (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] :
    T2Space G :=
  hG.isProCGroup.t2Space

/-- A pro-`C` group is `T1`. -/
theorem t1Space (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] :
    T1Space G := by
  letI : T2Space G := ProCGroup.t2Space ProC G
  infer_instance

/-- A pro-`C` group is totally disconnected. -/
theorem totallyDisconnectedSpace (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] :
    TotallyDisconnectedSpace G :=
  hG.isProCGroup.totallyDisconnectedSpace

/-- Open normal quotients of a pro-`C` group are finite. -/
theorem finite_quotient (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] (U : OpenNormalSubgroup G) :
    Finite (G ⧸ (U : Subgroup G)) :=
  hG.isProCGroup.finite_quotient U

/-- Open normal quotients of a pro-`C` group lie in the induced finite quotient class. -/
theorem quotient_mem (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] [ProC.HasFiniteQuotientFormation] (U : OpenNormalSubgroup G) :
    ProC.finiteQuotientClass (G ⧸ (U : Subgroup G)) :=
  hG.isProCGroup.quotient_mem ProC.finiteQuotientFormation U

/-- A pro-`C` group has an open-normal basis whose quotients lie in the induced finite quotient
class. -/
theorem hasOpenNormalBasisInClass (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] :
    HasOpenNormalBasisInClass ProC.finiteQuotientClass G :=
  hG.isProCGroup.hasOpenNormalBasisInClass

/-- Every neighborhood of `1` in a pro-`C` group contains an open normal subgroup whose quotient lies
in the induced finite quotient class. -/
theorem exists_openNormalSubgroupInClass_sub_open_nhds_of_one
    (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G]
    {W : Set G} (hW : IsOpen W) (h1W : (1 : G) ∈ W) :
    ∃ U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G,
      (((U.1 : Subgroup G) : Set G)) ⊆ W :=
  hG.isProCGroup.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hW h1W

/-- The open-normal-in-class family of a pro-`C` group is nonempty. -/
theorem openNormalSubgroupInClass_nonempty (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] :
    Nonempty (OpenNormalSubgroupInClass ProC.finiteQuotientClass G) :=
  hG.isProCGroup.openNormalSubgroupInClass_nonempty

/-- The open-normal-in-class subgroups of a pro-`C` group have trivial infimum. -/
theorem iInf_openNormalSubgroupInClass_eq_bot (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] :
    iInf (fun U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G =>
      (U.1 : Subgroup G)) = (⊥ : Subgroup G) :=
  hG.isProCGroup.iInf_openNormalSubgroupInClass_eq_bot

/-- The open-normal-in-class subgroups of a pro-`C` group have singleton intersection. -/
theorem iInter_openNormalSubgroupInClass_eq_singleton (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] :
    (⋂ U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G,
      (((U.1 : Subgroup G) : Set G))) = ({1} : Set G) :=
  hG.isProCGroup.iInter_openNormalSubgroupInClass_eq_singleton

/-- Membership in every open-normal-in-class subgroup of a pro-`C` group forces an element to be
trivial. -/
theorem eq_one_of_mem_all_openNormalSubgroupInClass (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] {x : G}
    (hx : ∀ U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G,
      x ∈ (U.1 : Subgroup G)) :
    x = 1 :=
  hG.isProCGroup.eq_one_of_mem_all_openNormalSubgroupInClass hx

/-- A nontrivial element of a pro-`C` group is omitted by some open-normal-in-class subgroup. -/
theorem exists_openNormalSubgroupInClass_not_mem (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] {x : G} (hx : x ≠ 1) :
    ∃ U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G,
      x ∉ (U.1 : Subgroup G) :=
  hG.isProCGroup.exists_openNormalSubgroupInClass_not_mem hx

/-- Two elements of a pro-`C` group are equal when they agree in every open-normal-in-class
quotient. -/
theorem eq_of_forall_openNormalSubgroupInClass_quotient_eq
    (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] {x y : G}
    (hxy : ∀ U : OpenNormalSubgroupInClass ProC.finiteQuotientClass G,
      QuotientGroup.mk' (U.1 : Subgroup G) x = QuotientGroup.mk' (U.1 : Subgroup G) y) :
    x = y :=
  hG.isProCGroup.eq_of_forall_openNormalSubgroupInClass_quotient_eq hxy

/-- Coordinatewise equality in the canonical open-normal-in-class quotient system forces equality in
the ambient pro-`C` group. -/
theorem eq_of_forall_openNormalSubgroupInClassProj_eq
    (ProC : ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G] {x y : G}
    (hxy : ∀ U : OrderDual (OpenNormalSubgroupInClass ProC.finiteQuotientClass G),
      openNormalSubgroupInClassProj (C := ProC.finiteQuotientClass) (G := G) U x =
        openNormalSubgroupInClassProj (C := ProC.finiteQuotientClass) (G := G) U y) :
    x = y :=
  hG.isProCGroup.eq_of_forall_openNormalSubgroupInClassProj_eq hxy

/-- Build the public `ProCGroup` class from the concrete quotient condition. -/
theorem of_isProCGroup
    (ProC : ProCGroupPredicate.{u}) [ProC.DeterminedByFiniteQuotients]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : IsProCGroup ProC.finiteQuotientClass G) :
    ProCGroup ProC G where
  isProC :=
    ProCGroupPredicate.DeterminedByFiniteQuotients.holds_of_isProCGroup hG
  isProCGroup := hG

/-- Enlarge the finite quotient class of a bundled pro-`C` group. -/
theorem of_finiteQuotientClass_mono
    {ProC ProD : ProCGroupPredicate.{u}} [ProD.DeterminedByFiniteQuotients]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [hG : ProCGroup ProC G]
    (hmono :
      ∀ {Q : Type u} [Group Q],
        ProC.finiteQuotientClass Q → ProD.finiteQuotientClass Q) :
    ProCGroup ProD G :=
  ProCGroup.of_isProCGroup ProD G (hG.isProCGroup.mono hmono)

end ProCGroup

/-- A finite discrete group lies in the finite quotient class induced by `allFiniteProC`. -/
theorem allFiniteProC_finiteQuotientClass_of_finite
    {Q : Type u} [Group Q] [Finite Q] :
    allFiniteProC.finiteQuotientClass Q := by
  refine ⟨inferInstance, ?_⟩
  letI : TopologicalSpace Q := ⊥
  letI : DiscreteTopology Q := ⟨rfl⟩
  letI : IsTopologicalGroup Q := inferInstance
  change IsProfiniteGroup Q
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The finite quotient class induced by `allFiniteProC` is exactly the all-finite class. -/
theorem allFiniteProC_finiteQuotientClass_iff_finite
    {Q : Type u} [Group Q] :
    allFiniteProC.finiteQuotientClass Q ↔ Finite Q := by
  constructor
  · intro hQ
    exact hQ.1
  · intro hQ
    letI : Finite Q := hQ
    exact allFiniteProC_finiteQuotientClass_of_finite (Q := Q)

/-- The all-finite pro-`C` predicate has a full finite quotient formation. -/
instance allFiniteProC_hasFiniteQuotientFullFormation :
    ProCGroupPredicate.HasFiniteQuotientFullFormation allFiniteProC where
  fullFormation :=
    { melnikovFormation :=
        { formation :=
            { quotientClosed := by
                intro G _ N _ hG
                exact allFiniteProC_finiteQuotientClass_iff_finite.2
                  (FiniteGroupClass.allFinite_quotientClosed N
                    (allFiniteProC_finiteQuotientClass_iff_finite.1 hG))
              finiteSubdirectProductClosed := by
                intro ι _ G _ H _ f hf _hsurj hH
                exact allFiniteProC_finiteQuotientClass_iff_finite.2
                  (FiniteGroupClass.allFinite_finiteSubdirectProductClosed f hf _hsurj
                    (fun i => allFiniteProC_finiteQuotientClass_iff_finite.1 (hH i))) }
          normalSubgroupClosed := by
            intro Q _ N _ hQ
            exact allFiniteProC_finiteQuotientClass_iff_finite.2
              (FiniteGroupClass.allFinite_normalSubgroupClosed N
                (allFiniteProC_finiteQuotientClass_iff_finite.1 hQ))
          extensionClosed := by
            intro E _ N _ hN hQ
            exact allFiniteProC_finiteQuotientClass_iff_finite.2
              (FiniteGroupClass.allFinite_extensionClosed N
                (allFiniteProC_finiteQuotientClass_iff_finite.1 hN)
                (allFiniteProC_finiteQuotientClass_iff_finite.1 hQ)) }
      subgroupClosed := by
        intro G _ H hG
        exact allFiniteProC_finiteQuotientClass_iff_finite.2
          (FiniteGroupClass.allFinite_subgroupClosed H
            (allFiniteProC_finiteQuotientClass_iff_finite.1 hG)) }

/-- The all-finite pro-`C` predicate is determined by finite quotients. -/
instance allFiniteProC_determinedByFiniteQuotients :
    ProCGroupPredicate.DeterminedByFiniteQuotients allFiniteProC where
  holds_of_isProCGroup hG := hG.isProfinite

/-- A profinite group is pro-`C` for the all-finite predicate in the concrete quotient sense. -/
theorem allFiniteProC_isProCGroup_of_profinite
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : IsProfiniteGroup G) :
    IsProCGroup allFiniteProC.finiteQuotientClass G := by
  refine ⟨hG, ?_⟩
  intro W hW h1W
  letI : CompactSpace G := IsProfiniteGroup.compactSpace hG
  letI : T2Space G := IsProfiniteGroup.t2Space hG
  letI : TotallyDisconnectedSpace G := IsProfiniteGroup.totallyDisconnectedSpace hG
  rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hW h1W with ⟨U, hUW⟩
  have hfinite : Finite (G ⧸ (U : Subgroup G)) := by
    exact
      Subgroup.quotient_finite_of_isOpen (U : Subgroup G)
        (openNormalSubgroup_isOpen (G := G) U)
  letI : Finite (G ⧸ (U : Subgroup G)) := hfinite
  exact ⟨U, hUW, allFiniteProC_finiteQuotientClass_of_finite (Q := G ⧸ (U : Subgroup G))⟩

/-- A profinite group is a bundled pro-`C` group for the all-finite predicate. -/
theorem allFiniteProCGroup_of_profinite
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : IsProfiniteGroup G) :
    ProCGroup allFiniteProC G :=
  ProCGroup.of_isProCGroup allFiniteProC G (allFiniteProC_isProCGroup_of_profinite hG)

end ProCGroups.ProC
