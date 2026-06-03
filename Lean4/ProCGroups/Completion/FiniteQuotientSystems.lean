import ProCGroups.Completion.FiniteQuotientLifts

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Completion/FiniteQuotientSystems.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C completion and finite quotient systems

Organizes finite quotient systems, completion maps, finite-target factorization, and the universal property of pro-C completion.
-/

namespace ProCGroups.Completion

universe u

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable {G : Type u} [Group G]

/-- Normal subgroups whose corresponding quotient belongs to the chosen class `C`. -/
structure NormalSubgroupInClass (C : ProCGroups.FiniteGroupClass.{u}) (G : Type u) [Group G] where
  toSubgroup : Subgroup G
  normal' : toSubgroup.Normal
  quotient_mem' : C (G ⧸ toSubgroup)

namespace NormalSubgroupInClass

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable {G : Type u} [Group G]

/-- Coerce a finite-quotient index to its underlying normal subgroup. -/
instance instCoeOutNormalSubgroupInClass : CoeOut (NormalSubgroupInClass C G) (Subgroup G) where
  coe N := N.toSubgroup

/-- The subgroup underlying a finite-quotient index is normal. -/
instance instNormalCoeNormalSubgroupInClass (N : NormalSubgroupInClass C G) :
    (N : Subgroup G).Normal :=
  N.normal'

/-- Order finite-quotient indices by reverse inclusion of their subgroups. -/
instance instLENormalSubgroupInClass : LE (NormalSubgroupInClass C G) where
  le N M := (M : Subgroup G) ≤ (N : Subgroup G)

/-- Finite-quotient indices form a preorder under reverse inclusion. -/
instance instPreorderNormalSubgroupInClass : Preorder (NormalSubgroupInClass C G) where
  le := fun N M => (M : Subgroup G) ≤ (N : Subgroup G)
  le_refl N := show (N : Subgroup G) ≤ (N : Subgroup G) from le_rfl
  le_trans N M K hNM hMK := show (K : Subgroup G) ≤ (N : Subgroup G) from hMK.trans hNM

/-- The quotient attached to a normal subgroup in the finite-quotient index family lies in `C`. -/
theorem quotient_mem (N : NormalSubgroupInClass C G) :
    C (G ⧸ (N : Subgroup G)) :=
  N.quotient_mem'

/-- The canonical transition map between two quotients in the finite-quotient system. -/
def map {N M : NormalSubgroupInClass C G}
    (hNM : (M : Subgroup G) ≤ (N : Subgroup G)) :
    G ⧸ (M : Subgroup G) →* G ⧸ (N : Subgroup G) :=
  QuotientGroup.map _ _ (MonoidHom.id G) hNM

/-- These transition maps are the natural quotient epimorphisms. -/
theorem map_surjective {N M : NormalSubgroupInClass C G}
    (hNM : (M : Subgroup G) ≤ (N : Subgroup G)) :
    Function.Surjective (map (C := C) (G := G) hNM) := by
  intro x
  rcases QuotientGroup.mk'_surjective (N : Subgroup G) x with ⟨g, rfl⟩
  exact ⟨QuotientGroup.mk' (M : Subgroup G) g, rfl⟩

/-- The transition map attached to a normal subgroup in class is the identity at the same level. -/
theorem map_id (N : NormalSubgroupInClass C G) :
    map (C := C) (G := G)
      (le_rfl : (N : Subgroup G) ≤ (N : Subgroup G)) = MonoidHom.id _ := by
  simp only [map, QuotientGroup.map_id]

/-- Transition maps between normal-subgroup-in-class quotients compose along inclusions. -/
theorem map_comp {N M K : NormalSubgroupInClass C G}
    (hNM : (M : Subgroup G) ≤ (N : Subgroup G))
    (hMK : (K : Subgroup G) ≤ (M : Subgroup G)) :
    (map (C := C) (G := G) hNM).comp (map (C := C) (G := G) hMK) =
      map (C := C) (G := G) (hMK.trans hNM) := by
  simpa [map] using QuotientGroup.map_comp_map
    (N := (K : Subgroup G)) (M := (M : Subgroup G)) (O := (N : Subgroup G))
    (f := MonoidHom.id G) (g := MonoidHom.id G) hMK hNM

end NormalSubgroupInClass

/-- The inverse system of quotients `G/N`, indexed by reverse inclusion.

The coordinates carry the discrete topology, matching the finite-quotient setting. -/
def normalSubgroupInClassSystem (C : ProCGroups.FiniteGroupClass.{u}) (G : Type u) [Group G] :
    ProCGroups.InverseSystems.InverseSystem (I := NormalSubgroupInClass C G) where
  X := fun N => G ⧸ (N : Subgroup G)
  topologicalSpace := fun _ => ⊥
  map := fun {N M} hNM =>
    NormalSubgroupInClass.map (C := C) (G := G) (N := N) (M := M)
      (show (M : Subgroup G) ≤ (N : Subgroup G) from hNM)
  continuous_map := by
    intro N M hNM
    letI : TopologicalSpace (G ⧸ (M : Subgroup G)) := ⊥
    letI : TopologicalSpace (G ⧸ (N : Subgroup G)) := ⊥
    letI : DiscreteTopology (G ⧸ (M : Subgroup G)) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro N
    ext g
    rcases QuotientGroup.mk'_surjective (N : Subgroup G) g with ⟨x, rfl⟩
    rfl
  map_comp := by
    intro N M K hNM hMK
    ext g
    rcases QuotientGroup.mk'_surjective (K : Subgroup G) g with ⟨x, rfl⟩
    rfl

/-- Every coordinate of `normalSubgroupInClassSystem` is a quotient group. -/
instance instGroupNormalSubgroupInClassSystemX
    (N : NormalSubgroupInClass C G) :
    Group ((normalSubgroupInClassSystem C G).X N) := by
  dsimp [normalSubgroupInClassSystem]
  infer_instance

/-- The quotient system is group-valued. -/
instance instIsGroupSystemNormalSubgroupInClassSystem :
    ProCGroups.InverseSystems.IsGroupSystem (normalSubgroupInClassSystem C G) where
  map_one := by
    intro i j hij
    change
      NormalSubgroupInClass.map
        (C := C) (G := G) (N := i) (M := j)
        (show (j : Subgroup G) ≤ (i : Subgroup G) from hij) 1 = 1
    exact
      (NormalSubgroupInClass.map
        (C := C) (G := G) (N := i) (M := j)
        (show (j : Subgroup G) ≤ (i : Subgroup G) from hij)).map_one
  map_mul := by
    intro i j hij x y
    change
      NormalSubgroupInClass.map
        (C := C) (G := G) (N := i) (M := j)
        (show (j : Subgroup G) ≤ (i : Subgroup G) from hij) (x * y) =
          NormalSubgroupInClass.map
            (C := C) (G := G) (N := i) (M := j)
            (show (j : Subgroup G) ≤ (i : Subgroup G) from hij) x *
          NormalSubgroupInClass.map
            (C := C) (G := G) (N := i) (M := j)
            (show (j : Subgroup G) ≤ (i : Subgroup G) from hij) y
    exact
      (NormalSubgroupInClass.map
        (C := C) (G := G) (N := i) (M := j)
        (show (j : Subgroup G) ≤ (i : Subgroup G) from hij)).map_mul x y
  map_inv := by
    intro i j hij x
    change
      NormalSubgroupInClass.map
        (C := C) (G := G) (N := i) (M := j)
        (show (j : Subgroup G) ≤ (i : Subgroup G) from hij) x⁻¹ =
          (NormalSubgroupInClass.map
            (C := C) (G := G) (N := i) (M := j)
            (show (j : Subgroup G) ≤ (i : Subgroup G) from hij) x)⁻¹
    exact
      (NormalSubgroupInClass.map
        (C := C) (G := G) (N := i) (M := j)
        (show (j : Subgroup G) ≤ (i : Subgroup G) from hij)).map_inv x

/-- Under the formation hypothesis, the finite-quotient indexing family is directed by reverse
inclusion. -/
theorem directed_normalSubgroupInClass (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    Directed (α := NormalSubgroupInClass C G) (· ≤ ·) fun N => N := by
  intro N M
  letI : (N : Subgroup G).Normal := N.normal'
  letI : (M : Subgroup G).Normal := M.normal'
  let K : NormalSubgroupInClass C G :=
    ⟨(N : Subgroup G) ⊓ (M : Subgroup G), inferInstance,
      ProCGroups.FiniteGroupClass.Formation.quotient_inf_mem
        (C := C) (G := G) hForm (N : Subgroup G) (M : Subgroup G)
        N.quotient_mem' M.quotient_mem'⟩
  refine ⟨K, ?_, ?_⟩
  · change ((K : Subgroup G) ≤ (N : Subgroup G))
    exact inf_le_left
  · change ((K : Subgroup G) ≤ (M : Subgroup G))
    exact inf_le_right

/-- The inverse-limit carrier built from the quotients `G/N` with `N ◁ G` and `G/N ∈ C`.

This is the concrete carrier used in the finite-quotient construction, not the public completion
object with its universal property. -/
abbrev ProCCompletionLimitCarrier (C : ProCGroups.FiniteGroupClass.{u}) (G : Type u) [Group G] :=
  (normalSubgroupInClassSystem C G).inverseLimit

/-- A pro-`C` completion object: a target, its completion map, and the universal property. -/
structure ProCCompletion
    (T : ProCGroups.ProC.ProCTheory.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  carrier : Type u
  [group : Group carrier]
  [topology : TopologicalSpace carrier]
  [topologicalGroup : IsTopologicalGroup carrier]
  map : G →ₜ* carrier
  isCompletion : IsProCCompletion T.predicate G carrier map

attribute [instance] ProCCompletion.group ProCCompletion.topology ProCCompletion.topologicalGroup

/-- The canonical abstract homomorphism from `G` to its finite-quotient inverse-limit carrier. -/
noncomputable def proCCompletionLimitCarrierHom
    (C : ProCGroups.FiniteGroupClass.{u}) (G : Type u) [Group G] :
    G →* ProCCompletionLimitCarrier C G where
  toFun g :=
    ⟨fun N => QuotientGroup.mk' (N : Subgroup G) g, by
      intro N M hNM
      rfl⟩
  map_one' := by
    apply (normalSubgroupInClassSystem C G).ext
    intro N
    rfl
  map_mul' := by
    intro x y
    apply (normalSubgroupInClassSystem C G).ext
    intro N
    rfl

/-- The canonical continuous map from a discrete group to its finite-quotient inverse-limit
carrier. -/
noncomputable def proCCompletionLimitCarrierMap
    (C : ProCGroups.FiniteGroupClass.{u}) (G : Type u)
    [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    G →ₜ* ProCCompletionLimitCarrier C G where
  toMonoidHom := proCCompletionLimitCarrierHom C G
  continuous_toFun := continuous_of_discreteTopology

/-- Coordinatewise description of the canonical map to the pro-`C` completion. -/
@[simp] theorem projection_proCCompletionLimitCarrierHom
    (N : NormalSubgroupInClass C G) (g : G) :
    (normalSubgroupInClassSystem C G).projection N (proCCompletionLimitCarrierHom C G g) =
      QuotientGroup.mk' (N : Subgroup G) g :=
  rfl

/-- Coordinatewise description of the canonical continuous map from a discrete group. -/
@[simp] theorem projection_proCCompletionLimitCarrierMap
    [TopologicalSpace G] [DiscreteTopology G]
    (N : NormalSubgroupInClass C G) (g : G) :
    (normalSubgroupInClassSystem C G).projection N (proCCompletionLimitCarrierMap C G g) =
      QuotientGroup.mk' (N : Subgroup G) g :=
  rfl

/-- The finite-quotient inverse-limit carrier is a pro-`C` completion once the required
construction hypotheses are supplied explicitly. -/
theorem proCCompletionLimitCarrier_isCompletion
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    [TopologicalSpace G] [IsTopologicalGroup G] [DiscreteTopology G]
    [IsTopologicalGroup (ProCCompletionLimitCarrier C G)]
    (hCarrier :
      ProCGroups.ProC.IsProCGroup C (ProCCompletionLimitCarrier C G))
    (hdense : DenseRange (proCCompletionLimitCarrierMap C G))
    (hlifts :
      HasUniqueFiniteDiscreteQuotientLifts C (proCCompletionLimitCarrierMap C G)) :
    IsProCCompletion (ProCGroups.ProC.finiteGroupClassProCPredicate C)
      G (ProCCompletionLimitCarrier C G) (proCCompletionLimitCarrierMap C G) :=
  isProCCompletion_of_finiteDiscreteQuotientLifts
    (C := C) hForm hCarrier hdense hlifts

end ProCGroups.Completion
