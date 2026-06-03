import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Algebra.Module.Pi

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/InverseSystems/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Concrete inverse systems

This file defines a concrete, calculation-oriented inverse-system wrapper for
topological spaces and its subtype inverse limit.  Categorical diagram bridges
live in `ProCGroups.InverseSystems.CategoryBridge`.
-/

open Set
open scoped Topology

namespace ProCGroups
namespace InverseSystems

universe u v w

section

variable {I : Type u} [Preorder I]

/-- An inverse system of topological spaces indexed by a preorder. -/
structure InverseSystem where
  X : I → Type v
  topologicalSpace : ∀ i, TopologicalSpace (X i)
  map : ∀ {i j : I}, i ≤ j → X j → X i
  continuous_map : ∀ {i j : I} (hij : i ≤ j), Continuous (map hij)
  map_id : ∀ i, map (le_rfl : i ≤ i) = id
  map_comp : ∀ {i j k : I} (hij : i ≤ j) (hjk : j ≤ k),
    map hij ∘ map hjk = map (hij.trans hjk)

attribute [instance] InverseSystem.topologicalSpace

namespace InverseSystem

variable (S : InverseSystem (I := I))

/-- The transition map along `i ≤ i` is the identity on points. -/
@[simp] theorem map_id_apply (i : I) (x : S.X i) :
    S.map (le_rfl : i ≤ i) x = x := by
  simpa using congrFun (S.map_id i) x

/-- Transition maps compose pointwise along comparable indices. -/
@[simp] theorem map_comp_apply {i j k : I} (hij : i ≤ j) (hjk : j ≤ k) (x : S.X k) :
    S.map hij (S.map hjk x) = S.map (hij.trans hjk) x := by
  simpa [Function.comp] using congrFun (S.map_comp hij hjk) x

/-- Compatibility of a family of points in the product. -/
def Compatible (x : ∀ i, S.X i) : Prop :=
  ∀ i j, ∀ hij : i ≤ j, S.map hij (x j) = x i

/-- Compatibility of a family of maps into an inverse system. -/
def CompatibleMaps {Y : Type w} (ψ : ∀ i, Y → S.X i) : Prop :=
  ∀ i j, ∀ hij : i ≤ j, S.map hij ∘ ψ j = ψ i

/-- The inverse limit realized as a subtype of the product. -/
abbrev inverseLimit : Type _ := {x : ∀ i, S.X i // S.Compatible x}

/-- The canonical projection from the inverse limit to the `i`-th component. -/
def projection (i : I) : S.inverseLimit → S.X i := fun x => x.1 i

/-- Linearity data for an inverse system and its concrete inverse-limit cone.

This companion predicate packages the scalar-compatibility facts used by Hom-comparison APIs,
without installing them as global typeclass instances. -/
def IsLinearSystem {R : Type w} [Semiring R] (S : InverseSystem (I := I))
    [∀ i, AddCommMonoid (S.X i)] [∀ i, Module R (S.X i)]
    [AddCommMonoid S.inverseLimit] [Module R S.inverseLimit] : Prop :=
  (∀ {i j : I} (hij : i ≤ j) (r : R) (x : S.X j),
    S.map hij (r • x) = r • S.map hij x) ∧
  (∀ i (r : R) (x : S.inverseLimit), S.projection i (r • x) = r • S.projection i x)

namespace IsLinearSystem

theorem map_smul {R : Type w} [Semiring R] {S : InverseSystem (I := I)}
    [∀ i, AddCommMonoid (S.X i)] [∀ i, Module R (S.X i)]
    [AddCommMonoid S.inverseLimit] [Module R S.inverseLimit]
    (hS : IsLinearSystem (R := R) S) {i j : I} (hij : i ≤ j) (r : R) (x : S.X j) :
    S.map hij (r • x) = r • S.map hij x :=
  hS.1 hij r x

theorem projection_smul {R : Type w} [Semiring R] {S : InverseSystem (I := I)}
    [∀ i, AddCommMonoid (S.X i)] [∀ i, Module R (S.X i)]
    [AddCommMonoid S.inverseLimit] [Module R S.inverseLimit]
    (hS : IsLinearSystem (R := R) S) (i : I) (r : R) (x : S.inverseLimit) :
    S.projection i (r • x) = r • S.projection i x :=
  hS.2 i r x

end IsLinearSystem

/-- Evaluating the canonical projection is evaluation of the underlying compatible family. -/
@[simp] theorem projection_apply (i : I) (x : S.inverseLimit) :
    S.projection i x = x.1 i := rfl

/-- Projections from the inverse limit are compatible with the transition maps. -/
theorem projection_compatible (x : S.inverseLimit) (i j : I) (hij : i ≤ j) :
    S.map hij (S.projection j x) = S.projection i x := by
  exact x.2 i j hij

/-- The canonical projections form a compatible family of maps. -/
theorem projection_compatibleMaps : S.CompatibleMaps S.projection := by
  intro i j hij
  funext x
  exact S.projection_compatible x i j hij

/-- Each canonical projection from an inverse limit is continuous. -/
theorem continuous_projection (i : I) : Continuous (S.projection i) :=
  (continuous_apply i).comp continuous_subtype_val

/-- Two inverse-limit points are equal when all their projections are equal. -/
@[ext] theorem ext {x y : S.inverseLimit}
    (h : ∀ i, S.projection i x = S.projection i y) : x = y := by
  apply Subtype.ext
  funext i
  exact h i

/-- The concrete map induced by a compatible family of maps into the subtype inverse limit. -/
def inverseLimitLift {Y : Type w} (ψ : ∀ i, Y → S.X i)
    (hcompat : S.CompatibleMaps ψ) :
    Y → S.inverseLimit := fun y =>
      ⟨fun i => ψ i y, by
      intro i j hij
      exact congrFun (hcompat i j hij) y⟩

/-- A canonical projection composed with the lift recovers the corresponding compatible map. -/
@[simp] theorem projection_comp_inverseLimitLift {Y : Type w} (ψ : ∀ i, Y → S.X i)
    (hcompat : S.CompatibleMaps ψ) (i : I) :
    S.projection i ∘ S.inverseLimitLift ψ hcompat = ψ i := rfl

/-- Applying a canonical projection to the lift of a compatible family. -/
@[simp] theorem projection_inverseLimitLift_apply {Y : Type w} (ψ : ∀ i, Y → S.X i)
    (hcompat : S.CompatibleMaps ψ) (i : I) (y : Y) :
    S.projection i (S.inverseLimitLift ψ hcompat y) = ψ i y := rfl

/-- A map into the subtype inverse limit is uniquely determined by its projections. -/
theorem inverseLimitLift_unique {Y : Type w} (ψ : ∀ i, Y → S.X i)
    (hcompat : S.CompatibleMaps ψ) {f : Y → S.inverseLimit}
    (hf : ∀ i, S.projection i ∘ f = ψ i) :
    f = S.inverseLimitLift ψ hcompat := by
  funext y
  apply S.ext
  intro i
  simpa [Function.comp] using congrFun (hf i) y

/-- A lift from a topological space is continuous when all of its component maps are continuous. -/
theorem continuous_inverseLimitLift {Y : Type w} [TopologicalSpace Y] (ψ : ∀ i, Y → S.X i)
    (hψ : ∀ i, Continuous (ψ i))
    (hcompat : S.CompatibleMaps ψ) :
    Continuous (S.inverseLimitLift ψ hcompat) := by
  exact Continuous.subtype_mk (continuous_pi fun i => hψ i) fun y => by
    intro i j hij
    exact congrFun (hcompat i j hij) y

/-- The universal property of an inverse limit. -/
structure IsInverseLimit {L : Type w} [TopologicalSpace L] (π : ∀ i, L → S.X i) : Prop where
  continuous_proj : ∀ i, Continuous (π i)
  compatible : S.CompatibleMaps π
  existsUnique_lift :
    ∀ {Y : Type w} [TopologicalSpace Y] (ψ : ∀ i, Y → S.X i)
      (_hψ : ∀ i, Continuous (ψ i)) (_hcompat : S.CompatibleMaps ψ),
      ∃! f : Y → L, Continuous f ∧ ∀ i, π i ∘ f = ψ i

namespace IsInverseLimit

variable {S}
variable {L : Type w} [TopologicalSpace L] {π : ∀ i, L → S.X i}

/-- The map supplied by the inverse-limit universal property. -/
noncomputable def lift (hπ : S.IsInverseLimit π) {Y : Type w} [TopologicalSpace Y]
    (ψ : ∀ i, Y → S.X i) (hψ : ∀ i, Continuous (ψ i)) (hcompat : S.CompatibleMaps ψ) :
    Y → L :=
  Classical.choose (ExistsUnique.exists (hπ.existsUnique_lift ψ hψ hcompat))

/-- The universal-property lift is continuous and has the prescribed projections. -/
theorem lift_spec (hπ : S.IsInverseLimit π) {Y : Type w} [TopologicalSpace Y]
    (ψ : ∀ i, Y → S.X i) (hψ : ∀ i, Continuous (ψ i)) (hcompat : S.CompatibleMaps ψ) :
    Continuous (hπ.lift ψ hψ hcompat) ∧
      ∀ i, π i ∘ hπ.lift ψ hψ hcompat = ψ i :=
  Classical.choose_spec (ExistsUnique.exists (hπ.existsUnique_lift ψ hψ hcompat))

/-- The universal-property lift is continuous. -/
theorem continuous_lift (hπ : S.IsInverseLimit π) {Y : Type w} [TopologicalSpace Y]
    (ψ : ∀ i, Y → S.X i) (hψ : ∀ i, Continuous (ψ i)) (hcompat : S.CompatibleMaps ψ) :
    Continuous (hπ.lift ψ hψ hcompat) :=
  (hπ.lift_spec ψ hψ hcompat).1

/-- The universal-property lift has the prescribed `i`-th projection. -/
theorem fac (hπ : S.IsInverseLimit π) {Y : Type w} [TopologicalSpace Y]
    (ψ : ∀ i, Y → S.X i) (hψ : ∀ i, Continuous (ψ i)) (hcompat : S.CompatibleMaps ψ)
    (i : I) :
    π i ∘ hπ.lift ψ hψ hcompat = ψ i :=
  (hπ.lift_spec ψ hψ hcompat).2 i

/-- The universal-property lift is the unique continuous map with the prescribed projections. -/
theorem uniq (hπ : S.IsInverseLimit π) {Y : Type w} [TopologicalSpace Y]
    (ψ : ∀ i, Y → S.X i) (hψ : ∀ i, Continuous (ψ i)) (hcompat : S.CompatibleMaps ψ)
    {f : Y → L} (hf : Continuous f) (hfac : ∀ i, π i ∘ f = ψ i) :
    f = hπ.lift ψ hψ hcompat := by
  rcases hπ.existsUnique_lift ψ hψ hcompat with ⟨g, hg, huniq⟩
  have hchosen : hπ.lift ψ hψ hcompat = g := huniq _ (hπ.lift_spec ψ hψ hcompat)
  exact (huniq _ ⟨hf, hfac⟩).trans hchosen.symm

/-- Lifting the projection family of an inverse limit gives the identity map. -/
theorem lift_self (hπ : S.IsInverseLimit π) :
    hπ.lift (Y := L) π hπ.continuous_proj hπ.compatible = id := by
  symm
  exact hπ.uniq (Y := L) π hπ.continuous_proj hπ.compatible continuous_id fun _ => rfl

/-- Inverse limits are unique up to unique homeomorphism. -/
noncomputable def homeomorph {L' : Type w} [TopologicalSpace L'] {π' : ∀ i, L' → S.X i}
    (hπ : S.IsInverseLimit π) (hπ' : S.IsInverseLimit π') :
    L ≃ₜ L' where
  toFun := hπ'.lift (Y := L) π hπ.continuous_proj hπ.compatible
  invFun := hπ.lift (Y := L') π' hπ'.continuous_proj hπ'.compatible
  left_inv := by
    intro x
    let f : L → L' := hπ'.lift (Y := L) π hπ.continuous_proj hπ.compatible
    let g : L' → L := hπ.lift (Y := L') π' hπ'.continuous_proj hπ'.compatible
    have hgf : g ∘ f = hπ.lift (Y := L) π hπ.continuous_proj hπ.compatible := by
      exact hπ.uniq (Y := L) π hπ.continuous_proj hπ.compatible
        ((hπ.continuous_lift (Y := L') π' hπ'.continuous_proj hπ'.compatible).comp
          (hπ'.continuous_lift (Y := L) π hπ.continuous_proj hπ.compatible))
        (by
          intro i
          calc
            π i ∘ (g ∘ f) = (π i ∘ g) ∘ f := by rfl
            _ = π' i ∘ f := by
              rw [hπ.fac (Y := L') π' hπ'.continuous_proj hπ'.compatible i]
            _ = π i := by
              simpa [Function.comp] using
                hπ'.fac (Y := L) π hπ.continuous_proj hπ.compatible i)
    calc
      g (f x) = hπ.lift (Y := L) π hπ.continuous_proj hπ.compatible x := congrFun hgf x
      _ = x := by
        simpa using congrFun hπ.lift_self x
  right_inv := by
    intro x
    let f : L → L' := hπ'.lift (Y := L) π hπ.continuous_proj hπ.compatible
    let g : L' → L := hπ.lift (Y := L') π' hπ'.continuous_proj hπ'.compatible
    have hfg : f ∘ g = hπ'.lift (Y := L') π' hπ'.continuous_proj hπ'.compatible := by
      exact hπ'.uniq (Y := L') π' hπ'.continuous_proj hπ'.compatible
        ((hπ'.continuous_lift (Y := L) π hπ.continuous_proj hπ.compatible).comp
          (hπ.continuous_lift (Y := L') π' hπ'.continuous_proj hπ'.compatible))
        (by
          intro i
          calc
            π' i ∘ (f ∘ g) = (π' i ∘ f) ∘ g := by rfl
            _ = π i ∘ g := by
              rw [hπ'.fac (Y := L) π hπ.continuous_proj hπ.compatible i]
            _ = π' i := by
              simpa [Function.comp] using
                hπ.fac (Y := L') π' hπ'.continuous_proj hπ'.compatible i)
    calc
      f (g x) = hπ'.lift (Y := L') π' hπ'.continuous_proj hπ'.compatible x := congrFun hfg x
      _ = x := by
        simpa using congrFun hπ'.lift_self x
  continuous_toFun := hπ'.continuous_lift (Y := L) π hπ.continuous_proj hπ.compatible
  continuous_invFun := hπ.continuous_lift (Y := L') π' hπ'.continuous_proj hπ'.compatible

end IsInverseLimit

/-- The subtype model carries the inverse-limit universal property. -/
theorem isInverseLimit_projection : S.IsInverseLimit S.projection := by
  refine ⟨S.continuous_projection, S.projection_compatibleMaps, ?_⟩
  intro Y _ ψ hψ hcompat
  refine ⟨S.inverseLimitLift ψ hcompat, ?_, ?_⟩
  · exact ⟨S.continuous_inverseLimitLift ψ hψ hcompat,
      fun i => S.projection_comp_inverseLimitLift ψ hcompat i⟩
  · intro f hf
    exact S.inverseLimitLift_unique ψ hcompat hf.2

/-- The inverse limit is a closed subspace of the product. -/
theorem isClosed_setOf_compatible [∀ i, T2Space (S.X i)] :
    IsClosed {x : ∀ i, S.X i | S.Compatible x} := by
  simp only [Compatible, setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun hij => ?_
  exact isClosed_eq ((S.continuous_map hij).comp (continuous_apply j)) (continuous_apply i)

/-- The inverse limit of compact Hausdorff stages is compact. -/
instance instCompactSpaceInverseLimit [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)] :
    CompactSpace S.inverseLimit := by
  let hs : IsClosed {x : ∀ i, S.X i | S.Compatible x} := S.isClosed_setOf_compatible
  simpa [InverseSystem.inverseLimit] using hs.isClosedEmbedding_subtypeVal.compactSpace

/-- Inverse limits of Hausdorff spaces are Hausdorff. -/
theorem t2Space_inverseLimit [∀ i, T2Space (S.X i)] :
    T2Space S.inverseLimit := inferInstance

/-- Inverse limits of totally disconnected spaces are totally disconnected. -/
theorem totallyDisconnectedSpace_inverseLimit [∀ i, TotallyDisconnectedSpace (S.X i)] :
    TotallyDisconnectedSpace S.inverseLimit := inferInstance

/-- A surjective projection from a compact inverse limit to a Hausdorff stage is a quotient map. -/
theorem isQuotientMap_projection_of_surjective [∀ i, CompactSpace (S.X i)]
    [∀ i, T2Space (S.X i)] {i : I} (hsurj : Function.Surjective (S.projection i)) :
    Topology.IsQuotientMap (S.projection i) :=
  IsQuotientMap.of_surjective_continuous hsurj (S.continuous_projection i)

end InverseSystem

section GroupSystems

variable {I : Type u} [Preorder I] (S : InverseSystem (I := I))

/-- A group-valued inverse system whose transition maps are group homomorphisms. -/
class IsGroupSystem (S : InverseSystem (I := I)) [∀ i, Group (S.X i)] : Prop where
  map_one : ∀ {i j : I} (hij : i ≤ j), S.map hij 1 = 1
  map_mul : ∀ {i j : I} (hij : i ≤ j) (x y : S.X j),
    S.map hij (x * y) = S.map hij x * S.map hij y
  map_inv : ∀ {i j : I} (hij : i ≤ j) (x : S.X j),
    S.map hij x⁻¹ = (S.map hij x)⁻¹

variable [∀ i, Group (S.X i)] [IsGroupSystem S]

/-- The identity element of a group-valued inverse limit is defined coordinatewise. -/
instance instOneInverseLimit : One S.inverseLimit where
  one := ⟨fun i => 1, by
    intro i j hij
    simpa using IsGroupSystem.map_one (S := S) hij⟩

/-- Multiplication in a group-valued inverse limit is defined coordinatewise. -/
instance instMulInverseLimit : Mul S.inverseLimit where
  mul x y := ⟨fun i => S.projection i x * S.projection i y, by
    intro i j hij
    calc
      S.map hij (S.projection j x * S.projection j y)
          = S.map hij (S.projection j x) * S.map hij (S.projection j y) := by
              simpa using IsGroupSystem.map_mul (S := S) hij (S.projection j x)
                (S.projection j y)
      _ = S.projection i x * S.projection i y := by
          rw [S.projection_compatible x i j hij, S.projection_compatible y i j hij]⟩

/-- Inversion in a group-valued inverse limit is defined coordinatewise. -/
instance instInvInverseLimit : Inv S.inverseLimit where
  inv x := ⟨fun i => (S.projection i x)⁻¹, by
    intro i j hij
    calc
      S.map hij ((S.projection j x)⁻¹) = (S.map hij (S.projection j x))⁻¹ := by
        simpa using IsGroupSystem.map_inv (S := S) hij (S.projection j x)
      _ = (S.projection i x)⁻¹ := by rw [S.projection_compatible x i j hij]⟩

/-- The projection of the identity element is the identity at each stage. -/
@[simp] theorem projection_one (i : I) : S.projection i (1 : S.inverseLimit) = 1 := rfl

/-- Projection commutes with multiplication in a group-valued inverse system. -/
@[simp] theorem projection_mul (i : I) (x y : S.inverseLimit) :
    S.projection i (x * y) = S.projection i x * S.projection i y := rfl

/-- Projection commutes with inversion in a group-valued inverse system. -/
@[simp] theorem projection_inv (i : I) (x : S.inverseLimit) :
    S.projection i x⁻¹ = (S.projection i x)⁻¹ := rfl

/-- A group-valued inverse limit inherits a group structure coordinatewise. -/
instance instGroupInverseLimit : Group S.inverseLimit where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc x y z := by
    apply S.ext
    intro i
    change ((x.1 i * y.1 i) * z.1 i) = (x.1 i * (y.1 i * z.1 i))
    simp only [mul_assoc]
  one_mul x := by
    apply S.ext
    intro i
    change 1 * x.1 i = x.1 i
    simp only [one_mul]
  mul_one x := by
    apply S.ext
    intro i
    change x.1 i * 1 = x.1 i
    simp only [mul_one]
  inv_mul_cancel x := by
    apply S.ext
    intro i
    change (x.1 i)⁻¹ * x.1 i = 1
    simp only [inv_mul_cancel]

/-- An inverse limit of topological group stages is a topological group. -/
instance instIsTopologicalGroupInverseLimit [∀ i, IsTopologicalGroup (S.X i)] :
    IsTopologicalGroup S.inverseLimit where
  continuous_mul := by
    exact Continuous.subtype_mk
      (continuous_pi fun i =>
        ((S.continuous_projection i).comp continuous_fst).mul
          ((S.continuous_projection i).comp continuous_snd))
      (fun xy => by
        intro i j hij
        change S.map hij (S.projection j xy.1 * S.projection j xy.2) =
          S.projection i xy.1 * S.projection i xy.2
        rw [IsGroupSystem.map_mul (S := S) hij,
          S.projection_compatible xy.1 i j hij, S.projection_compatible xy.2 i j hij])
  continuous_inv := by
    exact Continuous.subtype_mk
      (continuous_pi fun i => continuous_inv.comp (S.continuous_projection i))
      (fun x => by
        intro i j hij
        change S.map hij ((S.projection j x)⁻¹) = (S.projection i x)⁻¹
        rw [IsGroupSystem.map_inv (S := S) hij, S.projection_compatible x i j hij])

/-- The canonical projections from a group-valued inverse limit are homomorphisms. -/
def projectionHom (i : I) : S.inverseLimit →* S.X i where
  toFun := S.projection i
  map_one' := projection_one (S := S) i
  map_mul' := by
    intro x y
    exact projection_mul (S := S) i x y

/-- Evaluating the projection homomorphism is the same as evaluating the projection. -/
@[simp] theorem projectionHom_apply (i : I) (x : S.inverseLimit) :
    projectionHom (S := S) i x = S.projection i x := rfl

end GroupSystems

section AddGroupSystems

variable {I : Type u} [Preorder I] (S : InverseSystem (I := I))

/-- An additive-group-valued inverse system whose transition maps are additive homomorphisms. -/
class IsAddGroupSystem (S : InverseSystem (I := I)) [∀ i, AddCommGroup (S.X i)] : Prop where
  map_zero : ∀ {i j : I} (hij : i ≤ j), S.map hij 0 = 0
  map_add : ∀ {i j : I} (hij : i ≤ j) (x y : S.X j),
    S.map hij (x + y) = S.map hij x + S.map hij y
  map_neg : ∀ {i j : I} (hij : i ≤ j) (x : S.X j),
    S.map hij (-x) = -S.map hij x

variable [∀ i, AddCommGroup (S.X i)] [IsAddGroupSystem S]

/-- A module-valued inverse system whose transition maps are linear over a fixed semiring. -/
class IsModuleSystem (R : Type w) [Semiring R] (S : InverseSystem (I := I))
    [∀ i, AddCommGroup (S.X i)] [∀ i, Module R (S.X i)] : Prop where
  map_smul : ∀ {i j : I} (hij : i ≤ j) (r : R) (x : S.X j),
    S.map hij (r • x) = r • S.map hij x

/-- The zero element of an additive-group-valued inverse limit is defined coordinatewise. -/
instance instZeroAddInverseLimit : Zero S.inverseLimit where
  zero := ⟨fun i => 0, by
    intro i j hij
    simpa using IsAddGroupSystem.map_zero (S := S) hij⟩

/-- Addition in an additive-group-valued inverse limit is defined coordinatewise. -/
instance instAddAddInverseLimit : Add S.inverseLimit where
  add x y := ⟨fun i => S.projection i x + S.projection i y, by
    intro i j hij
    calc
      S.map hij (S.projection j x + S.projection j y)
          = S.map hij (S.projection j x) + S.map hij (S.projection j y) := by
              simpa using IsAddGroupSystem.map_add (S := S) hij (S.projection j x)
                (S.projection j y)
      _ = S.projection i x + S.projection i y := by
          rw [S.projection_compatible x i j hij, S.projection_compatible y i j hij]⟩

/-- Negation in an additive-group-valued inverse limit is defined coordinatewise. -/
instance instNegAddInverseLimit : Neg S.inverseLimit where
  neg x := ⟨fun i => -S.projection i x, by
    intro i j hij
    calc
      S.map hij (-S.projection j x) = -S.map hij (S.projection j x) := by
        simpa using IsAddGroupSystem.map_neg (S := S) hij (S.projection j x)
      _ = -S.projection i x := by rw [S.projection_compatible x i j hij]⟩

/-- Subtraction in an additive-group-valued inverse limit is defined coordinatewise. -/
instance instSubAddInverseLimit : Sub S.inverseLimit where
  sub x y := ⟨fun i => S.projection i x - S.projection i y, by
    intro i j hij
    change S.map hij (S.projection j x - S.projection j y) =
      S.projection i x - S.projection i y
    rw [sub_eq_add_neg, IsAddGroupSystem.map_add, IsAddGroupSystem.map_neg,
      S.projection_compatible x i j hij, S.projection_compatible y i j hij, sub_eq_add_neg]⟩

instance instSMulNatAddInverseLimit : SMul ℕ S.inverseLimit where
  smul n x := ⟨fun i => n • S.projection i x, by
    intro i j hij
    change S.map hij (n • S.projection j x) = n • S.projection i x
    induction n with
    | zero =>
        simp only [InverseSystem.projection_apply, zero_nsmul, IsAddGroupSystem.map_zero]
    | succ n ihn =>
        rw [succ_nsmul, succ_nsmul]
        calc
          S.map hij (n • S.projection j x + S.projection j x)
              = S.map hij (n • S.projection j x) + S.map hij (S.projection j x) := by
                  exact IsAddGroupSystem.map_add (S := S) hij (n • S.projection j x)
                    (S.projection j x)
          _ = n • S.projection i x + S.projection i x := by
              rw [ihn, S.projection_compatible x i j hij]⟩

instance instSMulIntAddInverseLimit : SMul ℤ S.inverseLimit where
  smul n x := ⟨fun i => n • S.projection i x, by
    intro i j hij
    change S.map hij (n • S.projection j x) = n • S.projection i x
    let f : S.X j →+ S.X i :=
      { toFun := S.map hij
        map_zero' := IsAddGroupSystem.map_zero (S := S) hij
        map_add' := IsAddGroupSystem.map_add (S := S) hij }
    calc
      S.map hij (n • S.projection j x) = f (n • S.projection j x) := rfl
      _ = n • f (S.projection j x) := f.map_zsmul (S.projection j x) n
      _ = n • S.projection i x := by
        change n • S.map hij (S.projection j x) = n • S.projection i x
        rw [S.projection_compatible x i j hij]⟩

/-- The projection of zero is zero at each stage. -/
@[simp] theorem projection_zero (i : I) : S.projection i (0 : S.inverseLimit) = 0 := rfl

/-- Projection commutes with addition in an additive inverse system. -/
@[simp] theorem projection_add (i : I) (x y : S.inverseLimit) :
    S.projection i (x + y) = S.projection i x + S.projection i y := rfl

/-- Projection commutes with negation in an additive inverse system. -/
@[simp] theorem projection_neg (i : I) (x : S.inverseLimit) :
    S.projection i (-x) = -S.projection i x := rfl

/-- Projection commutes with subtraction in an additive inverse system. -/
@[simp] theorem projection_sub (i : I) (x y : S.inverseLimit) :
    S.projection i (x - y) = S.projection i x - S.projection i y := rfl

/-- An additive-group-valued inverse limit inherits an additive commutative group structure. -/
instance instAddCommGroupAddInverseLimit : AddCommGroup S.inverseLimit := by
  let f : S.inverseLimit → ∀ i, S.X i := Subtype.val
  apply Subtype.val_injective.addCommGroup f rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

section ModuleSystems

variable {R : Type w} [Semiring R]
variable [∀ i, Module R (S.X i)] [IsModuleSystem (I := I) R S]

/-- Scalar multiplication on a module-valued inverse limit is defined coordinatewise. -/
instance instSMulInverseLimitOfIsModuleSystem : SMul R S.inverseLimit where
  smul r x := ⟨fun i => r • S.projection i x, by
    intro i j hij
    change S.map hij (r • S.projection j x) = r • S.projection i x
    rw [IsModuleSystem.map_smul (S := S) hij, S.projection_compatible x i j hij]⟩

omit [IsAddGroupSystem S] in
/-- Projection commutes with scalar multiplication in a module-valued inverse system. -/
@[simp] theorem projection_smul_of_isModuleSystem (i : I) (r : R) (x : S.inverseLimit) :
    S.projection i (r • x) = r • S.projection i x :=
  rfl

/-- A module-valued inverse limit inherits a module structure coordinatewise. -/
instance instModuleInverseLimitOfIsModuleSystem : Module R S.inverseLimit := by
  let f : S.inverseLimit →+ ∀ i, S.X i :=
    { toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact Function.Injective.module R f Subtype.val_injective (fun _ _ => rfl)

/-- Scalar multiplication on a module-valued inverse limit is continuous when it is continuous
stagewise. -/
instance instContinuousSMulInverseLimitOfIsModuleSystem
    [TopologicalSpace R] [∀ i, ContinuousSMul R (S.X i)] :
    ContinuousSMul R S.inverseLimit where
  continuous_smul := by
    exact Continuous.subtype_mk
      (continuous_pi fun i =>
        continuous_fst.smul ((S.continuous_projection i).comp continuous_snd))
      (fun p => by
        intro i j hij
        change S.map hij (p.1 • S.projection j p.2) = p.1 • S.projection i p.2
        rw [IsModuleSystem.map_smul (S := S) hij, S.projection_compatible p.2 i j hij])

end ModuleSystems

/-- An inverse limit of topological additive groups is a topological additive group. -/
instance instIsTopologicalAddGroupAddInverseLimit [∀ i, IsTopologicalAddGroup (S.X i)] :
    IsTopologicalAddGroup S.inverseLimit where
  continuous_add := by
    exact Continuous.subtype_mk
      (continuous_pi fun i =>
        ((S.continuous_projection i).comp continuous_fst).add
          ((S.continuous_projection i).comp continuous_snd))
      (fun xy => by
        intro i j hij
        change S.map hij (S.projection j xy.1 + S.projection j xy.2) =
          S.projection i xy.1 + S.projection i xy.2
        rw [IsAddGroupSystem.map_add (S := S) hij,
          S.projection_compatible xy.1 i j hij, S.projection_compatible xy.2 i j hij])
  continuous_neg := by
    exact Continuous.subtype_mk
      (continuous_pi fun i => continuous_neg.comp (S.continuous_projection i))
      (fun x => by
        intro i j hij
        change S.map hij (-S.projection j x) = -S.projection i x
        rw [IsAddGroupSystem.map_neg (S := S) hij, S.projection_compatible x i j hij])

/-- The canonical projections from an additive inverse limit are additive homomorphisms. -/
def projectionAddHom (i : I) : S.inverseLimit →+ S.X i where
  toFun := S.projection i
  map_zero' := projection_zero (S := S) i
  map_add' := by
    intro x y
    exact projection_add (S := S) i x y

/-- Evaluating the projection additive homomorphism is projection evaluation. -/
@[simp] theorem projectionAddHom_apply (i : I) (x : S.inverseLimit) :
    projectionAddHom (S := S) i x = S.projection i x := rfl

end AddGroupSystems

section RingSystems

variable {I : Type u} [Preorder I] (S : InverseSystem (I := I))

/-- A ring-valued inverse system whose transition maps are ring homomorphisms. -/
class IsRingSystem (S : InverseSystem (I := I)) [∀ i, Ring (S.X i)] : Prop where
  map_zero : ∀ {i j : I} (hij : i ≤ j), S.map hij 0 = 0
  map_one : ∀ {i j : I} (hij : i ≤ j), S.map hij 1 = 1
  map_add : ∀ {i j : I} (hij : i ≤ j) (x y : S.X j),
    S.map hij (x + y) = S.map hij x + S.map hij y
  map_mul : ∀ {i j : I} (hij : i ≤ j) (x y : S.X j),
    S.map hij (x * y) = S.map hij x * S.map hij y

variable [∀ i, Ring (S.X i)] [IsRingSystem S]

/-- A transition map in a ring-valued inverse system, bundled as a ring homomorphism. -/
def mapRingHom {i j : I} (hij : i ≤ j) : S.X j →+* S.X i where
  toFun := S.map hij
  map_zero' := IsRingSystem.map_zero (S := S) hij
  map_one' := IsRingSystem.map_one (S := S) hij
  map_add' := IsRingSystem.map_add (S := S) hij
  map_mul' := IsRingSystem.map_mul (S := S) hij

@[simp]
theorem mapRingHom_apply {i j : I} (hij : i ≤ j) (x : S.X j) :
    mapRingHom (S := S) hij x = S.map hij x := rfl

instance instIsAddGroupSystemOfIsRingSystem : IsAddGroupSystem S where
  map_zero := IsRingSystem.map_zero (S := S)
  map_add := IsRingSystem.map_add (S := S)
  map_neg := by
    intro i j hij x
    exact (mapRingHom (S := S) hij).map_neg x

/-- Multiplication in a ring-valued inverse limit is defined coordinatewise. -/
instance instMulRingInverseLimit : Mul S.inverseLimit where
  mul x y := ⟨fun i => S.projection i x * S.projection i y, by
    intro i j hij
    calc
      S.map hij (S.projection j x * S.projection j y)
          = S.map hij (S.projection j x) * S.map hij (S.projection j y) := by
              exact IsRingSystem.map_mul (S := S) hij (S.projection j x)
                (S.projection j y)
      _ = S.projection i x * S.projection i y := by
          rw [S.projection_compatible x i j hij, S.projection_compatible y i j hij]⟩

/-- The unit in a ring-valued inverse limit is defined coordinatewise. -/
instance instOneRingInverseLimit : One S.inverseLimit where
  one := ⟨fun i => 1, by
    intro i j hij
    exact IsRingSystem.map_one (S := S) hij⟩

/-- Natural powers in a ring-valued inverse limit are defined coordinatewise. -/
instance instPowNatRingInverseLimit : Pow S.inverseLimit ℕ where
  pow x n := ⟨fun i => S.projection i x ^ n, by
    intro i j hij
    change S.map hij (S.projection j x ^ n) = S.projection i x ^ n
    rw [← mapRingHom_apply (S := S) hij, map_pow, mapRingHom_apply,
      S.projection_compatible x i j hij]⟩

/-- Natural-number casts in a ring-valued inverse limit are defined coordinatewise. -/
instance instNatCastRingInverseLimit : NatCast S.inverseLimit where
  natCast n := ⟨fun _ => n, by
    intro i j hij
    change S.map hij (Nat.cast n) = Nat.cast n
    exact map_natCast (mapRingHom (S := S) hij) n⟩

/-- Integer casts in a ring-valued inverse limit are defined coordinatewise. -/
instance instIntCastRingInverseLimit : IntCast S.inverseLimit where
  intCast n := ⟨fun _ => n, by
    intro i j hij
    change S.map hij (Int.cast n) = Int.cast n
    exact map_intCast (mapRingHom (S := S) hij) n⟩

@[simp]
theorem projection_ring_one (i : I) : S.projection i (1 : S.inverseLimit) = 1 := rfl

@[simp]
theorem projection_ring_mul (i : I) (x y : S.inverseLimit) :
    S.projection i (x * y) = S.projection i x * S.projection i y := rfl

@[simp]
theorem projection_ring_pow (i : I) (x : S.inverseLimit) (n : ℕ) :
    S.projection i (x ^ n) = S.projection i x ^ n := rfl

@[simp]
theorem projection_ring_natCast (i : I) (n : ℕ) :
    S.projection i (Nat.cast n : S.inverseLimit) = Nat.cast n := rfl

@[simp]
theorem projection_ring_intCast (i : I) (n : ℤ) :
    S.projection i (Int.cast n : S.inverseLimit) = Int.cast n := rfl

/-- A ring-valued inverse limit inherits a ring structure coordinatewise. -/
instance instRingInverseLimit : Ring S.inverseLimit :=
  Function.Injective.ring
    (fun x : S.inverseLimit => (x : ∀ i, S.X i))
    Subtype.val_injective
    (by funext i; rfl)
    (by funext i; rfl)
    (by intro x y; funext i; rfl)
    (by intro x y; funext i; rfl)
    (by intro x; funext i; rfl)
    (by intro x y; funext i; rfl)
    (by intro n x; funext i; rfl)
    (by intro n x; funext i; rfl)
    (by intro x n; funext i; rfl)
    (by intro n; funext i; rfl)
    (by intro n; funext i; rfl)

/-- Multiplication on a ring-valued inverse limit is continuous when it is continuous stagewise. -/
instance instContinuousMulRingInverseLimit [∀ i, ContinuousMul (S.X i)] :
    ContinuousMul S.inverseLimit where
  continuous_mul := by
    exact Continuous.subtype_mk
      (continuous_pi fun i =>
        ((S.continuous_projection i).comp continuous_fst).mul
          ((S.continuous_projection i).comp continuous_snd))
      (fun xy => by
        intro i j hij
        change S.map hij (S.projection j xy.1 * S.projection j xy.2) =
          S.projection i xy.1 * S.projection i xy.2
        rw [IsRingSystem.map_mul (S := S) hij,
          S.projection_compatible xy.1 i j hij, S.projection_compatible xy.2 i j hij])

/-- An inverse limit of topological rings is a topological ring. -/
instance instIsTopologicalRingRingInverseLimit [∀ i, IsTopologicalRing (S.X i)] :
    IsTopologicalRing S.inverseLimit := by
  letI : IsTopologicalAddGroup S.inverseLimit :=
    instIsTopologicalAddGroupAddInverseLimit S
  letI : ContinuousMul S.inverseLimit := instContinuousMulRingInverseLimit S
  letI : IsTopologicalSemiring S.inverseLimit := IsTopologicalSemiring.mk
  exact IsTopologicalRing.mk

/-- The canonical projection from a ring-valued inverse limit, bundled as a ring homomorphism. -/
def projectionRingHom (i : I) : S.inverseLimit →+* S.X i where
  toFun := S.projection i
  map_zero' := projection_zero (S := S) i
  map_one' := projection_ring_one (S := S) i
  map_add' := by
    intro x y
    exact projection_add (S := S) i x y
  map_mul' := by
    intro x y
    exact projection_ring_mul (S := S) i x y

@[simp]
theorem projectionRingHom_apply (i : I) (x : S.inverseLimit) :
    projectionRingHom (S := S) i x = S.projection i x := rfl

/-- The ring-valued transition from `j` to `i` composed with the `j`-th projection is the
`i`-th projection. -/
theorem mapRingHom_comp_projectionRingHom {i j : I} (hij : i ≤ j) :
    (mapRingHom (S := S) hij).comp (projectionRingHom (S := S) j) =
      projectionRingHom (S := S) i := by
  apply RingHom.ext
  intro x
  exact S.projection_compatible x i j hij

end RingSystems

end
end InverseSystems
end ProCGroups
