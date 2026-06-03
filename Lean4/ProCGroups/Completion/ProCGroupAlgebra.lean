import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finsupp.Fintype
import ProCGroups.Completion.ProCInteger

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Completion/ProCGroupAlgebra.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed pro-C group algebras

Builds completed group algebras from finite quotient stages and finite cyclic coefficient stages, with coordinatewise ring operations and projection formulas.
-/

open scoped Topology

namespace ProCGroups.Completion

noncomputable section

universe u v

variable (C : FiniteGroupClass.{u})
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The open-normal quotient coordinate in the completed group-algebra indexing set. -/
abbrev ProCCompletedGroupAlgebraQuotientIndex :=
  OrderDual (ProC.OpenNormalSubgroupInClass C G)

/-- The full indexing set: a coefficient modulus and a group quotient. -/
abbrev ProCCompletedGroupAlgebraIndex :=
  ProCIntegerIndex C × ProCCompletedGroupAlgebraQuotientIndex C G

/-- The quotient group `G/U` at one group-coordinate. -/
abbrev ProCCompletedGroupAlgebraQuotient
    (U : ProCCompletedGroupAlgebraQuotientIndex C G) :=
  (ProC.openNormalSubgroupInClassSystem C G).X U

/-- The finite stage `(ZMod n)[G/U]`. -/
abbrev ProCCompletedGroupAlgebraStage
    (i : ProCCompletedGroupAlgebraIndex C G) :=
  MonoidAlgebra (ProCIntegerStage C i.1)
    (ProCCompletedGroupAlgebraQuotient C G i.2)

/-- Each finite group-algebra stage carries the discrete topology. -/
instance instTopologicalSpaceProCCompletedGroupAlgebraStage
    (i : ProCCompletedGroupAlgebraIndex C G) :
    TopologicalSpace (ProCCompletedGroupAlgebraStage C G i) :=
  ⊥

/-- Each finite group-algebra stage is discrete. -/
instance instDiscreteTopologyProCCompletedGroupAlgebraStage
    (i : ProCCompletedGroupAlgebraIndex C G) :
    DiscreteTopology (ProCCompletedGroupAlgebraStage C G i) :=
  ⟨rfl⟩

/-- The group quotient in each completed group-algebra coordinate is finite. -/
instance instFiniteProCCompletedGroupAlgebraQuotient
    (U : ProCCompletedGroupAlgebraQuotientIndex C G) :
    Finite (ProCCompletedGroupAlgebraQuotient C G U) := by
  dsimp [ProCCompletedGroupAlgebraQuotient, ProC.openNormalSubgroupInClassSystem]
  exact FiniteGroupClass.finite (C := C) (OrderDual.ofDual U).2

/-- Each completed group-algebra stage is finite. -/
instance instFiniteProCCompletedGroupAlgebraStage
    (i : ProCCompletedGroupAlgebraIndex C G) :
    Finite (ProCCompletedGroupAlgebraStage C G i) := by
  classical
  letI : NeZero i.1.modulus := ⟨Nat.ne_of_gt i.1.positive⟩
  letI : Fintype (ProCIntegerStage C i.1) := ZMod.fintype i.1.modulus
  letI : Fintype (ProCCompletedGroupAlgebraQuotient C G i.2) := Fintype.ofFinite _
  letI : DecidableEq (ProCCompletedGroupAlgebraQuotient C G i.2) := Classical.decEq _
  dsimp [ProCCompletedGroupAlgebraStage, ProCIntegerStage]
  change Finite (ProCCompletedGroupAlgebraQuotient C G i.2 →₀ ZMod i.1.modulus)
  exact Finite.of_fintype _

/-- The quotient transition map between the group coordinates. -/
def proCCompletedGroupAlgebraQuotientTransition
    {U V : ProCCompletedGroupAlgebraQuotientIndex C G} (hUV : U ≤ V) :
    ProCCompletedGroupAlgebraQuotient C G V →*
      ProCCompletedGroupAlgebraQuotient C G U :=
  ProC.OpenNormalSubgroupInClass.map (C := C) (G := G)
    (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV

/-- The transition map `(ZMod m)[G/V] -> (ZMod n)[G/U]` for a refinement of coordinates. -/
def proCCompletedGroupAlgebraTransition
    {i j : ProCCompletedGroupAlgebraIndex C G} (hij : i ≤ j) :
    ProCCompletedGroupAlgebraStage C G j →+*
      ProCCompletedGroupAlgebraStage C G i :=
  (MonoidAlgebra.mapDomainRingHom (ProCIntegerStage C i.1)
      (proCCompletedGroupAlgebraQuotientTransition (C := C) (G := G) hij.2)).comp
    (MonoidAlgebra.mapRangeRingHom
      (ProCCompletedGroupAlgebraQuotient C G j.2)
      (proCIntegerTransition (C := C) hij.1))

/-- Compatibility condition for a point of the inverse limit defining the completed group algebra. -/
def ProCCompletedGroupAlgebraCompatible
    (x : ∀ i : ProCCompletedGroupAlgebraIndex C G,
      ProCCompletedGroupAlgebraStage C G i) : Prop :=
  ∀ i j, ∀ hij : i ≤ j,
    proCCompletedGroupAlgebraTransition (C := C) (G := G) hij (x j) = x i

/-- Explicit carrier-level name for the `ProCGroups`-side pro-`C` inverse-limit implementation of
the completed group algebra.  Use this name when no Chapter 5 universal property is needed. -/
abbrev ProCCompletedGroupAlgebraLimitCarrier : Type _ :=
  {x : ∀ i : ProCCompletedGroupAlgebraIndex C G,
      ProCCompletedGroupAlgebraStage C G i //
    ProCCompletedGroupAlgebraCompatible C G x}

/-- The `ProCGroups`-side pro-`C` inverse-limit model of the completed group algebra, bundled with
its topological ring structure and canonical coefficient and group maps.

This structure deliberately records only the constructed data.  Density and universal-property
claims should be provided by separate theorems or property structures, not by arbitrary `Prop`
fields on the carrier bundle. -/
structure ProCCompletedGroupAlgebraModel where
  carrier : Type v
  [ring : Ring carrier]
  [topology : TopologicalSpace carrier]
  [topologicalRing : IsTopologicalRing carrier]
  compact : CompactSpace carrier
  t2 : T2Space carrier
  coeff : ProCIntegerLimitCarrier C →+* carrier
  groupMap : G →* carrierˣ

/-- Projection from the pro-`C` completed group-algebra carrier to a finite group-algebra stage. -/
def proCCompletedGroupAlgebraProj (i : ProCCompletedGroupAlgebraIndex C G) :
    ProCCompletedGroupAlgebraLimitCarrier C G → ProCCompletedGroupAlgebraStage C G i :=
  fun x => x.1 i

/-- Extensionality through finite group-algebra projections. -/
@[ext]
theorem ProCCompletedGroupAlgebraLimitCarrier.ext {x y : ProCCompletedGroupAlgebraLimitCarrier C G}
    (h : ∀ i : ProCCompletedGroupAlgebraIndex C G,
      proCCompletedGroupAlgebraProj (C := C) (G := G) i x =
        proCCompletedGroupAlgebraProj (C := C) (G := G) i y) :
    x = y :=
  Subtype.ext (funext h)

/-- The zero element of the completed group algebra is defined coordinatewise. -/
instance instZeroProCCompletedGroupAlgebra :
    Zero (ProCCompletedGroupAlgebraLimitCarrier C G) where
  zero := ⟨fun _ => 0, by
    intro i j hij
    exact map_zero (proCCompletedGroupAlgebraTransition (C := C) (G := G) hij)⟩

/-- Addition on the completed group algebra is defined coordinatewise. -/
instance instAddProCCompletedGroupAlgebra :
    Add (ProCCompletedGroupAlgebraLimitCarrier C G) where
  add x y := ⟨fun i => x.1 i + y.1 i, by
    intro i j hij
    rw [map_add]
    exact congrArg₂ HAdd.hAdd (x.2 i j hij) (y.2 i j hij)⟩

/-- Negation on the completed group algebra is defined coordinatewise. -/
instance instNegProCCompletedGroupAlgebra :
    Neg (ProCCompletedGroupAlgebraLimitCarrier C G) where
  neg x := ⟨fun i => -x.1 i, by
    intro i j hij
    rw [map_neg]
    exact congrArg Neg.neg (x.2 i j hij)⟩

/-- Subtraction on the completed group algebra is defined coordinatewise. -/
instance instSubProCCompletedGroupAlgebra :
    Sub (ProCCompletedGroupAlgebraLimitCarrier C G) where
  sub x y := ⟨fun i => x.1 i - y.1 i, by
    intro i j hij
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 i j hij) (y.2 i j hij)⟩

/-- Natural-number scalar multiplication on the completed group algebra is defined
coordinatewise. -/
instance instSMulNatProCCompletedGroupAlgebra :
    SMul ℕ (ProCCompletedGroupAlgebraLimitCarrier C G) where
  smul n x := ⟨fun i => n • x.1 i, by
    intro i j hij
    rw [map_nsmul]
    exact congrArg (n • ·) (x.2 i j hij)⟩

/-- Integer scalar multiplication on the completed group algebra is defined coordinatewise. -/
instance instSMulIntProCCompletedGroupAlgebra :
    SMul ℤ (ProCCompletedGroupAlgebraLimitCarrier C G) where
  smul n x := ⟨fun i => n • x.1 i, by
    intro i j hij
    rw [map_zsmul]
    exact congrArg (n • ·) (x.2 i j hij)⟩

/-- The unit of the completed group algebra is defined coordinatewise. -/
instance instOneProCCompletedGroupAlgebra :
    One (ProCCompletedGroupAlgebraLimitCarrier C G) where
  one := ⟨fun _ => 1, by
    intro i j hij
    exact map_one (proCCompletedGroupAlgebraTransition (C := C) (G := G) hij)⟩

/-- Multiplication on the completed group algebra is defined coordinatewise. -/
instance instMulProCCompletedGroupAlgebra :
    Mul (ProCCompletedGroupAlgebraLimitCarrier C G) where
  mul x y := ⟨fun i => x.1 i * y.1 i, by
    intro i j hij
    rw [map_mul]
    exact congrArg₂ HMul.hMul (x.2 i j hij) (y.2 i j hij)⟩

/-- Natural-number casts into the completed group algebra are defined coordinatewise. -/
instance instNatCastProCCompletedGroupAlgebra :
    NatCast (ProCCompletedGroupAlgebraLimitCarrier C G) where
  natCast n := ⟨fun _ => n, by
    intro i j hij
    exact map_natCast (proCCompletedGroupAlgebraTransition (C := C) (G := G) hij) n⟩

/-- Integer casts into the completed group algebra are defined coordinatewise. -/
instance instIntCastProCCompletedGroupAlgebra :
    IntCast (ProCCompletedGroupAlgebraLimitCarrier C G) where
  intCast n := ⟨fun _ => n, by
    intro i j hij
    exact map_intCast (proCCompletedGroupAlgebraTransition (C := C) (G := G) hij) n⟩

/-- Powers in the completed group algebra are defined coordinatewise. -/
instance instPowProCCompletedGroupAlgebra :
    Pow (ProCCompletedGroupAlgebraLimitCarrier C G) ℕ where
  pow x n := ⟨fun i => x.1 i ^ n, by
    intro i j hij
    rw [map_pow]
    exact congrArg (fun t => t ^ n) (x.2 i j hij)⟩

/-- The underlying compatible family of the completed group algebra computes zero coordinatewise. -/
@[simp]
theorem coe_zero_proCCompletedGroupAlgebra :
    ((0 : ProCCompletedGroupAlgebraLimitCarrier C G) :
      ∀ i : ProCCompletedGroupAlgebraIndex C G,
        ProCCompletedGroupAlgebraStage C G i) = 0 := by
  funext i
  rfl

/-- The underlying compatible family of the completed group algebra computes one coordinatewise. -/
@[simp]
theorem coe_one_proCCompletedGroupAlgebra :
    ((1 : ProCCompletedGroupAlgebraLimitCarrier C G) :
      ∀ i : ProCCompletedGroupAlgebraIndex C G,
        ProCCompletedGroupAlgebraStage C G i) = 1 := by
  funext i
  rfl

/-- The underlying compatible family of the completed group algebra computes addition coordinatewise. -/
@[simp]
theorem coe_add_proCCompletedGroupAlgebra (x y : ProCCompletedGroupAlgebraLimitCarrier C G) :
    ((x + y : ProCCompletedGroupAlgebraLimitCarrier C G) :
      ∀ i : ProCCompletedGroupAlgebraIndex C G,
        ProCCompletedGroupAlgebraStage C G i) = x + y := by
  funext i
  rfl

/-- The underlying compatible family of the completed group algebra computes multiplication coordinatewise. -/
@[simp]
theorem coe_mul_proCCompletedGroupAlgebra (x y : ProCCompletedGroupAlgebraLimitCarrier C G) :
    ((x * y : ProCCompletedGroupAlgebraLimitCarrier C G) :
      ∀ i : ProCCompletedGroupAlgebraIndex C G,
        ProCCompletedGroupAlgebraStage C G i) = x * y := by
  funext i
  rfl

/-- The underlying compatible family of the completed group algebra computes negation coordinatewise. -/
@[simp]
theorem coe_neg_proCCompletedGroupAlgebra (x : ProCCompletedGroupAlgebraLimitCarrier C G) :
    ((-x : ProCCompletedGroupAlgebraLimitCarrier C G) :
      ∀ i : ProCCompletedGroupAlgebraIndex C G,
        ProCCompletedGroupAlgebraStage C G i) = -x := by
  funext i
  rfl

/-- The underlying compatible family of the completed group algebra computes subtraction coordinatewise. -/
@[simp]
theorem coe_sub_proCCompletedGroupAlgebra (x y : ProCCompletedGroupAlgebraLimitCarrier C G) :
    ((x - y : ProCCompletedGroupAlgebraLimitCarrier C G) :
      ∀ i : ProCCompletedGroupAlgebraIndex C G,
        ProCCompletedGroupAlgebraStage C G i) = x - y := by
  funext i
  rfl

/-- The underlying compatible family of the completed group algebra computes natural-number casts coordinatewise. -/
@[simp]
theorem coe_natCast_proCCompletedGroupAlgebra (n : ℕ) :
    ((n : ProCCompletedGroupAlgebraLimitCarrier C G) :
      ∀ i : ProCCompletedGroupAlgebraIndex C G,
        ProCCompletedGroupAlgebraStage C G i) = n := by
  funext i
  rfl

/-- The underlying compatible family of the completed group algebra computes integer casts coordinatewise. -/
@[simp]
theorem coe_intCast_proCCompletedGroupAlgebra (n : ℤ) :
    ((n : ProCCompletedGroupAlgebraLimitCarrier C G) :
      ∀ i : ProCCompletedGroupAlgebraIndex C G,
        ProCCompletedGroupAlgebraStage C G i) =
      fun i => (n : ProCCompletedGroupAlgebraStage C G i) := by
  funext i
  rfl

/-- The underlying compatible family of the completed group algebra computes powers coordinatewise. -/
@[simp]
theorem coe_pow_proCCompletedGroupAlgebra (x : ProCCompletedGroupAlgebraLimitCarrier C G) (n : ℕ) :
    ((x ^ n : ProCCompletedGroupAlgebraLimitCarrier C G) :
      ∀ i : ProCCompletedGroupAlgebraIndex C G,
        ProCCompletedGroupAlgebraStage C G i) = x ^ n := by
  funext i
  rfl

/-- The completed group algebra is a ring by coordinatewise operations on finite stages. -/
instance instRingProCCompletedGroupAlgebra : Ring (ProCCompletedGroupAlgebraLimitCarrier C G) :=
  Function.Injective.ring
    (fun x : ProCCompletedGroupAlgebraLimitCarrier C G =>
      (x : ∀ i : ProCCompletedGroupAlgebraIndex C G,
        ProCCompletedGroupAlgebraStage C G i))
    Subtype.val_injective
    (coe_zero_proCCompletedGroupAlgebra (C := C) (G := G))
    (coe_one_proCCompletedGroupAlgebra (C := C) (G := G))
    (coe_add_proCCompletedGroupAlgebra (C := C) (G := G))
    (coe_mul_proCCompletedGroupAlgebra (C := C) (G := G))
    (coe_neg_proCCompletedGroupAlgebra (C := C) (G := G))
    (coe_sub_proCCompletedGroupAlgebra (C := C) (G := G))
    (by intro n x; funext i; change (n • x).1 i = n • x.1 i; rfl)
    (by intro n x; funext i; change (n • x).1 i = n • x.1 i; rfl)
    (coe_pow_proCCompletedGroupAlgebra (C := C) (G := G))
    (coe_natCast_proCCompletedGroupAlgebra (C := C) (G := G))
    (coe_intCast_proCCompletedGroupAlgebra (C := C) (G := G))

/-- Finite group-algebra projections commute with `0`. -/
@[simp]
theorem proCCompletedGroupAlgebraProj_zero
    (i : ProCCompletedGroupAlgebraIndex C G) :
    proCCompletedGroupAlgebraProj (C := C) (G := G) i
      (0 : ProCCompletedGroupAlgebraLimitCarrier C G) = 0 :=
  by rfl

/-- Finite group-algebra projections commute with `1`. -/
@[simp]
theorem proCCompletedGroupAlgebraProj_one
    (i : ProCCompletedGroupAlgebraIndex C G) :
    proCCompletedGroupAlgebraProj (C := C) (G := G) i
      (1 : ProCCompletedGroupAlgebraLimitCarrier C G) = 1 :=
  by rfl

/-- Finite group-algebra projections commute with addition. -/
@[simp]
theorem proCCompletedGroupAlgebraProj_add
    (i : ProCCompletedGroupAlgebraIndex C G) (x y : ProCCompletedGroupAlgebraLimitCarrier C G) :
    proCCompletedGroupAlgebraProj (C := C) (G := G) i (x + y) =
      proCCompletedGroupAlgebraProj (C := C) (G := G) i x +
        proCCompletedGroupAlgebraProj (C := C) (G := G) i y :=
  by rfl

/-- Finite group-algebra projections commute with multiplication. -/
@[simp]
theorem proCCompletedGroupAlgebraProj_mul
    (i : ProCCompletedGroupAlgebraIndex C G) (x y : ProCCompletedGroupAlgebraLimitCarrier C G) :
    proCCompletedGroupAlgebraProj (C := C) (G := G) i (x * y) =
      proCCompletedGroupAlgebraProj (C := C) (G := G) i x *
        proCCompletedGroupAlgebraProj (C := C) (G := G) i y :=
  by rfl

/-- Finite group-algebra projections commute with negation. -/
@[simp]
theorem proCCompletedGroupAlgebraProj_neg
    (i : ProCCompletedGroupAlgebraIndex C G) (x : ProCCompletedGroupAlgebraLimitCarrier C G) :
    proCCompletedGroupAlgebraProj (C := C) (G := G) i (-x) =
      -proCCompletedGroupAlgebraProj (C := C) (G := G) i x :=
  by rfl

/-- Finite group-algebra projections commute with subtraction. -/
@[simp]
theorem proCCompletedGroupAlgebraProj_sub
    (i : ProCCompletedGroupAlgebraIndex C G) (x y : ProCCompletedGroupAlgebraLimitCarrier C G) :
    proCCompletedGroupAlgebraProj (C := C) (G := G) i (x - y) =
      proCCompletedGroupAlgebraProj (C := C) (G := G) i x -
        proCCompletedGroupAlgebraProj (C := C) (G := G) i y :=
  by rfl

/-- Projection from the completed group algebra to a finite group-algebra stage as a ring homomorphism. -/
def proCCompletedGroupAlgebraProjRingHom
    (i : ProCCompletedGroupAlgebraIndex C G) :
    ProCCompletedGroupAlgebraLimitCarrier C G →+* ProCCompletedGroupAlgebraStage C G i where
  toFun := proCCompletedGroupAlgebraProj (C := C) (G := G) i
  map_zero' := by simp only [proCCompletedGroupAlgebraProj_zero]
  map_one' := by simp only [proCCompletedGroupAlgebraProj_one]
  map_add' := by intro x y; simp only [proCCompletedGroupAlgebraProj_add]
  map_mul' := by intro x y; simp only [proCCompletedGroupAlgebraProj_mul]

/-- The ring-hom version of a completed group-algebra projection evaluates to the projection map. -/
@[simp]
theorem proCCompletedGroupAlgebraProjRingHom_apply
    (i : ProCCompletedGroupAlgebraIndex C G) (x : ProCCompletedGroupAlgebraLimitCarrier C G) :
    proCCompletedGroupAlgebraProjRingHom (C := C) (G := G) i x =
      proCCompletedGroupAlgebraProj (C := C) (G := G) i x :=
  rfl

/-- Each finite projection from the completed group algebra is continuous. -/
theorem continuous_proCCompletedGroupAlgebraProj
    (i : ProCCompletedGroupAlgebraIndex C G) :
    Continuous (proCCompletedGroupAlgebraProj (C := C) (G := G) i) :=
  (continuous_apply i).comp continuous_subtype_val

/-- Compatibility of the finite projections with completed group-algebra transition maps. -/
theorem proCCompletedGroupAlgebraProj_transition
    {i j : ProCCompletedGroupAlgebraIndex C G} (hij : i ≤ j)
    (x : ProCCompletedGroupAlgebraLimitCarrier C G) :
    proCCompletedGroupAlgebraTransition (C := C) (G := G) hij
        (proCCompletedGroupAlgebraProj (C := C) (G := G) j x) =
      proCCompletedGroupAlgebraProj (C := C) (G := G) i x :=
  x.2 i j hij

/-- The compatibility condition defining the completed group algebra is closed in the product of
finite stages. -/
theorem isClosed_setOf_completedGroupAlgebraCompatible :
    IsClosed {x : ∀ i : ProCCompletedGroupAlgebraIndex C G,
        ProCCompletedGroupAlgebraStage C G i |
      ProCCompletedGroupAlgebraCompatible C G x} := by
  simp only [ProCCompletedGroupAlgebraCompatible, Set.setOf_forall]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun hij => ?_
  have hleft :
      Continuous fun x : (∀ k : ProCCompletedGroupAlgebraIndex C G,
          ProCCompletedGroupAlgebraStage C G k) =>
        proCCompletedGroupAlgebraTransition (C := C) (G := G) hij (x j) := by
    exact (continuous_of_discreteTopology :
      Continuous (proCCompletedGroupAlgebraTransition (C := C) (G := G) hij)).comp
        (continuous_apply j)
  exact isClosed_eq hleft (continuous_apply i)

/-- The completed group-algebra limit carrier is compact as a closed subspace of a product of
finite discrete stages. -/
instance instCompactSpaceProCCompletedGroupAlgebraLimitCarrier :
    CompactSpace (ProCCompletedGroupAlgebraLimitCarrier C G) := by
  letI : ∀ i : ProCCompletedGroupAlgebraIndex C G,
      CompactSpace (ProCCompletedGroupAlgebraStage C G i) := fun _ => inferInstance
  let hs : IsClosed {x : ∀ i : ProCCompletedGroupAlgebraIndex C G,
      ProCCompletedGroupAlgebraStage C G i |
      ProCCompletedGroupAlgebraCompatible C G x} :=
    isClosed_setOf_completedGroupAlgebraCompatible (C := C) (G := G)
  simpa [ProCCompletedGroupAlgebraLimitCarrier] using hs.isClosedEmbedding_subtypeVal.compactSpace

/-- The completed group-algebra limit carrier is Hausdorff. -/
instance instT2SpaceProCCompletedGroupAlgebraLimitCarrier :
    T2Space (ProCCompletedGroupAlgebraLimitCarrier C G) := by
  change T2Space {x : ∀ i : ProCCompletedGroupAlgebraIndex C G,
      ProCCompletedGroupAlgebraStage C G i //
      ProCCompletedGroupAlgebraCompatible C G x}
  infer_instance

/-- Addition on the completed group-algebra limit carrier is continuous coordinatewise. -/
instance instContinuousAddProCCompletedGroupAlgebraLimitCarrier :
    ContinuousAdd (ProCCompletedGroupAlgebraLimitCarrier C G) where
  continuous_add := by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) (fun p => (p.1 + p.2).2)
    change Continuous fun p : ProCCompletedGroupAlgebraLimitCarrier C G ×
        ProCCompletedGroupAlgebraLimitCarrier C G =>
      proCCompletedGroupAlgebraProj (C := C) (G := G) i p.1 +
        proCCompletedGroupAlgebraProj (C := C) (G := G) i p.2
    exact ((continuous_proCCompletedGroupAlgebraProj (C := C) (G := G) i).comp
        continuous_fst).add
      ((continuous_proCCompletedGroupAlgebraProj (C := C) (G := G) i).comp continuous_snd)

/-- Multiplication on the completed group-algebra limit carrier is continuous coordinatewise. -/
instance instContinuousMulProCCompletedGroupAlgebraLimitCarrier :
    ContinuousMul (ProCCompletedGroupAlgebraLimitCarrier C G) where
  continuous_mul := by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) (fun p => (p.1 * p.2).2)
    change Continuous fun p : ProCCompletedGroupAlgebraLimitCarrier C G ×
        ProCCompletedGroupAlgebraLimitCarrier C G =>
      proCCompletedGroupAlgebraProj (C := C) (G := G) i p.1 *
        proCCompletedGroupAlgebraProj (C := C) (G := G) i p.2
    exact ((continuous_proCCompletedGroupAlgebraProj (C := C) (G := G) i).comp
        continuous_fst).mul
      ((continuous_proCCompletedGroupAlgebraProj (C := C) (G := G) i).comp continuous_snd)

/-- Negation on the completed group-algebra limit carrier is continuous coordinatewise. -/
instance instContinuousNegProCCompletedGroupAlgebraLimitCarrier :
    ContinuousNeg (ProCCompletedGroupAlgebraLimitCarrier C G) where
  continuous_neg := by
    refine Continuous.subtype_mk (continuous_pi fun i => ?_) (fun x => (-x).2)
    change Continuous fun x : ProCCompletedGroupAlgebraLimitCarrier C G =>
      -proCCompletedGroupAlgebraProj (C := C) (G := G) i x
    exact (continuous_proCCompletedGroupAlgebraProj (C := C) (G := G) i).neg

/-- The completed group-algebra limit carrier is a topological ring. -/
instance ProCCompletedGroupAlgebraLimitCarrier.instIsTopologicalRing :
    IsTopologicalRing (ProCCompletedGroupAlgebraLimitCarrier C G) := by
  letI : ContinuousAdd (ProCCompletedGroupAlgebraLimitCarrier C G) :=
    instContinuousAddProCCompletedGroupAlgebraLimitCarrier (C := C) (G := G)
  letI : ContinuousMul (ProCCompletedGroupAlgebraLimitCarrier C G) :=
    instContinuousMulProCCompletedGroupAlgebraLimitCarrier (C := C) (G := G)
  letI : ContinuousNeg (ProCCompletedGroupAlgebraLimitCarrier C G) :=
    instContinuousNegProCCompletedGroupAlgebraLimitCarrier (C := C) (G := G)
  letI : IsTopologicalSemiring (ProCCompletedGroupAlgebraLimitCarrier C G) :=
    IsTopologicalSemiring.mk
  exact IsTopologicalRing.mk

/-- The coefficient embedding into the completed group algebra. -/
def proCIntegerToProCCompletedGroupAlgebra :
    ProCIntegerLimitCarrier C →+* ProCCompletedGroupAlgebraLimitCarrier C G where
  toFun z := ⟨fun i =>
      algebraMap (ProCIntegerStage C i.1) (ProCCompletedGroupAlgebraStage C G i)
        (proCIntegerProj (C := C) i.1 z), by
    intro i j hij
    simp only [proCCompletedGroupAlgebraTransition, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, RingHom.coe_comp, MonoidAlgebra.mapRangeRingHom_single,
  proCIntegerProj_transition (C := C) hij.1 z, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single,
  map_one]⟩
  map_zero' := by
    apply ProCCompletedGroupAlgebraLimitCarrier.ext
    intro i
    exact map_zero (algebraMap (ProCIntegerStage C i.1)
      (ProCCompletedGroupAlgebraStage C G i))
  map_one' := by
    apply ProCCompletedGroupAlgebraLimitCarrier.ext
    intro i
    exact map_one (algebraMap (ProCIntegerStage C i.1)
      (ProCCompletedGroupAlgebraStage C G i))
  map_add' := by
    intro x y
    apply ProCCompletedGroupAlgebraLimitCarrier.ext
    intro i
    exact map_add (algebraMap (ProCIntegerStage C i.1)
      (ProCCompletedGroupAlgebraStage C G i))
      (proCIntegerProj (C := C) i.1 x) (proCIntegerProj (C := C) i.1 y)
  map_mul' := by
    intro x y
    apply ProCCompletedGroupAlgebraLimitCarrier.ext
    intro i
    exact map_mul (algebraMap (ProCIntegerStage C i.1)
      (ProCCompletedGroupAlgebraStage C G i))
      (proCIntegerProj (C := C) i.1 x) (proCIntegerProj (C := C) i.1 y)

/-- Projecting the coefficient embedding into the completed group algebra applies the stage algebra map. -/
@[simp]
theorem proCCompletedGroupAlgebraProj_proCIntegerToProCCompletedGroupAlgebra
    (i : ProCCompletedGroupAlgebraIndex C G) (z : ProCIntegerLimitCarrier C) :
    proCCompletedGroupAlgebraProj (C := C) (G := G) i
        (proCIntegerToProCCompletedGroupAlgebra (C := C) (G := G) z) =
      algebraMap (ProCIntegerStage C i.1) (ProCCompletedGroupAlgebraStage C G i)
        (proCIntegerProj (C := C) i.1 z) :=
  rfl

/-- The completed group-algebra limit carrier is an algebra over its pro-`C` coefficient ring. -/
instance instAlgebraProCIntegerLimitCarrierProCCompletedGroupAlgebraLimitCarrier :
    Algebra (ProCIntegerLimitCarrier C) (ProCCompletedGroupAlgebraLimitCarrier C G) :=
  RingHom.toAlgebra'
    (proCIntegerToProCCompletedGroupAlgebra (C := C) (G := G))
    (by
      intro z x
      apply ProCCompletedGroupAlgebraLimitCarrier.ext
      intro i
      change
        algebraMap (ProCIntegerStage C i.1) (ProCCompletedGroupAlgebraStage C G i)
            (proCIntegerProj (C := C) i.1 z) *
          proCCompletedGroupAlgebraProj (C := C) (G := G) i x =
        proCCompletedGroupAlgebraProj (C := C) (G := G) i x *
          algebraMap (ProCIntegerStage C i.1) (ProCCompletedGroupAlgebraStage C G i)
            (proCIntegerProj (C := C) i.1 z)
      exact Algebra.commutes _ _)

/-- The canonical group map into the completed group algebra, sending `g` to its compatible system of group
basis elements. -/
def proCCompletedGroupAlgebraOf : G →* ProCCompletedGroupAlgebraLimitCarrier C G where
  toFun g := ⟨fun i =>
      MonoidAlgebra.of (ProCIntegerStage C i.1)
        (ProCCompletedGroupAlgebraQuotient C G i.2)
        (ProC.openNormalSubgroupInClassProj (C := C) (G := G) i.2 g), by
    intro i j hij
    have hq :=
      congrFun (ProC.openNormalSubgroupInClassProj_compatible
        (C := C) (G := G) i.2 j.2 hij.2) g
    simpa [proCCompletedGroupAlgebraTransition,
      proCCompletedGroupAlgebraQuotientTransition] using
      congrArg (fun q =>
        MonoidAlgebra.of (ProCIntegerStage C i.1)
          (ProCCompletedGroupAlgebraQuotient C G i.2) q) hq⟩
  map_one' := by
    apply ProCCompletedGroupAlgebraLimitCarrier.ext
    intro i
    change
      MonoidAlgebra.of (ProCIntegerStage C i.1)
          (ProCCompletedGroupAlgebraQuotient C G i.2)
          (ProC.openNormalSubgroupInClassProj (C := C) (G := G) i.2 1) =
        1
    rfl
  map_mul' g h := by
    apply ProCCompletedGroupAlgebraLimitCarrier.ext
    intro i
    change
      MonoidAlgebra.of (ProCIntegerStage C i.1)
          (ProCCompletedGroupAlgebraQuotient C G i.2)
          (ProC.openNormalSubgroupInClassProj (C := C) (G := G) i.2 (g * h)) =
        MonoidAlgebra.of (ProCIntegerStage C i.1)
            (ProCCompletedGroupAlgebraQuotient C G i.2)
            (ProC.openNormalSubgroupInClassProj (C := C) (G := G) i.2 g) *
          MonoidAlgebra.of (ProCIntegerStage C i.1)
            (ProCCompletedGroupAlgebraQuotient C G i.2)
            (ProC.openNormalSubgroupInClassProj (C := C) (G := G) i.2 h)
    simp only [ProC.openNormalSubgroupInClassProj, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
  MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one]

/-- Projecting a group element into the completed group algebra gives the corresponding finite basis element. -/
@[simp]
theorem proCCompletedGroupAlgebraProj_of
    (i : ProCCompletedGroupAlgebraIndex C G) (g : G) :
    proCCompletedGroupAlgebraProj (C := C) (G := G) i
        (proCCompletedGroupAlgebraOf (C := C) (G := G) g) =
      MonoidAlgebra.of (ProCIntegerStage C i.1)
        (ProCCompletedGroupAlgebraQuotient C G i.2)
        (ProC.openNormalSubgroupInClassProj (C := C) (G := G) i.2 g) :=
  rfl

/-- A group element gives a unit in the completed group-algebra limit carrier. -/
def groupBasisUnit (g : G) : (ProCCompletedGroupAlgebraLimitCarrier C G)ˣ where
  val := proCCompletedGroupAlgebraOf (C := C) (G := G) g
  inv := proCCompletedGroupAlgebraOf (C := C) (G := G) g⁻¹
  val_inv := by
    rw [← map_mul]
    simp only [mul_inv_cancel, map_one]
  inv_val := by
    rw [← map_mul]
    simp only [inv_mul_cancel, map_one]

/-- The canonical map from `G` to units in the completed group-algebra limit carrier. -/
def ProCCompletedGroupAlgebraModel.groupToUnits : G →* (ProCCompletedGroupAlgebraLimitCarrier C G)ˣ where
  toFun := groupBasisUnit (C := C) (G := G)
  map_one' := by
    ext
    simp only [groupBasisUnit, map_one, inv_one, proCCompletedGroupAlgebraProj_one, Units.val_one]
  map_mul' g h := by
    ext
    simp only [groupBasisUnit, map_mul, mul_inv_rev, proCCompletedGroupAlgebraProj_mul,
  proCCompletedGroupAlgebraProj_of, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one, Units.val_mul]

namespace ProCCompletedGroupAlgebraModel

/-- Compatible maps into the finite stages lift to the completed group-algebra limit carrier. -/
def lift
    {R : Type v} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (f : ∀ i : ProCCompletedGroupAlgebraIndex C G,
      R →+* ProCCompletedGroupAlgebraStage C G i)
    (hf_compat : ∀ i j (hij : i ≤ j),
      (proCCompletedGroupAlgebraTransition (C := C) (G := G) hij).comp (f j) = f i) :
    R →+* ProCCompletedGroupAlgebraLimitCarrier C G where
  toFun r := ⟨fun i => f i r, by
    intro i j hij
    exact congrArg (fun φ : R →+* ProCCompletedGroupAlgebraStage C G i => φ r)
      (hf_compat i j hij)⟩
  map_zero' := by
    apply ProCCompletedGroupAlgebraLimitCarrier.ext
    intro i
    exact map_zero (f i)
  map_one' := by
    apply ProCCompletedGroupAlgebraLimitCarrier.ext
    intro i
    exact map_one (f i)
  map_add' := by
    intro x y
    apply ProCCompletedGroupAlgebraLimitCarrier.ext
    intro i
    exact map_add (f i) x y
  map_mul' := by
    intro x y
    apply ProCCompletedGroupAlgebraLimitCarrier.ext
    intro i
    exact map_mul (f i) x y

end ProCCompletedGroupAlgebraModel

/-- The inverse-limit carrier bundled as a completed group-algebra object. -/
def proCCompletedGroupAlgebraModel :
    ProCCompletedGroupAlgebraModel C G where
  carrier := ProCCompletedGroupAlgebraLimitCarrier C G
  ring := inferInstance
  topology := inferInstance
  topologicalRing := inferInstance
  compact := inferInstance
  t2 := inferInstance
  coeff := proCIntegerToProCCompletedGroupAlgebra (C := C) (G := G)
  groupMap := ProCCompletedGroupAlgebraModel.groupToUnits (C := C) (G := G)

end

end ProCGroups.Completion
