import FenchelNielsenZomorrodian.Discrete.Coordinates.FenchelPeriodCoordinate
import FenchelNielsenZomorrodian.Discrete.GroupTheory.DerivedSeries
import FenchelNielsenZomorrodian.Profinite.SmoothQuotient
import Mathlib.GroupTheory.SemidirectProduct

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Profinite/PositiveGenusQuotient.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Positive-genus smooth quotients

Builds finite quotients of derived length at most two in positive genus by assigning surface and inertia generators to a finite solvable target.
-/

namespace FenchelNielsen

universe u

namespace ProfiniteFGroup

abbrev PositiveGenusSmoothBase (σ : FenchelSignature) :=
  Multiplicative (FenchelPeriodCoordinate σ × FenchelPeriodCoordinate σ)

noncomputable def positiveGenusSmoothSwap
    (σ : FenchelSignature) :
    MulAut (PositiveGenusSmoothBase σ) where
  toFun x :=
    Multiplicative.ofAdd
      ((Multiplicative.toAdd x).2, (Multiplicative.toAdd x).1)
  invFun x :=
    Multiplicative.ofAdd
      ((Multiplicative.toAdd x).2, (Multiplicative.toAdd x).1)
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    cases x
    rfl
  map_mul' := by
    intro x y
    cases x
    cases y
    rfl

theorem zmod_two_eq_zero_or_one (z : ZMod 2) :
    z = 0 ∨ z = 1 := by
  have hzlt : z.val < 2 := ZMod.val_lt z
  have hval : z.val = 0 ∨ z.val = 1 := by omega
  rcases hval with h | h
  · left
    rw [← ZMod.natCast_zmod_val z, h]
    norm_num
  · right
    rw [← ZMod.natCast_zmod_val z, h]
    norm_num

noncomputable def positiveGenusSmoothAction
    (σ : FenchelSignature) :
    Multiplicative (ZMod 2) →* MulAut (PositiveGenusSmoothBase σ) where
  toFun t :=
    if Multiplicative.toAdd t = (0 : ZMod 2) then
      1
    else
      positiveGenusSmoothSwap σ
  map_one' := by simp only [toAdd_one, ↓reduceIte]
  map_mul' := by
    intro a b
    have ha := zmod_two_eq_zero_or_one (Multiplicative.toAdd a)
    have hb := zmod_two_eq_zero_or_one (Multiplicative.toAdd b)
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · ext x : 1
      cases x
      simp only [toAdd_mul, ha, hb, add_zero, ↓reduceIte, MulAut.one_apply, mul_one]
    · ext x : 1
      cases x
      simp only [toAdd_mul, ha, hb, zero_add, one_ne_zero, ↓reduceIte, positiveGenusSmoothSwap, MulEquiv.coe_mk,
  Equiv.coe_fn_mk, one_mul]
    · ext x : 1
      cases x
      simp only [toAdd_mul, ha, hb, add_zero, one_ne_zero, ↓reduceIte, positiveGenusSmoothSwap, MulEquiv.coe_mk,
  Equiv.coe_fn_mk, mul_one]
    · have hsum : (1 : ZMod 2) + 1 = 0 := by
        simpa using (ZMod.natCast_self 2)
      ext x : 1
      cases x
      simp only [toAdd_mul, ha, hb, hsum, ↓reduceIte, MulAut.one_apply, one_ne_zero, positiveGenusSmoothSwap,
  MulAut.mul_apply, MulEquiv.coe_mk, Equiv.coe_fn_mk, toAdd_ofAdd, Prod.mk.eta, ofAdd_toAdd]

abbrev PositiveGenusSmoothQuotient (σ : FenchelSignature) :=
  PositiveGenusSmoothBase σ ⋊[positiveGenusSmoothAction σ]
    Multiplicative (ZMod 2)

instance instTopologicalSpacePositiveGenusSmoothQuotient (σ : FenchelSignature) :
    TopologicalSpace (PositiveGenusSmoothQuotient σ) :=
  ⊥

instance instDiscreteTopologyPositiveGenusSmoothQuotient (σ : FenchelSignature) :
    DiscreteTopology (PositiveGenusSmoothQuotient σ) :=
  ⟨rfl⟩

/-- The base-coordinate value assigned to a positive-genus inertia generator. -/
def positiveGenusSmoothEllipticBase
    (σ : FenchelSignature) (i : Fin σ.numPeriods) :
    PositiveGenusSmoothBase σ :=
  Multiplicative.ofAdd
    (fenchelPeriodBasisVector σ i, -fenchelPeriodBasisVector σ i)

/-- The sum of the period-coordinate basis vectors. -/
def positiveGenusSmoothSumBasis
    (σ : FenchelSignature) :
    FenchelPeriodCoordinate σ :=
  ∑ i : Fin σ.numPeriods, fenchelPeriodBasisVector σ i

/-- The product of the base-coordinate values assigned to all inertia generators. -/
def positiveGenusSmoothEllipticProductBase
    (σ : FenchelSignature) :
    PositiveGenusSmoothBase σ :=
  Multiplicative.ofAdd
    (positiveGenusSmoothSumBasis σ,
      -positiveGenusSmoothSumBasis σ)

/-- The base-coordinate value used for the first positive-genus surface generator. -/
def positiveGenusSmoothSurfaceBase
    (σ : FenchelSignature) :
    PositiveGenusSmoothBase σ :=
  Multiplicative.ofAdd (0, positiveGenusSmoothSumBasis σ)

/-- The nontrivial top-coordinate generator of the positive-genus quotient. -/
def positiveGenusSmoothTopGenerator :
    Multiplicative (ZMod 2) :=
  Multiplicative.ofAdd (1 : ZMod 2)

/-- Each positive-genus inertia base value has exponent dividing its period. -/
theorem positiveGenusSmoothEllipticBase_pow_period
    (σ : FenchelSignature) (i : Fin σ.numPeriods) :
    positiveGenusSmoothEllipticBase σ i ^ σ.periods i = 1 := by
  rw [positiveGenusSmoothEllipticBase, ← ofAdd_nsmul]
  apply congrArg Multiplicative.ofAdd
  ext j
  · by_cases hji : j = i
    · subst hji
      simp only [fenchelPeriodBasisVector, zmodBasisVector, Prod.smul_mk, nsmul_eq_mul, smul_neg, Pi.mul_apply,
  Pi.natCast_apply, CharP.cast_eq_zero, Pi.single_eq_same, mul_one, Prod.fst_zero, Pi.zero_apply]
    · simp only [fenchelPeriodBasisVector, zmodBasisVector, Prod.smul_mk, nsmul_eq_mul, smul_neg, Pi.mul_apply,
  Pi.natCast_apply, ne_eq, hji, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, Prod.fst_zero, Pi.zero_apply]
  · by_cases hji : j = i
    · subst hji
      simp only [fenchelPeriodBasisVector, zmodBasisVector, Prod.smul_mk, nsmul_eq_mul, smul_neg, Pi.neg_apply,
  Pi.mul_apply, Pi.natCast_apply, CharP.cast_eq_zero, Pi.single_eq_same, mul_one, neg_zero, Prod.snd_zero,
  Pi.zero_apply]
    · simp only [fenchelPeriodBasisVector, zmodBasisVector, Prod.smul_mk, nsmul_eq_mul, smul_neg, Pi.neg_apply,
  Pi.mul_apply, Pi.natCast_apply, ne_eq, hji, not_false_eq_true, Pi.single_eq_of_ne, mul_zero, neg_zero,
  Prod.snd_zero, Pi.zero_apply]

/-- The named elliptic product base is the product of the individual inertia base values. -/
theorem positiveGenusSmoothEllipticProductBase_eq_prod
    (σ : FenchelSignature) :
    (∏ i : Fin σ.numPeriods, positiveGenusSmoothEllipticBase σ i) =
      positiveGenusSmoothEllipticProductBase σ := by
  calc
    (∏ i : Fin σ.numPeriods, positiveGenusSmoothEllipticBase σ i)
        =
          Multiplicative.ofAdd
            (∑ i : Fin σ.numPeriods,
              (fenchelPeriodBasisVector σ i, -fenchelPeriodBasisVector σ i)) := by
          simp only [positiveGenusSmoothEllipticBase, ofAdd_sum]
    _ = positiveGenusSmoothEllipticProductBase σ := by
          apply Multiplicative.ofAdd.injective
          ext j <;>
          simp only [ofAdd_sum, toAdd_ofAdd, toAdd_prod, Prod.fst_sum, Prod.snd_sum,
            Finset.sum_apply, Pi.neg_apply, Finset.sum_neg_distrib,
            positiveGenusSmoothEllipticProductBase, positiveGenusSmoothSumBasis]

private theorem list_finRange_prod_eq_single_zeroVal
    {G : Type*} [Monoid G] {n : ℕ} (h : 1 ≤ n) (c : G) :
    ((List.finRange n).map
      (fun j : Fin n => if j.val = 0 then c else 1)).prod = c := by
  cases hn : n with
  | zero => omega
  | succ k =>
      rw [List.finRange_succ]
      simp only [List.map_cons, List.prod_cons]
      simp only [Fin.val_zero, ↓reduceIte]
      have htail' :
          (List.map
            (fun j : Fin (k + 1) => if j.val = 0 then c else 1)
            (List.map Fin.succ (List.finRange k))).prod = 1 := by
        simp only [Fin.val_eq_zero_iff, List.map_map, Function.comp_def, Fin.succ_ne_zero, ↓reduceIte,
  List.map_const', List.length_finRange, List.prod_replicate, one_pow]
      rw [htail', mul_one]

/-- The elliptic product cancels the chosen surface commutator in the positive-genus quotient. -/
theorem positiveGenusSmoothEllipticProduct_mul_surfaceCommutator
    (σ : FenchelSignature) :
    (SemidirectProduct.inl (positiveGenusSmoothEllipticProductBase σ) :
        PositiveGenusSmoothQuotient σ) *
      ⁅(SemidirectProduct.inl (positiveGenusSmoothSurfaceBase σ) :
          PositiveGenusSmoothQuotient σ),
        SemidirectProduct.inr positiveGenusSmoothTopGenerator⁆ =
      1 := by
  ext <;>
    simp only [positiveGenusSmoothAction, toAdd_eq_zero, positiveGenusSmoothSwap,
      positiveGenusSmoothEllipticProductBase, positiveGenusSmoothSumBasis,
      positiveGenusSmoothSurfaceBase, positiveGenusSmoothTopGenerator, commutatorElement_def,
      SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.left_inl,
      SemidirectProduct.left_inr, SemidirectProduct.right_inl, SemidirectProduct.right_inr,
      one_mul, SemidirectProduct.inv_left, SemidirectProduct.inv_right, inv_one, mul_one,
      mul_inv_cancel, toAdd_one, SemidirectProduct.one_left, SemidirectProduct.one_right,
      ofAdd_eq_one, inv_eq_one, one_ne_zero, ↓reduceIte, MulAut.one_apply, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_mul, toAdd_inv, toAdd_ofAdd,
      Prod.fst_add, Prod.snd_add, Prod.fst_neg, Prod.snd_neg, Prod.fst_zero, Prod.snd_zero,
      Pi.add_apply, Pi.neg_apply, Pi.zero_apply, Finset.sum_apply, neg_zero, add_assoc,
      neg_add_cancel, add_neg_cancel, zero_add, add_zero]

noncomputable def positiveGenusGeneratorImageCore
    (Δ : ProfiniteFGroup.{u}) :
    ProfiniteFenchelGeneratorIndex.{u} Δ.signature →
      PositiveGenusSmoothQuotient Δ.signature
  | ULift.up (.inertia i) =>
      SemidirectProduct.inl
        (positiveGenusSmoothEllipticBase Δ.signature i)
  | ULift.up (.surfaceA j) =>
      if j.val = 0 then
        SemidirectProduct.inl
          (positiveGenusSmoothSurfaceBase Δ.signature)
      else
        1
  | ULift.up (.surfaceB j) =>
      if j.val = 0 then
        SemidirectProduct.inr positiveGenusSmoothTopGenerator
      else
        1
  | ULift.up (.cusp _) => 1

noncomputable def positiveGenusGeneratorImage
    (Δ : ProfiniteFGroup.{u}) :
    ProfiniteFenchelGeneratorIndex.{u} Δ.signature →
      ULift.{u, 0} (PositiveGenusSmoothQuotient Δ.signature) :=
  fun x => ULift.up (positiveGenusGeneratorImageCore Δ x)

private theorem positiveGenus_inertia_list_product
    (σ : FenchelSignature) :
    ((List.finRange σ.numPeriods).map fun i =>
        (SemidirectProduct.inl (positiveGenusSmoothEllipticBase σ i) :
          PositiveGenusSmoothQuotient σ)).prod =
      (SemidirectProduct.inl
        (positiveGenusSmoothEllipticProductBase σ) :
          PositiveGenusSmoothQuotient σ) := by
  calc
    (List.map
        (fun i : Fin σ.numPeriods =>
          (SemidirectProduct.inl (positiveGenusSmoothEllipticBase σ i) :
            PositiveGenusSmoothQuotient σ))
        (List.finRange σ.numPeriods)).prod
        =
      SemidirectProduct.inl
        ((List.map
          (fun i : Fin σ.numPeriods =>
            positiveGenusSmoothEllipticBase σ i)
          (List.finRange σ.numPeriods)).prod) := by
        simpa [List.map_map] using
          (map_list_prod
            (SemidirectProduct.inl :
              PositiveGenusSmoothBase σ →*
                PositiveGenusSmoothQuotient σ)
            (List.map
              (fun i : Fin σ.numPeriods =>
                positiveGenusSmoothEllipticBase σ i)
              (List.finRange σ.numPeriods))).symm
    _ =
      SemidirectProduct.inl
        (∏ i : Fin σ.numPeriods,
          positiveGenusSmoothEllipticBase σ i) := by
        exact congrArg SemidirectProduct.inl
          ((Fin.prod_univ_def
            (f := fun i : Fin σ.numPeriods =>
              positiveGenusSmoothEllipticBase σ i)).symm)
    _ =
      SemidirectProduct.inl
        (positiveGenusSmoothEllipticProductBase σ) := by
        rw [positiveGenusSmoothEllipticProductBase_eq_prod]

private theorem positiveGenusGeneratorImage_total_relation
    (Δ : ProfiniteFGroup.{u}) (hGenus : 1 ≤ Δ.signature.orbitGenus) :
    profiniteFenchelTotalRelation
        (fun i => positiveGenusGeneratorImageCore Δ
          (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
        (fun i => positiveGenusGeneratorImageCore Δ
          (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
        (fun j => positiveGenusGeneratorImageCore Δ
          (ULift.up (ProfiniteFenchelGenerator.cusp j)))
        (fun k => positiveGenusGeneratorImageCore Δ
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) = 1 := by
  let e : PositiveGenusSmoothQuotient Δ.signature :=
    ((List.finRange Δ.signature.numPeriods).map fun i =>
      positiveGenusGeneratorImageCore Δ
        (ULift.up (ProfiniteFenchelGenerator.inertia i))).prod
  let c : PositiveGenusSmoothQuotient Δ.signature :=
    ((List.finRange Δ.signature.orbitGenus).map fun j =>
      ⁅positiveGenusGeneratorImageCore Δ
          (ULift.up (ProfiniteFenchelGenerator.surfaceA j)),
        positiveGenusGeneratorImageCore Δ
          (ULift.up (ProfiniteFenchelGenerator.surfaceB j))⁆).prod
  have he :
      e =
        (SemidirectProduct.inl
          (positiveGenusSmoothEllipticProductBase Δ.signature) :
          PositiveGenusSmoothQuotient Δ.signature) := by
    simpa [e, positiveGenusGeneratorImageCore] using
      positiveGenus_inertia_list_product Δ.signature
  have hc :
      c =
        ⁅(SemidirectProduct.inl
            (positiveGenusSmoothSurfaceBase Δ.signature) :
            PositiveGenusSmoothQuotient Δ.signature),
          SemidirectProduct.inr positiveGenusSmoothTopGenerator⁆ := by
    let c0 : PositiveGenusSmoothQuotient Δ.signature :=
      ⁅(SemidirectProduct.inl
          (positiveGenusSmoothSurfaceBase Δ.signature) :
          PositiveGenusSmoothQuotient Δ.signature),
        SemidirectProduct.inr positiveGenusSmoothTopGenerator⁆
    have hmap :
        (fun j : Fin Δ.signature.orbitGenus =>
          ⁅positiveGenusGeneratorImageCore Δ
              (ULift.up (ProfiniteFenchelGenerator.surfaceA j)),
            positiveGenusGeneratorImageCore Δ
              (ULift.up (ProfiniteFenchelGenerator.surfaceB j))⁆) =
          fun j : Fin Δ.signature.orbitGenus =>
            if j.val = 0 then c0 else 1 := by
      funext j
      by_cases hj : j.val = 0
      · simp only [positiveGenusGeneratorImageCore, hj, ↓reduceIte, c0]
      · simp only [positiveGenusGeneratorImageCore, hj, ↓reduceIte, commutatorElement_self, c0]
    dsimp [c]
    rw [hmap]
    exact list_finRange_prod_eq_single_zeroVal hGenus c0
  have hCusp :
      ((List.finRange Δ.signature.numCusps).map fun j =>
        positiveGenusGeneratorImageCore Δ
          (ULift.up (ProfiniteFenchelGenerator.cusp j))).prod = 1 := by
    simp only [positiveGenusGeneratorImageCore, List.map_const', List.length_finRange,
      List.prod_replicate, one_pow]
  have hec : e * c = 1 := by
    rw [he, hc]
    exact positiveGenusSmoothEllipticProduct_mul_surfaceCommutator
      Δ.signature
  have hce : c * e = 1 := by
    have h' := congrArg (fun x => e⁻¹ * x * e) hec
    simpa [mul_assoc] using h'
  dsimp [profiniteFenchelTotalRelation]
  rw [hCusp]
  simpa [e, c, mul_assoc] using hce

private theorem positiveGenusGeneratorImage_lifted_total_relation
    (Δ : ProfiniteFGroup.{u}) (hGenus : 1 ≤ Δ.signature.orbitGenus) :
    profiniteFenchelTotalRelation
        (fun i => positiveGenusGeneratorImage Δ
          (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
        (fun i => positiveGenusGeneratorImage Δ
          (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
        (fun j => positiveGenusGeneratorImage Δ
          (ULift.up (ProfiniteFenchelGenerator.cusp j)))
        (fun k => positiveGenusGeneratorImage Δ
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) = 1 := by
  apply
    (MulEquiv.ulift :
      ULift.{u, 0} (PositiveGenusSmoothQuotient Δ.signature) ≃*
        PositiveGenusSmoothQuotient Δ.signature).injective
  simpa [positiveGenusGeneratorImage, profiniteFenchelTotalRelation,
    map_list_prod, Function.comp_def, map_commutatorElement] using
    positiveGenusGeneratorImage_total_relation Δ hGenus

private theorem positiveGenusGeneratorImage_period_relation
    (Δ : ProfiniteFGroup.{u}) (k : Fin Δ.signature.numPeriods) :
    positiveGenusGeneratorImageCore Δ
        (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^
      Δ.signature.periods k = 1 := by
  change
    (SemidirectProduct.inl
        (positiveGenusSmoothEllipticBase Δ.signature k) :
        PositiveGenusSmoothQuotient Δ.signature) ^
      Δ.signature.periods k = 1
  rw [← map_pow
    (SemidirectProduct.inl :
      PositiveGenusSmoothBase Δ.signature →*
        PositiveGenusSmoothQuotient Δ.signature)]
  simp only [positiveGenusSmoothEllipticBase_pow_period, map_one]

private theorem positiveGenusGeneratorImage_lifted_period_relation
    (Δ : ProfiniteFGroup.{u}) (k : Fin Δ.signature.numPeriods) :
    positiveGenusGeneratorImage Δ
        (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^
      Δ.signature.periods k = 1 := by
  apply
    (MulEquiv.ulift :
      ULift.{u, 0} (PositiveGenusSmoothQuotient Δ.signature) ≃*
        PositiveGenusSmoothQuotient Δ.signature).injective
  simpa [positiveGenusGeneratorImage] using
    positiveGenusGeneratorImage_period_relation Δ k

private theorem positiveGenusGeneratorImage_inertia_order
    (Δ : ProfiniteFGroup.{u}) (k : Fin Δ.signature.numPeriods) :
    orderOf
        (positiveGenusGeneratorImageCore Δ
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) =
      Δ.signature.periods k := by
  change
    orderOf
      ((SemidirectProduct.inl
        (positiveGenusSmoothEllipticBase Δ.signature k)) :
        PositiveGenusSmoothQuotient Δ.signature) =
      Δ.signature.periods k
  rw [orderOf_injective
    (SemidirectProduct.inl :
      PositiveGenusSmoothBase Δ.signature →*
        PositiveGenusSmoothQuotient Δ.signature)
    SemidirectProduct.inl_injective
    (positiveGenusSmoothEllipticBase Δ.signature k)]
  rw [positiveGenusSmoothEllipticBase, orderOf_ofAdd_eq_addOrderOf]
  exact zmodBasisVector_pair_neg_addOrderOf Δ.signature.periods k

private theorem positiveGenusGeneratorImage_lifted_inertia_order
    (Δ : ProfiniteFGroup.{u}) (k : Fin Δ.signature.numPeriods) :
    orderOf
        (positiveGenusGeneratorImage Δ
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) =
      Δ.signature.periods k := by
  have horder :=
    orderOf_injective
      ((MulEquiv.ulift :
        ULift.{u, 0} (PositiveGenusSmoothQuotient Δ.signature) ≃*
          PositiveGenusSmoothQuotient Δ.signature).toMonoidHom)
      (MulEquiv.ulift :
        ULift.{u, 0} (PositiveGenusSmoothQuotient Δ.signature) ≃*
          PositiveGenusSmoothQuotient Δ.signature).injective
      (positiveGenusGeneratorImage Δ
        (ULift.up (ProfiniteFenchelGenerator.inertia k)))
  rw [← horder]
  exact positiveGenusGeneratorImage_inertia_order Δ k

/-- The positive-genus smooth quotient is finite. -/
theorem positiveGenusSmoothQuotient_finite
    (σ : FenchelSignature) :
    Finite (PositiveGenusSmoothQuotient σ) := by
  classical
  letI : Finite (FenchelPeriodCoordinate σ) :=
    zmodCoordinateFamily_finite σ.periods
      (fun i => lt_of_lt_of_le (by decide : 0 < 2) (σ.period_ge_two i))
  haveI : Finite (PositiveGenusSmoothBase σ) := by
    infer_instance
  haveI : Finite (Multiplicative (ZMod 2)) := by
    infer_instance
  exact Finite.of_injective
    (fun q : PositiveGenusSmoothQuotient σ => (q.left, q.right))
    (by
      intro q r h
      exact SemidirectProduct.ext
        (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- The positive-genus smooth quotient has derived length at most two. -/
theorem positiveGenusSmoothQuotient_derivedSeries_two_eq_bot
    (σ : FenchelSignature) :
    derivedSeries (PositiveGenusSmoothQuotient σ) 2 = ⊥ := by
  let ρ : PositiveGenusSmoothQuotient σ →*
      Multiplicative (ZMod 2) :=
    SemidirectProduct.rightHom
  have hfirst :
      derivedSeries (PositiveGenusSmoothQuotient σ) 1 ≤ ρ.ker := by
    rw [derivedSeries_one]
    exact Abelianization.commutator_subset_ker ρ
  have hkerComm :
      ⁅ρ.ker, ρ.ker⁆ =
        (⊥ : Subgroup (PositiveGenusSmoothQuotient σ)) := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxright : x.right = 1 := by
      simpa [ρ] using MonoidHom.mem_ker.mp hx
    have hyright : y.right = 1 := by
      simpa [ρ] using MonoidHom.mem_ker.mp hy
    ext
    · simp only [SemidirectProduct.mul_left, hyright, map_one, MulAut.one_apply,
        mul_comm, toAdd_mul, Prod.fst_add, Pi.add_apply, hxright]
    · simp only [SemidirectProduct.mul_left, hyright, map_one, MulAut.one_apply,
        mul_comm, toAdd_mul, Prod.snd_add, Pi.add_apply, hxright]
    · simp only [SemidirectProduct.mul_right, hyright, hxright, mul_one, toAdd_one]
  apply le_antisymm
  · calc
      derivedSeries (PositiveGenusSmoothQuotient σ) 2 =
          ⁅derivedSeries (PositiveGenusSmoothQuotient σ) 1,
            derivedSeries (PositiveGenusSmoothQuotient σ) 1⁆ := by
            change derivedSeries (PositiveGenusSmoothQuotient σ) (1 + 1) =
              ⁅derivedSeries (PositiveGenusSmoothQuotient σ) 1,
                derivedSeries (PositiveGenusSmoothQuotient σ) 1⁆
            rw [derivedSeries_succ]
      _ ≤ ⁅ρ.ker, ρ.ker⁆ := Subgroup.commutator_mono hfirst hfirst
      _ = ⊥ := hkerComm
  · exact bot_le

noncomputable instance instFiniteULiftPositiveGenusSmoothQuotient (σ : FenchelSignature) :
    Finite (ULift.{u, 0} (PositiveGenusSmoothQuotient σ)) := by
  letI : Finite (PositiveGenusSmoothQuotient σ) :=
    positiveGenusSmoothQuotient_finite σ
  infer_instance

noncomputable def positiveGenusSmoothQuotientData
    (Δ : ProfiniteFGroup.{u}) (hGenus : 1 ≤ Δ.signature.orbitGenus) :
    ProfiniteSmoothQuotientData Δ 2 :=
  ProfiniteSmoothQuotientData.ofPresentationLiftToFiniteOfRelationsOfDerivedSeries
    Δ (positiveGenusGeneratorImage Δ)
    (positiveGenusGeneratorImage_lifted_total_relation Δ hGenus)
    (positiveGenusGeneratorImage_lifted_period_relation Δ)
    (derivedSeries_ulift_eq_bot_of
      (positiveGenusSmoothQuotient_derivedSeries_two_eq_bot
        Δ.signature))
    (positiveGenusGeneratorImage_lifted_inertia_order Δ)

end ProfiniteFGroup

end FenchelNielsen
