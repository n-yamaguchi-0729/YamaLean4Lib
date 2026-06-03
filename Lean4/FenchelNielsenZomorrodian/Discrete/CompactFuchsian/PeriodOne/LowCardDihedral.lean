import FenchelNielsenZomorrodian.Discrete.FiniteIndex.KernelTransfer
import FenchelNielsenZomorrodian.Discrete.FiniteIndex.SmoothQuotientData
import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.FirstReduction.KernelEquivalence

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/PeriodOne/LowCardDihedral.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Period-one cleanup step

Handles the cleanup of period-one target entries using quotient maps, kernel equivalences, low-cardinality dihedral cases, source subgroups, and relator proofs.
-/

open scoped BigOperators

namespace FenchelNielsen

theorem firstReductionTransportPeriodsFin_tail_low_card_eq_two
    {tailLen p : ℕ} (hp : 2 ≤ p) (hTailLen : 0 < tailLen)
    (hcard : ¬ 3 ≤ p * tailLen) :
    p = 2 ∧ tailLen = 1 := by
  have hlt : p * tailLen < 3 := by omega
  have htail_le : tailLen ≤ 1 := by
    by_cases hle : tailLen ≤ 1
    · exact hle
    · have htail_ge : 2 ≤ tailLen := by omega
      have hprod_ge : 4 ≤ p * tailLen := Nat.mul_le_mul hp htail_ge
      omega
  have htail_eq : tailLen = 1 := by omega
  have hp_le : p ≤ 2 := by
    rw [htail_eq, Nat.mul_one] at hlt
    omega
  have hp_eq : p = 2 := by omega
  exact ⟨hp_eq, htail_eq⟩

private theorem zmod_two_eq_zero_or_one_for_dihedral (z : ZMod 2) :
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

noncomputable def twoTwoTailDihedralInversion (n : ℕ) :
    MulAut (Multiplicative (ZMod n)) where
  toFun x := Multiplicative.ofAdd (-(Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd (-(Multiplicative.toAdd x))
  left_inv := by
    intro x
    cases x
    simp only [toAdd_ofAdd, ofAdd_neg, toAdd_inv, neg_neg]
  right_inv := by
    intro x
    cases x
    simp only [toAdd_ofAdd, ofAdd_neg, toAdd_inv, neg_neg]
  map_mul' := by
    intro x y
    cases x
    cases y
    simp only [toAdd_mul, toAdd_ofAdd, neg_add_rev, ofAdd_add, ofAdd_neg, mul_comm]

noncomputable def twoTwoTailDihedralAction (n : ℕ) :
    Multiplicative (ZMod 2) →* MulAut (Multiplicative (ZMod n)) where
  toFun t :=
    if Multiplicative.toAdd t = (0 : ZMod 2) then
      1
    else
      twoTwoTailDihedralInversion n
  map_one' := by rfl
  map_mul' := by
    intro a b
    have ha := zmod_two_eq_zero_or_one_for_dihedral (Multiplicative.toAdd a)
    have hb := zmod_two_eq_zero_or_one_for_dihedral (Multiplicative.toAdd b)
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · ext x : 1
      cases x
      simp only [toAdd_mul, ha, hb, add_zero, ↓reduceIte, MulAut.one_apply, mul_one]
    · ext x : 1
      cases x
      simp only [toAdd_mul, ha, hb, zero_add, one_ne_zero, ↓reduceIte, twoTwoTailDihedralInversion, ofAdd_neg,
  ofAdd_toAdd, MulEquiv.coe_mk, Equiv.coe_fn_mk, one_mul]
    · ext x : 1
      cases x
      simp only [toAdd_mul, ha, hb, add_zero, one_ne_zero, ↓reduceIte, twoTwoTailDihedralInversion, ofAdd_neg,
  ofAdd_toAdd, MulEquiv.coe_mk, Equiv.coe_fn_mk, mul_one]
    · have hsum : (1 : ZMod 2) + 1 = 0 := by
        simpa using (ZMod.natCast_self 2)
      ext x : 1
      cases x
      simp only [toAdd_mul, ha, hb, hsum, ↓reduceIte, MulAut.one_apply, one_ne_zero, twoTwoTailDihedralInversion,
  ofAdd_neg, ofAdd_toAdd, MulAut.mul_apply, MulEquiv.coe_mk, Equiv.coe_fn_mk, inv_inv]

abbrev TwoTwoTailDihedralQuotient (n : ℕ) :=
  Multiplicative (ZMod n) ⋊[twoTwoTailDihedralAction n] Multiplicative (ZMod 2)

noncomputable def twoTwoTailRotation (n : ℕ) : TwoTwoTailDihedralQuotient n :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod n))

noncomputable def twoTwoTailReflectionZero (n : ℕ) : TwoTwoTailDihedralQuotient n :=
  SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

noncomputable def twoTwoTailReflectionOne (n : ℕ) : TwoTwoTailDihedralQuotient n :=
  SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod n)) *
    SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))

/-- The rotation in the two-two-tail dihedral quotient has exponent `n`. -/
theorem twoTwoTailRotation_pow_period
    (n : ℕ) :
    twoTwoTailRotation n ^ n = 1 := by
  rw [twoTwoTailRotation, ← map_pow
    (SemidirectProduct.inl :
      Multiplicative (ZMod n) →* TwoTwoTailDihedralQuotient n)]
  apply congrArg SemidirectProduct.inl
  apply (Multiplicative.toAdd : Multiplicative (ZMod n) ≃ ZMod n).injective
  simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]

/-- The rotation in the two-two-tail dihedral quotient has order `n`. -/
theorem twoTwoTailRotation_order
    (n : ℕ) :
    orderOf (twoTwoTailRotation n) = n := by
  have hbase : orderOf (Multiplicative.ofAdd (1 : ZMod n)) = n := by
    simp only [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  simpa [twoTwoTailRotation, hbase] using
    orderOf_injective
      (SemidirectProduct.inl :
        Multiplicative (ZMod n) →* TwoTwoTailDihedralQuotient n)
      SemidirectProduct.inl_injective
      (Multiplicative.ofAdd (1 : ZMod n))

/-- The first reflection in the two-two-tail dihedral quotient squares to one. -/
theorem twoTwoTailReflectionZero_sq (n : ℕ) :
    twoTwoTailReflectionZero n ^ 2 = 1 := by
  have hsum : (1 : ZMod 2) + 1 = 0 := by
    simpa using (ZMod.natCast_self 2)
  ext
  · simp only [twoTwoTailReflectionZero, pow_two, SemidirectProduct.mul_left,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr, map_one, mul_one,
      toAdd_one, SemidirectProduct.one_left]
  · simp only [twoTwoTailReflectionZero, pow_two, SemidirectProduct.mul_right,
      SemidirectProduct.right_inr, toAdd_mul, toAdd_ofAdd, hsum,
      SemidirectProduct.one_right, toAdd_one]

/-- The second reflection in the two-two-tail dihedral quotient squares to one. -/
theorem twoTwoTailReflectionOne_sq (n : ℕ) :
    twoTwoTailReflectionOne n ^ 2 = 1 := by
  have href : ¬ Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2)) = (0 : ZMod 2) := by
    exact one_ne_zero
  have hsum : (1 : ZMod 2) + 1 = 0 := by
    simpa using (ZMod.natCast_self 2)
  ext
  · simp only [twoTwoTailDihedralAction, toAdd_eq_zero, twoTwoTailDihedralInversion,
      ofAdd_neg, ofAdd_toAdd, twoTwoTailReflectionOne, pow_two,
      SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
      MonoidHom.coe_mk, OneHom.coe_mk, ↓reduceIte, SemidirectProduct.left_inr,
      MulAut.one_apply, mul_one, SemidirectProduct.mul_right, SemidirectProduct.right_inr,
      one_mul, ofAdd_eq_one, one_ne_zero, MulEquiv.coe_mk, Equiv.coe_fn_mk,
      mul_inv_cancel, toAdd_one, SemidirectProduct.one_left]
  · simp only [twoTwoTailDihedralAction, twoTwoTailDihedralInversion,
      ofAdd_neg, ofAdd_toAdd, twoTwoTailReflectionOne, pow_two,
      SemidirectProduct.mul_right, SemidirectProduct.right_inl,
      SemidirectProduct.right_inr, one_mul, toAdd_mul, toAdd_ofAdd, hsum,
      SemidirectProduct.one_right, toAdd_one]

/-- The first reflection in the two-two-tail dihedral quotient has order two. -/
theorem twoTwoTailReflectionZero_order (n : ℕ) :
    orderOf (twoTwoTailReflectionZero n) = 2 := by
  have hsq := twoTwoTailReflectionZero_sq n
  have hdvd : orderOf (twoTwoTailReflectionZero n) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hsq
  have hne : twoTwoTailReflectionZero n ≠ 1 := by
    intro h
    have hright := congrArg (fun x : TwoTwoTailDihedralQuotient n => x.right) h
    simp only [twoTwoTailReflectionZero, SemidirectProduct.right_inr, SemidirectProduct.one_right, ofAdd_eq_one,
  one_ne_zero] at hright
  have hnotOne : orderOf (twoTwoTailReflectionZero n) ≠ 1 := by
    intro horder
    exact hne (orderOf_eq_one_iff.mp horder)
  have hnotZero : orderOf (twoTwoTailReflectionZero n) ≠ 0 := by
    intro hzero
    rw [hzero] at hdvd
    norm_num at hdvd
  have hle : orderOf (twoTwoTailReflectionZero n) ≤ 2 :=
    Nat.le_of_dvd (by decide : 0 < 2) hdvd
  omega

/-- The second reflection in the two-two-tail dihedral quotient has order two. -/
theorem twoTwoTailReflectionOne_order (n : ℕ) :
    orderOf (twoTwoTailReflectionOne n) = 2 := by
  have hsq := twoTwoTailReflectionOne_sq n
  have hdvd : orderOf (twoTwoTailReflectionOne n) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hsq
  have hne : twoTwoTailReflectionOne n ≠ 1 := by
    intro h
    have hright := congrArg (fun x : TwoTwoTailDihedralQuotient n => x.right) h
    simp only [twoTwoTailReflectionOne, SemidirectProduct.mul_right, SemidirectProduct.right_inl,
  SemidirectProduct.right_inr, one_mul, SemidirectProduct.one_right, ofAdd_eq_one, one_ne_zero] at hright
  have hnotOne : orderOf (twoTwoTailReflectionOne n) ≠ 1 := by
    intro horder
    exact hne (orderOf_eq_one_iff.mp horder)
  have hnotZero : orderOf (twoTwoTailReflectionOne n) ≠ 0 := by
    intro hzero
    rw [hzero] at hdvd
    norm_num at hdvd
  have hle : orderOf (twoTwoTailReflectionOne n) ≤ 2 :=
    Nat.le_of_dvd (by decide : 0 < 2) hdvd
  omega

/-- The two reflections and the rotation satisfy the total-relation product. -/
theorem twoTwoTail_reflection_product_rotation_eq_one (n : ℕ) :
    twoTwoTailReflectionZero n * twoTwoTailReflectionOne n * twoTwoTailRotation n = 1 := by
  have href : ¬ Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod 2)) = (0 : ZMod 2) := by
    exact one_ne_zero
  have hsum : (1 : ZMod 2) + 1 = 0 := by
    simpa using (ZMod.natCast_self 2)
  ext
  · simp only [twoTwoTailDihedralAction, toAdd_eq_zero, twoTwoTailDihedralInversion,
      ofAdd_neg, ofAdd_toAdd, twoTwoTailReflectionZero, twoTwoTailReflectionOne,
      twoTwoTailRotation, mul_assoc, SemidirectProduct.mul_left,
      SemidirectProduct.left_inr, SemidirectProduct.right_inr, MonoidHom.coe_mk,
      OneHom.coe_mk, ofAdd_eq_one, one_ne_zero, ↓reduceIte,
      SemidirectProduct.left_inl, SemidirectProduct.right_inl, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, one_mul, MulAut.one_apply, mul_inv_cancel, inv_one, mul_one,
      toAdd_one, SemidirectProduct.one_left]
  · simp only [twoTwoTailDihedralAction, twoTwoTailDihedralInversion,
      ofAdd_neg, ofAdd_toAdd, twoTwoTailReflectionZero, twoTwoTailReflectionOne,
      twoTwoTailRotation, mul_assoc, SemidirectProduct.mul_right,
      SemidirectProduct.right_inr, SemidirectProduct.right_inl, mul_comm, one_mul,
      toAdd_mul, toAdd_ofAdd, hsum, SemidirectProduct.one_right, toAdd_one]

def twoTwoTailPeriods (n : ℕ) : Fin 3 → ℕ := fun i =>
  if i.val = 0 then 2 else if i.val = 1 then 2 else n

/-- The period family of `twoTwoTailSignature` is pointwise at least two. -/
theorem twoTwoTailPeriods_ge_two {n : ℕ} (hn : 2 ≤ n) :
    ∀ i : Fin 3, 2 ≤ twoTwoTailPeriods n i := by
  intro i
  fin_cases i
  · simp only [twoTwoTailPeriods, ↓reduceIte, le_refl]
  · simp only [twoTwoTailPeriods, one_ne_zero, ↓reduceIte, le_refl]
  · simp only [twoTwoTailPeriods, OfNat.ofNat_ne_zero, ↓reduceIte, OfNat.ofNat_ne_one, hn]

noncomputable def twoTwoTailSignature (n : ℕ) (hn : 2 ≤ n) :
    FuchsianSignature where
  orbitGenus := 0
  numCusps := 0
  numPeriods := 3
  periods := twoTwoTailPeriods n
  period_ge_two := twoTwoTailPeriods_ge_two hn
  numCusps_eq_zero := rfl
  numPeriods_ge_three := by norm_num

noncomputable def twoTwoTailDihedralGeneratorImage {n : ℕ} (hn : 2 ≤ n) :
    FuchsianGenerator (twoTwoTailSignature n hn) → TwoTwoTailDihedralQuotient n
  | .elliptic i =>
      if i.val = 0 then
        twoTwoTailReflectionZero n
      else if i.val = 1 then
        twoTwoTailReflectionOne n
      else
        twoTwoTailRotation n
  | .surfaceA _ => 1
  | .surfaceB _ => 1

private theorem twoTwoTailDihedralGeneratorImage_respects_relators
    {n : ℕ} (hn : 2 ≤ n) :
    ∀ r ∈ relators (twoTwoTailSignature n hn),
      FreeGroup.lift (twoTwoTailDihedralGeneratorImage hn) r = 1 := by
  intro r hr
  rcases hr with ⟨i, rfl⟩ | rfl
  · fin_cases i
    · simpa only [twoTwoTailSignature, xWord, Fin.reduceFinMk, Fin.isValue,
        twoTwoTailPeriods, Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceIte, map_pow,
        FreeGroup.lift_apply_of, twoTwoTailDihedralGeneratorImage] using
        twoTwoTailReflectionZero_sq (n := n)
    · simpa only [twoTwoTailSignature, xWord, Fin.reduceFinMk, Fin.isValue,
        twoTwoTailPeriods, Fin.coe_ofNat_eq_mod, Nat.one_mod, one_ne_zero,
        ↓reduceIte, map_pow, FreeGroup.lift_apply_of, twoTwoTailDihedralGeneratorImage] using
        twoTwoTailReflectionOne_sq (n := n)
    · simpa only [twoTwoTailSignature, xWord, Fin.reduceFinMk, Fin.isValue,
        twoTwoTailPeriods, Fin.coe_ofNat_eq_mod, Nat.mod_succ, OfNat.ofNat_ne_zero,
        ↓reduceIte, OfNat.ofNat_ne_one, map_pow, FreeGroup.lift_apply_of,
        twoTwoTailDihedralGeneratorImage] using
        twoTwoTailRotation_pow_period (n := n)
  · dsimp [totalRelation]
    rw [map_mul, map_list_prod, map_list_prod]
    have hEll :
        (List.map (⇑(FreeGroup.lift (twoTwoTailDihedralGeneratorImage hn)))
            (List.map (fun i => xWord (twoTwoTailSignature n hn) i)
              (List.finRange (twoTwoTailSignature n hn).numPeriods))).prod =
          twoTwoTailReflectionZero n * twoTwoTailReflectionOne n * twoTwoTailRotation n := by
      simpa [twoTwoTailSignature] using
        (show
          (List.map (⇑(FreeGroup.lift (twoTwoTailDihedralGeneratorImage hn)))
              (List.map (fun i => xWord (twoTwoTailSignature n hn) i)
                (List.finRange 3))).prod =
            twoTwoTailReflectionZero n * twoTwoTailReflectionOne n * twoTwoTailRotation n by
          have hRange : List.finRange 3 = [0, 1, 2] := by
            decide
          rw [hRange]
          have hNum : (twoTwoTailSignature n hn).numPeriods = 3 := by
            rfl
          simp only [xWord, Fin.isValue, List.map_cons, List.map_nil, FreeGroup.lift_apply_of,
  twoTwoTailDihedralGeneratorImage, Fin.coe_ofNat_eq_mod, hNum, Nat.zero_mod, ↓reduceIte, twoTwoTailReflectionZero,
  Nat.one_mod, one_ne_zero, twoTwoTailReflectionOne, Nat.mod_succ, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one,
  twoTwoTailRotation, List.prod_cons, List.prod_nil, mul_one, mul_assoc])
    have hComm :
        (List.map (⇑(FreeGroup.lift (twoTwoTailDihedralGeneratorImage hn)))
            (List.map (fun j => ⁅aWord (twoTwoTailSignature n hn) j,
                bWord (twoTwoTailSignature n hn) j⁆)
              (List.finRange (twoTwoTailSignature n hn).orbitGenus))).prod = 1 := by
      rfl
    rw [hEll, hComm, mul_one]
    exact twoTwoTail_reflection_product_rotation_eq_one n

noncomputable def twoTwoTailDihedralHom
    {n : ℕ} (hn : 2 ≤ n) :
    FuchsianPresentedGroup (twoTwoTailSignature n hn) →*
      TwoTwoTailDihedralQuotient n :=
  PresentedGroup.toGroup (rels := relators (twoTwoTailSignature n hn))
    (f := twoTwoTailDihedralGeneratorImage hn)
    (twoTwoTailDihedralGeneratorImage_respects_relators hn)

/-- The two-two-tail dihedral quotient is finite. -/
theorem twoTwoTailDihedralQuotient_finite
    {n : ℕ} (hn : 2 ≤ n) :
    Finite (TwoTwoTailDihedralQuotient n) := by
  letI : NeZero n := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn)⟩
  letI : Fintype (ZMod n) := ZMod.fintype n
  haveI : Fintype (Multiplicative (ZMod n)) := inferInstance
  haveI : Fintype (Multiplicative (ZMod 2)) := inferInstance
  exact Finite.of_injective
    (fun q : TwoTwoTailDihedralQuotient n => (q.left, q.right))
    (by
      intro q r h
      exact SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

/-- The two-two-tail dihedral quotient has derived length at most two. -/
theorem twoTwoTailDihedralQuotient_derivedSeries_two_eq_bot
    (n : ℕ) :
    derivedSeries (TwoTwoTailDihedralQuotient n) 2 = ⊥ := by
  let ρ : TwoTwoTailDihedralQuotient n →* Multiplicative (ZMod 2) :=
    SemidirectProduct.rightHom
  have hfirst : derivedSeries (TwoTwoTailDihedralQuotient n) 1 ≤ ρ.ker := by
    rw [derivedSeries_one]
    exact Abelianization.commutator_subset_ker ρ
  have hkerComm :
      ⁅ρ.ker, ρ.ker⁆ = (⊥ : Subgroup (TwoTwoTailDihedralQuotient n)) := by
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
        mul_comm, toAdd_mul, hxright]
    · simp only [SemidirectProduct.mul_right, hyright, hxright, mul_one, toAdd_one]
  apply le_antisymm
  · calc
      derivedSeries (TwoTwoTailDihedralQuotient n) 2 =
          ⁅derivedSeries (TwoTwoTailDihedralQuotient n) 1,
            derivedSeries (TwoTwoTailDihedralQuotient n) 1⁆ := by
            change derivedSeries (TwoTwoTailDihedralQuotient n) (1 + 1) =
              ⁅derivedSeries (TwoTwoTailDihedralQuotient n) 1,
                derivedSeries (TwoTwoTailDihedralQuotient n) 1⁆
            rw [derivedSeries_succ]
      _ ≤ ⁅ρ.ker, ρ.ker⁆ := Subgroup.commutator_mono hfirst hfirst
      _ = ⊥ := hkerComm
  · exact bot_le

noncomputable def finiteSolvableSmoothQuotientData_two_of_twoTwoTail
    {n : ℕ} (hn : 2 ≤ n) :
    FiniteSolvableSmoothQuotientData (twoTwoTailSignature n hn) 2 where
  Q := TwoTwoTailDihedralQuotient n
  finite := twoTwoTailDihedralQuotient_finite hn
  φ := twoTwoTailDihedralHom hn
  derived_length := twoTwoTailDihedralQuotient_derivedSeries_two_eq_bot n
  elliptic_exact := by
    intro i
    fin_cases i
    · simpa [twoTwoTailDihedralHom, ellipticElement, twoTwoTailDihedralGeneratorImage,
        twoTwoTailSignature, twoTwoTailPeriods] using
          twoTwoTailReflectionZero_order n
    · simpa [twoTwoTailDihedralHom, ellipticElement, twoTwoTailDihedralGeneratorImage,
        twoTwoTailSignature, twoTwoTailPeriods] using
          twoTwoTailReflectionOne_order n
    · simpa [twoTwoTailDihedralHom, ellipticElement, twoTwoTailDihedralGeneratorImage,
        twoTwoTailSignature, twoTwoTailPeriods] using
          twoTwoTailRotation_order n

/-- Source-subgroup version of the low `[2,2,n]` first-reduction branch.
    This avoids taking a normal core in the local period-one cleanup proof: the
    later paper-facing endpoint can still normalize the final subgroup if it is
    needed. -/
theorem FirstReductionPeriodData.sourceSubgroup_exists_of_two_two_tail_two
    {σ : FuchsianSignature} (D : FirstReductionPeriodData σ)
    (hm₁' : D.m₁' = 1) (hm₂' : D.m₂' = 1)
    (hp_eq_two : D.p = 2) (hTailLen_eq_one : D.tailLen = 1) :
    ∃ L : Subgroup (FuchsianPresentedGroup D.sourceSignature),
      L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
        SubgroupQuotientHasDerivedLengthAtMost L 2 := by
  classical
  let k : Fin D.tailLen := ⟨0, by omega⟩
  let n := D.tail k
  have hn : 2 ≤ n := D.htail k
  let τ := twoTwoTailSignature n hn
  let eTarget : OriginalFirstReductionIndex D.tailLen ≃ Fin τ.numPeriods :=
    (originalFirstReductionIndexEquivCanonicalSourceFin D.tailLen).trans
      (finCongr (by simp only [twoTwoTailSignature, τ]; omega))
  have hSourceEquiv :
      Nonempty (FuchsianPresentedGroup D.sourceSignature ≃* FuchsianPresentedGroup τ) := by
    refine
      zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods
        D.sourceSignature τ
        (by rfl)
        (by rfl)
        (originalFirstReductionOrderedIndexEquiv D.tailLen)
        eTarget ?_
    intro x
    cases x using Sum.casesOn with
    | inl i =>
        fin_cases i
        · have hSource :
            D.sourceSignature.periods
                ((originalFirstReductionOrderedIndexEquiv D.tailLen) (.inl 0)) = 2 := by
            simp only [sourceSignature, originalFirstReductionSignature, Fin.isValue,
  originalFirstReductionOrderedIndexEquiv_left_zero, hp_eq_two, hm₁', originalFirstReductionSignaturePeriod_zero_fin,
  mul_one]
          have hTarget :
              τ.periods (eTarget (.inl 0)) = 2 := by
            rfl
          exact hSource.trans hTarget.symm
        · have hSource :
            D.sourceSignature.periods
                ((originalFirstReductionOrderedIndexEquiv D.tailLen) (.inl 1)) = 2 := by
            simp only [sourceSignature, originalFirstReductionSignature, Fin.isValue,
  originalFirstReductionOrderedIndexEquiv_left_one, hp_eq_two, hm₂', originalFirstReductionSignaturePeriod_one_fin,
  mul_one]
          have hTarget :
              τ.periods (eTarget (.inl 1)) = 2 := by
            rfl
          exact hSource.trans hTarget.symm
    | inr j =>
        have hj : j = k := by
          ext
          omega
        rw [hj]
        have hSource :
          D.sourceSignature.periods
              ((originalFirstReductionOrderedIndexEquiv D.tailLen) (.inr k)) = n := by
          rw [originalFirstReductionOrderedIndexEquiv_right]
          simpa [FirstReductionPeriodData.sourceSignature, originalFirstReductionSignature, k, n]
            using
              originalFirstReductionSignaturePeriod_tail
                (p := D.p) D.m₁' D.m₂' D.tail k
        have hTarget :
            τ.periods (eTarget (.inr k)) = n := by
          rfl
        exact hSource.trans hTarget.symm
  have hτ :
      ∃ L : Subgroup (FuchsianPresentedGroup τ),
        L.FiniteIndex ∧ IsTorsionFreeGroup L ∧
          SubgroupQuotientHasDerivedLengthAtMost L 2 :=
    (finiteSolvableSmoothQuotientData_two_of_twoTwoTail hn).sourceSubgroup_exists_classical
  exact sourceSubgroup_exists_of_mulEquiv (Classical.choice hSourceEquiv) hτ

end FenchelNielsen
