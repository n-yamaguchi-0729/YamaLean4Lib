import FenchelNielsenZomorrodian.Profinite.SmoothQuotient

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Profinite/LowPeriodQuotient.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Low-period compact quotients

Handles compact zero-genus boundary cases with two periods by constructing the required cyclic smooth quotient.
-/

namespace FenchelNielsen

universe u

namespace ProfiniteFGroup

noncomputable def twoPeriodIndexZero
    (Δ : ProfiniteFGroup.{u}) (hTwo : Δ.signature.numPeriods = 2) :
    Fin Δ.signature.numPeriods :=
  Fin.cast hTwo.symm (0 : Fin 2)

noncomputable def twoPeriodIndexOne
    (Δ : ProfiniteFGroup.{u}) (hTwo : Δ.signature.numPeriods = 2) :
    Fin Δ.signature.numPeriods :=
  Fin.cast hTwo.symm (1 : Fin 2)

/-- With two periods, the inertia part of the total relation is the product of the two indexed
inertia generators. -/
theorem twoPeriod_inertia_list_product
    (Δ : ProfiniteFGroup.{u}) (hTwo : Δ.signature.numPeriods = 2) :
    ((List.finRange Δ.signature.numPeriods).map fun k => Δ.inertia k).prod =
      Δ.inertia (twoPeriodIndexZero Δ hTwo) *
        Δ.inertia (twoPeriodIndexOne Δ hTwo) := by
  cases Δ with
  | mk carrier ps prof fg sig dsig surfaceA surfaceB cusp inertia rel gen
      basis relators rel_eq pres presA presB presC presI inertia_order =>
    cases sig with
    | mk orbitGenus numCusps numPeriods periods period_ge_two =>
      dsimp at hTwo ⊢
      subst numPeriods
      norm_num [twoPeriodIndexZero, twoPeriodIndexOne, List.finRange]

/-- In the compact zero-genus two-period case, the two inertia generators multiply to one. -/
theorem twoPeriod_inertia_mul_eq_one
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hZero : Δ.signature.orbitGenus = 0)
    (hTwo : Δ.signature.numPeriods = 2) :
    Δ.inertia (twoPeriodIndexZero Δ hTwo) *
        Δ.inertia (twoPeriodIndexOne Δ hTwo) = 1 := by
  have hrel := Δ.presentation_relation
  have hSurface :
      ((List.finRange Δ.signature.orbitGenus).map fun i =>
        ⁅Δ.surfaceA i, Δ.surfaceB i⁆).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    rcases List.mem_map.mp hx with ⟨j, _hj, rfl⟩
    exfalso
    rw [hZero] at j
    exact Nat.not_lt_zero _ j.2
  have hCusp :
      ((List.finRange Δ.signature.numCusps).map fun j => Δ.cusp j).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    rcases List.mem_map.mp hx with ⟨j, _hj, rfl⟩
    exfalso
    rw [hCompact] at j
    exact Nat.not_lt_zero _ j.2
  rw [profiniteFenchelTotalRelation, hSurface, hCusp, one_mul, one_mul,
    twoPeriod_inertia_list_product Δ hTwo] at hrel
  exact hrel

/-- In the compact zero-genus two-period case, the two periods are equal. -/
theorem twoPeriod_periods_eq
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hZero : Δ.signature.orbitGenus = 0)
    (hTwo : Δ.signature.numPeriods = 2) :
    Δ.signature.periods (twoPeriodIndexZero Δ hTwo) =
      Δ.signature.periods (twoPeriodIndexOne Δ hTwo) := by
  have hmul := twoPeriod_inertia_mul_eq_one Δ hCompact hZero hTwo
  calc
    Δ.signature.periods (twoPeriodIndexZero Δ hTwo) =
        orderOf (Δ.inertia (twoPeriodIndexZero Δ hTwo)) := by
          rw [Δ.inertia_order]
    _ = orderOf (Δ.inertia (twoPeriodIndexOne Δ hTwo)) := by
          rw [eq_inv_of_mul_eq_one_left hmul, orderOf_inv]
    _ = Δ.signature.periods (twoPeriodIndexOne Δ hTwo) := by
          rw [Δ.inertia_order]

instance instTopologicalSpaceMultiplicativeZMod (n : ℕ) :
    TopologicalSpace (Multiplicative (ZMod n)) :=
  ⊥

instance instDiscreteTopologyMultiplicativeZMod (n : ℕ) :
    DiscreteTopology (Multiplicative (ZMod n)) :=
  ⟨rfl⟩

noncomputable instance instFintypeMultiplicativeZMod (n : ℕ) [NeZero n] :
    Fintype (Multiplicative (ZMod n)) :=
  Fintype.ofEquiv (ZMod n) Multiplicative.toAdd

noncomputable instance instFiniteMultiplicativeZMod (n : ℕ) [NeZero n] :
    Finite (Multiplicative (ZMod n)) :=
  Finite.of_fintype _

noncomputable instance instFiniteULiftMultiplicativeZMod (n : ℕ) [NeZero n] :
    Finite (ULift.{u, 0} (Multiplicative (ZMod n))) := by
  infer_instance

noncomputable def twoPeriodCyclicGeneratorImageCore
    (Δ : ProfiniteFGroup.{u}) (hTwo : Δ.signature.numPeriods = 2) :
    ProfiniteFenchelGeneratorIndex.{u} Δ.signature →
      Multiplicative
        (ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)))
  | ULift.up (.inertia k) =>
      if (Fin.cast hTwo k).val = 0 then
        Multiplicative.ofAdd (1 :
          ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)))
      else
        (Multiplicative.ofAdd (1 :
          ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo))))⁻¹
  | ULift.up (.surfaceA _) => 1
  | ULift.up (.surfaceB _) => 1
  | ULift.up (.cusp _) => 1

noncomputable def twoPeriodCyclicGeneratorImage
    (Δ : ProfiniteFGroup.{u}) (hTwo : Δ.signature.numPeriods = 2) :
    ProfiniteFenchelGeneratorIndex.{u} Δ.signature →
      ULift.{u, 0}
        (Multiplicative
          (ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)))) :=
  fun x => ULift.up (twoPeriodCyclicGeneratorImageCore Δ hTwo x)

private theorem twoPeriodCyclicGeneratorImage_total_relation
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hZero : Δ.signature.orbitGenus = 0)
    (hTwo : Δ.signature.numPeriods = 2) :
    profiniteFenchelTotalRelation
        (fun i => twoPeriodCyclicGeneratorImageCore Δ hTwo
          (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
        (fun i => twoPeriodCyclicGeneratorImageCore Δ hTwo
          (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
        (fun j => twoPeriodCyclicGeneratorImageCore Δ hTwo
          (ULift.up (ProfiniteFenchelGenerator.cusp j)))
        (fun k => twoPeriodCyclicGeneratorImageCore Δ hTwo
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) = 1 := by
  cases Δ with
  | mk carrier ps prof fg sig dsig surfaceA surfaceB cusp inertia rel gen
      basis relators rel_eq pres presA presB presC presI inertia_order =>
    cases sig with
    | mk orbitGenus numCusps numPeriods periods period_ge_two =>
      dsimp [FenchelSignature.IsCompact] at hCompact
      dsimp at hZero hTwo ⊢
      subst orbitGenus
      subst numCusps
      subst numPeriods
      dsimp [profiniteFenchelTotalRelation, twoPeriodCyclicGeneratorImageCore,
        twoPeriodIndexZero]
      simp only [List.finRange_zero, List.map_nil, List.prod_nil, one_mul]
      change
        ((List.finRange 2).map fun k : Fin 2 =>
          if k = 0 then
            Multiplicative.ofAdd (1 : ZMod (periods 0))
          else
            (Multiplicative.ofAdd (1 : ZMod (periods 0)))⁻¹).prod = 1
      norm_num [List.finRange]

private theorem twoPeriodCyclicGeneratorImage_lifted_total_relation
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hZero : Δ.signature.orbitGenus = 0)
    (hTwo : Δ.signature.numPeriods = 2) :
    profiniteFenchelTotalRelation
        (fun i => twoPeriodCyclicGeneratorImage Δ hTwo
          (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
        (fun i => twoPeriodCyclicGeneratorImage Δ hTwo
          (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
        (fun j => twoPeriodCyclicGeneratorImage Δ hTwo
          (ULift.up (ProfiniteFenchelGenerator.cusp j)))
        (fun k => twoPeriodCyclicGeneratorImage Δ hTwo
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) = 1 := by
  apply
    (MulEquiv.ulift :
      ULift.{u, 0}
        (Multiplicative
          (ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)))) ≃*
        Multiplicative
          (ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)))).injective
  simpa [twoPeriodCyclicGeneratorImage, profiniteFenchelTotalRelation,
    map_list_prod, Function.comp_def, map_commutatorElement] using
    twoPeriodCyclicGeneratorImage_total_relation Δ hCompact hZero hTwo

private theorem twoPeriodCyclicGeneratorImage_period_relation
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hZero : Δ.signature.orbitGenus = 0)
    (hTwo : Δ.signature.numPeriods = 2)
    (k : Fin Δ.signature.numPeriods) :
    twoPeriodCyclicGeneratorImageCore Δ hTwo
        (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^
      Δ.signature.periods k = 1 := by
  have hEq := twoPeriod_periods_eq Δ hCompact hZero hTwo
  cases Δ with
  | mk carrier ps prof fg sig dsig surfaceA surfaceB cusp inertia rel gen
      basis relators rel_eq pres presA presB presC presI inertia_order =>
    cases sig with
    | mk orbitGenus numCusps numPeriods periods period_ge_two =>
      dsimp at hCompact hZero hTwo hEq k ⊢
      subst numPeriods
      fin_cases k
      · have horder :
            orderOf
              (Multiplicative.ofAdd (1 : ZMod (periods 0))) =
                periods 0 := by
          rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
        simpa [twoPeriodCyclicGeneratorImageCore, twoPeriodIndexZero,
          horder] using
          pow_orderOf_eq_one
            (Multiplicative.ofAdd (1 : ZMod (periods 0)))
      · have h10 : periods 1 = periods 0 := by
          simpa [twoPeriodIndexZero, twoPeriodIndexOne] using hEq.symm
        have horder :
            orderOf
              ((Multiplicative.ofAdd (1 : ZMod (periods 0)))⁻¹) =
                periods 1 := by
          rw [orderOf_inv, orderOf_ofAdd_eq_addOrderOf,
            ZMod.addOrderOf_one, h10]
        simpa [twoPeriodCyclicGeneratorImageCore, twoPeriodIndexZero,
          horder] using
          pow_orderOf_eq_one
            ((Multiplicative.ofAdd (1 : ZMod (periods 0)))⁻¹)

private theorem twoPeriodCyclicGeneratorImage_lifted_period_relation
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hZero : Δ.signature.orbitGenus = 0)
    (hTwo : Δ.signature.numPeriods = 2)
    (k : Fin Δ.signature.numPeriods) :
    twoPeriodCyclicGeneratorImage Δ hTwo
        (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^
      Δ.signature.periods k = 1 := by
  apply
    (MulEquiv.ulift :
      ULift.{u, 0}
        (Multiplicative
          (ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)))) ≃*
        Multiplicative
          (ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)))).injective
  simpa [twoPeriodCyclicGeneratorImage] using
    twoPeriodCyclicGeneratorImage_period_relation Δ hCompact hZero hTwo k

private theorem twoPeriodCyclicGeneratorImage_inertia_order
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hZero : Δ.signature.orbitGenus = 0)
    (hTwo : Δ.signature.numPeriods = 2)
    (k : Fin Δ.signature.numPeriods) :
    orderOf
        (twoPeriodCyclicGeneratorImageCore Δ hTwo
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) =
      Δ.signature.periods k := by
  have hEq := twoPeriod_periods_eq Δ hCompact hZero hTwo
  cases Δ with
  | mk carrier ps prof fg sig dsig surfaceA surfaceB cusp inertia rel gen
      basis relators rel_eq pres presA presB presC presI inertia_order =>
    cases sig with
    | mk orbitGenus numCusps numPeriods periods period_ge_two =>
      dsimp at hCompact hZero hTwo hEq k ⊢
      subst numPeriods
      fin_cases k
      · simp only [twoPeriodIndexZero, Fin.isValue, Fin.cast_eq_self, twoPeriodCyclicGeneratorImageCore, Fin.zero_eta,
  Fin.coe_ofNat_eq_mod, Nat.zero_mod, ↓reduceIte, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
      · have h10 : periods 1 = periods 0 := by
          simpa [twoPeriodIndexZero, twoPeriodIndexOne] using hEq.symm
        simp only [twoPeriodIndexZero, Fin.isValue, Fin.cast_eq_self, twoPeriodCyclicGeneratorImageCore, Fin.mk_one,
  Fin.coe_ofNat_eq_mod, Nat.mod_succ, one_ne_zero, ↓reduceIte, orderOf_inv, orderOf_ofAdd_eq_addOrderOf,
  ZMod.addOrderOf_one, h10]

private theorem twoPeriodCyclicGeneratorImage_lifted_inertia_order
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hZero : Δ.signature.orbitGenus = 0)
    (hTwo : Δ.signature.numPeriods = 2)
    (k : Fin Δ.signature.numPeriods) :
    orderOf
        (twoPeriodCyclicGeneratorImage Δ hTwo
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) =
      Δ.signature.periods k := by
  have horder :=
    orderOf_injective
      ((MulEquiv.ulift :
        ULift.{u, 0}
          (Multiplicative
            (ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)))) ≃*
          Multiplicative
            (ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)))).toMonoidHom)
      (MulEquiv.ulift :
        ULift.{u, 0}
          (Multiplicative
            (ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)))) ≃*
          Multiplicative
            (ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)))).injective
      (twoPeriodCyclicGeneratorImage Δ hTwo
        (ULift.up (ProfiniteFenchelGenerator.inertia k)))
  rw [← horder]
  exact twoPeriodCyclicGeneratorImage_inertia_order Δ hCompact hZero hTwo k

noncomputable def twoPeriodCyclicSmoothQuotientData
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hZero : Δ.signature.orbitGenus = 0)
    (hTwo : Δ.signature.numPeriods = 2) :
    ProfiniteSmoothQuotientData Δ 1 :=
  have hpos :
      0 < Δ.signature.periods (twoPeriodIndexZero Δ hTwo) :=
    lt_of_lt_of_le (by decide : 0 < 2)
      (Δ.signature.period_ge_two (twoPeriodIndexZero Δ hTwo))
  letI : NeZero (Δ.signature.periods (twoPeriodIndexZero Δ hTwo)) :=
    ⟨Nat.pos_iff_ne_zero.mp hpos⟩
  ProfiniteSmoothQuotientData.ofPresentationLiftToFiniteOfRelations
    Δ (twoPeriodCyclicGeneratorImage Δ hTwo)
    (twoPeriodCyclicGeneratorImage_lifted_total_relation
      Δ hCompact hZero hTwo)
    (twoPeriodCyclicGeneratorImage_lifted_period_relation
      Δ hCompact hZero hTwo)
    (profiniteDerivedSeries_one_eq_bot_of_commGroup
      (ULift.{u, 0}
        (Multiplicative
          (ZMod (Δ.signature.periods (twoPeriodIndexZero Δ hTwo))))))
    (twoPeriodCyclicGeneratorImage_lifted_inertia_order
      Δ hCompact hZero hTwo)

end ProfiniteFGroup

end FenchelNielsen
