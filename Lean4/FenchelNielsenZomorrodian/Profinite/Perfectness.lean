import FenchelNielsenZomorrodian.Discrete.Arithmetic.PrimeDivisors
import FenchelNielsenZomorrodian.Profinite.FGroup

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Profinite/Perfectness.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Perfectness numerics for profinite Fenchel groups

This file isolates the abelianization computation used in the non-perfect
zero-genus compact branch of the three-step Fenchel-Nielsen theorem.
-/

namespace FenchelNielsen

universe u

namespace ProfiniteFGroup

/-- In a compact zero-genus no-cusp profinite Fenchel group, every commutative quotient kills the
`otherPeriodsLcm`-power of each inertia image. -/
theorem commHom_inertia_pow_otherPeriodsLcm_eq_one_of_zeroGenus_noCusps
    (Δ : ProfiniteFGroup.{u})
    (hZero : Δ.signature.orbitGenus = 0)
    (hNoCusps : Δ.signature.numCusps = 0)
    {A : Type u} [CommGroup A]
    (φ : Δ.carrier →* A) (i : Fin Δ.signature.numPeriods) :
    φ (Δ.inertia i) ^ otherPeriodsLcm Δ.signature i = 1 := by
  let ξ : Fin Δ.signature.numPeriods → A := fun j => φ (Δ.inertia j)
  have hpow : ∀ j : Fin Δ.signature.numPeriods,
      ξ j ^ Δ.signature.periods j = 1 := by
    intro j
    have hsource : Δ.inertia j ^ Δ.signature.periods j = 1 := by
      rw [← Δ.inertia_order j]
      exact pow_orderOf_eq_one (Δ.inertia j)
    simpa [ξ] using congrArg φ hsource
  have hprodList :
      ((List.finRange Δ.signature.numPeriods).map fun j => ξ j).prod = 1 := by
    have hrel := congrArg φ Δ.presentation_relation
    have hrelFull :
        (List.map (fun i : Fin Δ.signature.orbitGenus =>
            φ ⁅Δ.surfaceA i, Δ.surfaceB i⁆)
            (List.finRange Δ.signature.orbitGenus)).prod *
          (List.map (fun j : Fin Δ.signature.numCusps => φ (Δ.cusp j))
            (List.finRange Δ.signature.numCusps)).prod *
            (List.map (fun k : Fin Δ.signature.numPeriods => φ (Δ.inertia k))
              (List.finRange Δ.signature.numPeriods)).prod = 1 := by
      simpa [profiniteFenchelTotalRelation, map_list_prod, Function.comp_def,
        map_commutatorElement] using hrel
    have hSurface :
        (List.map (fun i : Fin Δ.signature.orbitGenus =>
            φ ⁅Δ.surfaceA i, Δ.surfaceB i⁆)
            (List.finRange Δ.signature.orbitGenus)).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      rcases List.mem_map.mp hx with ⟨j, _hj, rfl⟩
      exfalso
      rw [hZero] at j
      exact Nat.not_lt_zero _ j.2
    have hCusp :
        (List.map (fun j : Fin Δ.signature.numCusps => φ (Δ.cusp j))
            (List.finRange Δ.signature.numCusps)).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      rcases List.mem_map.mp hx with ⟨j, _hj, rfl⟩
      exfalso
      rw [hNoCusps] at j
      exact Nat.not_lt_zero _ j.2
    rw [hSurface, hCusp, one_mul, one_mul] at hrelFull
    simpa [ξ] using hrelFull
  have hprod : ∏ j : Fin Δ.signature.numPeriods, ξ j = 1 := by
    simpa [Fin.prod_univ_def] using hprodList
  let L := otherPeriodsLcm Δ.signature i
  have hsplit' : ((Finset.univ.erase i).prod ξ) * ξ i = 1 := by
    calc
      ((Finset.univ.erase i).prod ξ) * ξ i = ∏ j, ξ j := by
        exact Finset.prod_erase_mul
          (s := Finset.univ) (f := ξ) (a := i) (Finset.mem_univ i)
      _ = 1 := hprod
  have hsplit : ξ i * ((Finset.univ.erase i).prod ξ) = 1 := by
    simpa [mul_comm] using hsplit'
  have hOthers :
      ((Finset.univ.erase i).prod ξ) ^ L = 1 := by
    rw [← Finset.prod_pow]
    refine Finset.prod_eq_one ?_
    intro j hj
    obtain ⟨m, hm⟩ :=
      Finset.dvd_lcm (s := Finset.univ.erase i)
        (f := Δ.signature.periods) hj
    rw [show L = Δ.signature.periods j * m by
        simpa [L, otherPeriodsLcm] using hm,
      pow_mul, hpow j, one_pow]
  have hPow : ξ i ^ L = 1 := by
    have hsplitPow := congrArg (fun a : A => a ^ L) hsplit
    simp only at hsplitPow
    rw [mul_pow, hOthers, mul_one] at hsplitPow
    simpa [L] using hsplitPow
  simpa [ξ, L] using hPow

/-- Under the characteristic perfect numerical condition, every commutative quotient kills each
inertia image. -/
theorem commHom_inertia_eq_one_of_charPerfectNumericalCondition
    (Δ : ProfiniteFGroup.{u})
    (hChar : Δ.CharPerfectNumericalCondition)
    {A : Type u} [CommGroup A]
    (φ : Δ.carrier →* A)
    (i : Fin Δ.signature.numPeriods) :
    φ (Δ.inertia i) = 1 := by
  rcases hChar with ⟨hZero, hNoCusps, hPair⟩
  let ξ : Fin Δ.signature.numPeriods → A := fun j => φ (Δ.inertia j)
  have hpow : ξ i ^ Δ.signature.periods i = 1 := by
    have hsource : Δ.inertia i ^ Δ.signature.periods i = 1 := by
      rw [← Δ.inertia_order i]
      exact pow_orderOf_eq_one (Δ.inertia i)
    simpa [ξ] using congrArg φ hsource
  have hPow : ξ i ^ otherPeriodsLcm Δ.signature i = 1 :=
    commHom_inertia_pow_otherPeriodsLcm_eq_one_of_zeroGenus_noCusps
      Δ hZero hNoCusps φ i
  have hCoprimeProd :
      Nat.Coprime (Δ.signature.periods i)
        ((Finset.univ.erase i : Finset (Fin Δ.signature.numPeriods)).prod
          Δ.signature.periods) := by
    rw [Nat.coprime_prod_right_iff]
    intro j hj
    exact hPair i j (Finset.mem_erase.mp hj).1.symm
  have hLDiv :
      otherPeriodsLcm Δ.signature i ∣
        (Finset.univ.erase i : Finset (Fin Δ.signature.numPeriods)).prod
          Δ.signature.periods := by
    dsimp [otherPeriodsLcm]
    exact Finset.lcm_dvd (fun j hj => Finset.dvd_prod_of_mem _ hj)
  have hCoprime :
      Nat.Coprime (Δ.signature.periods i)
        (otherPeriodsLcm Δ.signature i) :=
    hCoprimeProd.of_dvd_right hLDiv
  have hOrder : orderOf (ξ i) = 1 := by
    exact Nat.eq_one_of_dvd_coprimes hCoprime
      (orderOf_dvd_of_pow_eq_one hpow)
      (orderOf_dvd_of_pow_eq_one hPow)
  simpa [ξ] using orderOf_eq_one_iff.mp hOrder

/-- The characteristic perfect numerical condition implies perfectness. -/
theorem isPerfect_of_charPerfectNumericalCondition
    (Δ : ProfiniteFGroup.{u})
    (hChar : Δ.CharPerfectNumericalCondition) :
    Δ.IsPerfect := by
  rcases hChar with ⟨hZero, hNoCusps, hPair⟩
  let Q : Type u :=
    ProCGroups.FiniteStepSolvableQuotients.MaxSolvQuot Δ.carrier 1
  let q : Δ.carrier →ₜ* Q :=
    ProCGroups.FiniteStepSolvableQuotients.continuousToMaxSolvQuot
      Δ.carrier 1
  have hComm : Std.Commutative (fun a b : Q => a * b) := by
    refine (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := ProCGroups.FiniteStepSolvableQuotients.topDerivedTop
        Δ.carrier 1)).2 ?_
    change
      ⁅(⊤ : Subgroup Δ.carrier), (⊤ : Subgroup Δ.carrier)⁆ ≤
        ProCGroups.FiniteStepSolvableQuotients.topDerivedTop Δ.carrier 1
    change
      ⁅(⊤ : Subgroup Δ.carrier), (⊤ : Subgroup Δ.carrier)⁆ ≤
        (⁅(⊤ : Subgroup Δ.carrier), (⊤ : Subgroup Δ.carrier)⁆).topologicalClosure
    exact Subgroup.le_topologicalClosure
      (s := ⁅(⊤ : Subgroup Δ.carrier), (⊤ : Subgroup Δ.carrier)⁆)
  letI : CommGroup Q :=
    { inferInstanceAs (Group Q) with
      mul_comm := hComm.comm }
  have hInertia :
      ∀ i : Fin Δ.signature.numPeriods, q (Δ.inertia i) = 1 := by
    intro i
    exact
      commHom_inertia_eq_one_of_charPerfectNumericalCondition
        Δ ⟨hZero, hNoCusps, hPair⟩ q.toMonoidHom i
  have hq_eq_one : q = 1 := by
    apply
      ProCGroups.Generation.continuousMonoidHom_ext_of_topologicallyGenerates
        Δ.presentation_generates
    intro x hx
    rcases hx with hxABC | hxInertia
    · rcases hxABC with hxAB | hxCusp
      · rcases hxAB with hxA | hxB
        · rcases hxA with ⟨i, rfl⟩
          exfalso
          rw [hZero] at i
          exact Nat.not_lt_zero _ i.2
        · rcases hxB with ⟨i, rfl⟩
          exfalso
          rw [hZero] at i
          exact Nat.not_lt_zero _ i.2
      · rcases hxCusp with ⟨j, rfl⟩
        exfalso
        rw [hNoCusps] at j
        exact Nat.not_lt_zero _ j.2
    · rcases hxInertia with ⟨i, rfl⟩
      simpa using hInertia i
  apply le_antisymm
  · exact le_top
  · intro x _hx
    have hxq : q x = 1 := by
      simp only [ProCGroups.FiniteStepSolvableQuotients.closedDerivedSeries_succ,
  ProCGroups.FiniteStepSolvableQuotients.closedDerivedSeries_zero, hq_eq_one, ContinuousMonoidHom.one_toFun]
    exact
      (ProCGroups.FiniteStepSolvableQuotients.continuousToMaxSolvQuot_eq_one_iff
        (G := Δ.carrier) (m := 1) (x := x)).1 hxq

/-- Non-perfect compact zero-genus Fenchel groups have two periods with a common prime divisor.

This numerical extraction is used directly by the compact discrete bridge, so the bridge does not
need to prove non-perfectness again on the discrete presentation side. -/
theorem exists_prime_dvd_two_periods_of_isNonPerfect_zeroGenus_noCusps
    (Δ : ProfiniteFGroup.{u})
    (hNonPerfect : Δ.IsNonPerfect)
    (hZero : Δ.signature.orbitGenus = 0)
    (hNoCusps : Δ.signature.numCusps = 0) :
    ∃ p : ℕ, p.Prime ∧
      ∃ i j : Fin Δ.signature.numPeriods,
        i ≠ j ∧ p ∣ Δ.signature.periods i ∧
          p ∣ Δ.signature.periods j := by
  exact
    (not_pairwiseCoprimeFamily_iff_exists_prime_dvd_two
      (periods := Δ.signature.periods)).mp
      (by
        intro hPair
        exact hNonPerfect
          (isPerfect_of_charPerfectNumericalCondition Δ ⟨hZero, hNoCusps, hPair⟩))

/-- In the compact zero-genus non-perfect branch, fewer than three periods forces exactly two
periods.  This is the numerical boundary case used by the direct cyclic quotient construction. -/
theorem numPeriods_eq_two_of_isNonPerfect_zeroGenus_noCusps_not_three
    (Δ : ProfiniteFGroup.{u})
    (hNonPerfect : Δ.IsNonPerfect)
    (hZero : Δ.signature.orbitGenus = 0)
    (hNoCusps : Δ.signature.numCusps = 0)
    (hNotThree : ¬ 3 ≤ Δ.signature.numPeriods) :
    Δ.signature.numPeriods = 2 := by
  rcases
    exists_prime_dvd_two_periods_of_isNonPerfect_zeroGenus_noCusps
      Δ hNonPerfect hZero hNoCusps with
    ⟨_p, _hpPrime, i, j, hij, _hpi, _hpj⟩
  have hvne : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  have hi := i.2
  have hj := j.2
  omega

end ProfiniteFGroup

end FenchelNielsen
