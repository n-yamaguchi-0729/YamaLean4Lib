import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SlimnessAndTorsion
import ProCGroups.FiniteStepSolvableQuotients.Commutators.Basic
import CompletedGroupAlgebra.ProfiniteModules.FiniteGroupAlgebra.Functoriality
import FoxDifferential.Completed.ProCIntegerCoefficients.Core
import ProCGroups.Categorical.QuotientPullbackEquivalences
import ProCGroups.FreeProducts.UniversalProperty
import ProCGroups.FreeProC.Abelianization
import ProCGroups.FreeProC.SolvableQuotients
import ProCGroups.Generation.Basic
import ProCGroups.GroupTheory.Subgroups
import ProCGroups.Order.Basic
import CrowellExactSequence.Profinite.FiniteRank
import ReidemeisterSchreier.Profinite.OpenSubgroups.MinimalPower
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/Yama2026_Sections_1_And_2_1/main.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Yama2026: Section 1 and Subsection 2.1

This file is the complete Lean public module for the currently formalized part of the Yama2026
paper: Section 1 and Subsection 2.1. It intentionally keeps the theorem-numbered declarations in
this file, rather than hiding them behind section-named modules or wrapper-only imports.

The Section 1 part proves the free pro-`Σ` centralizer calculation, the completed abelianization
non-zero-divisor lemma, the center-freeness theorem for maximal solvable quotients of free
pro-`Σ` groups, and the slimness corollary. The Subsection 2.1 part records the
ab-torsion-freeness and ab-faithfulness consequences used later in the paper.
-/

universe u v w z

namespace CenterFreenessFiniteStepSolvable

open scoped BigOperators
open scoped Topology
open ProCGroups.FiniteStepSolvableQuotients
open ProCGroups.Abelian
open ProCGroups.FreeProC
open ProCGroups.GroupTheory
open ProCGroups.Generation
open ProCGroups.ProC
open CompletedGroupAlgebra

-- Local notation used only in this file to keep paper-facing statements readable.
local notation "Qm" => MaxSolvQuot
local notation "AbTop" => TopologicalAbelianization
local notation "SigmaGroup[" σ "]" => ProCGroups.FiniteGroupClass.sigmaGroup σ
local notation "ProSigmaGroup[" σ "]" => ProCGroups.ProC.IsProCGroup (SigmaGroup[σ])
local notation "IsFreeProSigmaProduct[" σ "]" =>
  ProCGroups.FreeProducts.IsFreeProCProduct
    (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[σ]))

local instance sigmaGroupVarietyFact (sigma : Set ℕ) :
    Fact (ProCGroups.FiniteGroupClass.Variety (SigmaGroup[sigma])) :=
  ⟨ProCGroups.FiniteGroupClass.sigmaGroup_variety sigma⟩

local instance sigmaGroupIsomClosedFact (sigma : Set ℕ) :
    Fact (ProCGroups.FiniteGroupClass.IsomClosed (SigmaGroup[sigma])) :=
  ⟨ProCGroups.FiniteGroupClass.sigmaGroup_isomClosed sigma⟩

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable [hCVariety : Fact (ProCGroups.FiniteGroupClass.Variety C)]
variable [hCIsomClosed : Fact (ProCGroups.FiniteGroupClass.IsomClosed C)]

variable {G Q F Ω A P H : Type u}
variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
variable [TopologicalSpace F] [Group F] [IsTopologicalGroup F]
variable [TopologicalSpace Ω] [Group Ω] [IsTopologicalGroup Ω]
variable [TopologicalSpace A] [Group A] [IsTopologicalGroup A]
variable [TopologicalSpace P] [Group P] [IsTopologicalGroup P]
variable [TopologicalSpace H] [Group H] [IsTopologicalGroup H]

private def cosetModuleAddEquiv
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ) (a : G₀) :
    ((G₀ ⧸ H) → ZMod K) ≃+
      ((G₀ ⧸ H) → ZMod K) where
  toFun f := fun q => f (a⁻¹ • q)
  invFun f := fun q => f (a • q)
  left_inv := by
    intro f
    ext q
    simp only [inv_smul_smul]
  right_inv := by
    intro f
    ext q
    simp only [smul_inv_smul]
  map_add' := by
    intro f h
    rfl

private def cosetModuleAction
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ) :
    G₀ × H →* MulAut (Multiplicative ((G₀ ⧸ H) → ZMod K)) where
  toFun p := (cosetModuleAddEquiv H K p.1).toMultiplicative
  map_one' := by
    ext f q
    simp only [cosetModuleAddEquiv, Prod.fst_one, inv_one, one_smul,
      AddEquiv.toMultiplicative_apply_apply, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.toMultiplicative_apply_apply, AddMonoidHom.coe_coe, AddEquiv.coe_mk,
      Equiv.coe_fn_mk, ofAdd_toAdd, MulAut.one_apply]
  map_mul' := by
    intro p q
    ext f x
    simp only [cosetModuleAddEquiv, Prod.fst_mul, mul_inv_rev, mul_smul,
      AddEquiv.toMultiplicative_apply_apply, AddEquiv.toAddMonoidHom_eq_coe,
      AddMonoidHom.toMultiplicative_apply_apply, AddMonoidHom.coe_coe, AddEquiv.coe_mk,
      Equiv.coe_fn_mk, toAdd_ofAdd, MulAut.mul_apply]

/-- The finite coset-module semidirect product used in Lemma 1.2 and Proposition 1.3.
This is kept as a type abbreviation because the full semidirect product type is repeated in
projection maps, cyclic maps, and the finite-discrete `ProC` target. -/
abbrev FreeprocenterCosetTarget
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ) :=
  Multiplicative ((G₀ ⧸ H) → ZMod K) ⋊[cosetModuleAction H K] (G₀ × H)

-- The semidirect targets are used only as finite discrete test groups in this file.
local instance
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ) :
    TopologicalSpace (FreeprocenterCosetTarget H K) :=
  ⊥

local instance
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ) :
    DiscreteTopology (FreeprocenterCosetTarget H K) :=
  ⟨rfl⟩

local instance
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ) :
    IsTopologicalGroup (FreeprocenterCosetTarget H K) := by
  infer_instance

private def cosetBasis
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ)
    [DecidableEq ((G₀ ⧸ H))] :
    (G₀ ⧸ H) → ZMod K :=
  Pi.single (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) (1 : ZMod K)

private theorem action_basis_eq_self_of_mem
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ)
    [DecidableEq ((G₀ ⧸ H))] {a : G₀} (ha : a ∈ H) :
    cosetModuleAddEquiv H K a (cosetBasis H K) = cosetBasis H K := by
  ext q
  change cosetBasis H K (a⁻¹ • q) = cosetBasis H K q
  let e : (G₀ ⧸ H) := QuotientGroup.mk (1 : G₀)
  have hbase : a • e = e := by
    have hstab : a ∈ MulAction.stabilizer G₀ e := by
      simpa [e, MulAction.stabilizer_quotient] using ha
    exact (MulAction.mem_stabilizer_iff).1 hstab
  have hbase_inv : a⁻¹ • e = e := by
    have hstab : a⁻¹ ∈ MulAction.stabilizer G₀ e := by
      simpa [e, MulAction.stabilizer_quotient] using H.inv_mem ha
    exact (MulAction.mem_stabilizer_iff).1 hstab
  by_cases hq : a⁻¹ • q = e
  · have hq' : q = e := by
      have := congrArg (fun r => a • r) hq
      simpa [e, smul_smul, hbase] using this
    rw [hq, hq']
  · have hne :
        a⁻¹ • q ≠ (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) := by
      simpa [e] using hq
    have hqbase : q ≠ (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) := by
      intro hqbase
      exact hq (by simpa [e, hqbase] using hbase_inv)
    change
      Pi.single (M := fun _ : (G₀ ⧸ H) => ZMod K)
          (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) (1 : ZMod K)
          (a⁻¹ • q) =
        Pi.single (M := fun _ : (G₀ ⧸ H) => ZMod K)
          (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) (1 : ZMod K) q
    rw [Pi.single_eq_of_ne (M := fun _ => ZMod K) hne,
      Pi.single_eq_of_ne (M := fun _ => ZMod K) hqbase]

private theorem mem_of_coset_centralizer_module_equation
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ)
    [DecidableEq ((G₀ ⧸ H))]
    {n : ℕ} (hn : (n : ZMod K) ≠ 0)
    (b : (G₀ ⧸ H) → ZMod K) (a h : G₀) (hh : h ∈ H)
    (heq :
      b + cosetModuleAddEquiv H K a (n • cosetBasis H K) =
        n • cosetBasis H K + cosetModuleAddEquiv H K h b) :
    a ∈ H := by
  have hcoord := congrFun heq (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H))
  have hfixed :
      (cosetModuleAddEquiv H K h b)
          (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) =
        b (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) := by
    have hbase :
        h⁻¹ • (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) =
          (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) :=
      by
        have hstab :
            h⁻¹ ∈ MulAction.stabilizer G₀
              (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) := by
          simpa [MulAction.stabilizer_quotient] using H.inv_mem hh
        exact (MulAction.mem_stabilizer_iff).1 hstab
    change b (h⁻¹ • (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H))) =
      b (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H))
    rw [hbase]
  have hleft :
      (cosetModuleAddEquiv H K a (n • cosetBasis H K))
          (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) = (n : ZMod K) := by
    have hcoord0 : b (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) +
          (cosetModuleAddEquiv H K a (n • cosetBasis H K))
            (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) =
        (n : ZMod K) +
          b (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) := by
      simpa only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, cosetBasis, Pi.single_eq_same,
        hfixed, nsmul_eq_mul, mul_one] using hcoord
    have hcoord' : b (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) +
          (cosetModuleAddEquiv H K a (n • cosetBasis H K))
            (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) =
        b (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) + (n : ZMod K) := by
      rw [add_comm (n : ZMod K)
        (b (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)))] at hcoord0
      exact hcoord0
    exact add_left_cancel hcoord'
  by_contra ha
  have hzero :
      (cosetModuleAddEquiv H K a (n • cosetBasis H K))
          (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) = 0 := by
    change (n • cosetBasis H K)
        (a⁻¹ • (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H))) = 0
    have hne :
        a⁻¹ • (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) ≠
          (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) := by
      intro hbase
      have hmem_inv : a⁻¹ ∈ H := by
        have hstab :
            a⁻¹ ∈ MulAction.stabilizer G₀
              (QuotientGroup.mk (1 : G₀) : (G₀ ⧸ H)) :=
          (MulAction.mem_stabilizer_iff).2 hbase
        simpa [MulAction.stabilizer_quotient] using hstab
      exact ha (by simpa using H.inv_mem hmem_inv)
    simp only [Pi.smul_apply, cosetBasis, Pi.single_eq_of_ne (M := fun _ => ZMod K) hne,
      nsmul_zero]
  exact hn (hleft.symm.trans hzero)

def cosetTestElement
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ)
    [DecidableEq ((G₀ ⧸ H))] (g : G₀) (hg : g ∈ H) :
    FreeprocenterCosetTarget H K :=
  ⟨Multiplicative.ofAdd (cosetBasis H K), (g, ⟨g, hg⟩)⟩

private def cosetTestPowerElement
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ)
    [DecidableEq ((G₀ ⧸ H))] (g : G₀) (hg : g ∈ H) (n : ℕ) :
    FreeprocenterCosetTarget H K :=
  ⟨Multiplicative.ofAdd (n • cosetBasis H K), (g ^ n, ⟨g ^ n, H.pow_mem hg n⟩)⟩

private theorem cosetTestElement_pow
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ)
    [DecidableEq ((G₀ ⧸ H))]
    (g : G₀) (hg : g ∈ H) (n : ℕ) :
    cosetTestElement H K g hg ^ n = cosetTestPowerElement H K g hg n := by
  induction n with
  | zero =>
      apply SemidirectProduct.ext
      · apply Multiplicative.ofAdd.injective
        ext q
        simp only [pow_zero, SemidirectProduct.one_left, toAdd_ofAdd, toAdd_one,
          Pi.zero_apply, cosetTestPowerElement, zero_nsmul, ofAdd_zero,
          SemidirectProduct.mk_eq_inl_mul_inr, map_one, one_mul, SemidirectProduct.left_inr]
      · change (1 : G₀ × H) = (g ^ 0, (⟨g ^ 0, H.pow_mem hg 0⟩ : H))
        ext
        · simp only [Prod.fst_one, pow_zero]
        · simp only [Prod.snd_one, pow_zero, OneMemClass.coe_one]
  | succ n ih =>
      rw [pow_succ, ih]
      apply SemidirectProduct.ext
      · apply Multiplicative.ofAdd.injective
        change
          n • cosetBasis H K +
              cosetModuleAddEquiv H K (g ^ n) (cosetBasis H K) =
            Nat.succ n • cosetBasis H K
        rw [action_basis_eq_self_of_mem H K (H.pow_mem hg n)]
        exact (succ_nsmul (cosetBasis H K) n).symm
      · ext <;> simp only [cosetTestPowerElement, nsmul_eq_mul,
          SemidirectProduct.mk_eq_inl_mul_inr, cosetTestElement, mul_assoc,
          SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr,
          one_mul, Prod.mk_mul_mk, MulMemClass.mk_mul_mk, Nat.cast_add, Nat.cast_one,
          pow_succ]

private theorem cosetTestElement_pow_eq_one_of
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ)
    [DecidableEq ((G₀ ⧸ H))]
    (g : G₀) (hg : g ∈ H) {s : ℕ}
    (hgs : g ^ s = 1) (hs : (s : ZMod K) = 0) :
    cosetTestElement H K g hg ^ s = 1 := by
  rw [cosetTestElement_pow H K g hg s]
  unfold cosetTestPowerElement
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (s • cosetBasis H K) = 1
    apply Multiplicative.ofAdd.injective
    ext q
    change (s • cosetBasis H K) q = 0
    simp only [Pi.smul_apply, nsmul_eq_mul, hs, zero_mul]
  · change ((g ^ s, (⟨g ^ s, H.pow_mem hg s⟩ : H)) : G₀ × H) = 1
    ext <;> assumption

private theorem centralizer_cosetTestPower_first_mem
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ)
    [DecidableEq ((G₀ ⧸ H))]
    {n : ℕ} (hn : (n : ZMod K) ≠ 0)
    {g : G₀} (hg : g ∈ H) (y : FreeprocenterCosetTarget H K)
    (hy : y * cosetTestPowerElement H K g hg n = cosetTestPowerElement H K g hg n * y) :
    y.right.1 ∈ H := by
  have hleft := congrArg (fun z : FreeprocenterCosetTarget H K => z.left.toAdd) hy
  have hmodule :
      y.left.toAdd + cosetModuleAddEquiv H K y.right.1 (n • cosetBasis H K) =
        n • cosetBasis H K + cosetModuleAddEquiv H K (g ^ n) y.left.toAdd :=
    by
      change
          y.left.toAdd +
              ((cosetModuleAction H K y.right)
                (Multiplicative.ofAdd (n • cosetBasis H K))).toAdd =
            (n • cosetBasis H K) +
              ((cosetModuleAction H K (g ^ n, ⟨g ^ n, H.pow_mem hg n⟩))
                y.left).toAdd at hleft
      simpa using hleft
  exact
    mem_of_coset_centralizer_module_equation H K hn y.left.toAdd y.right.1 (g ^ n)
      (H.pow_mem hg n) hmodule

/-- Lemma 1.2 in the paper, in the equivalent nat-power form used after choosing
`z τ^n z⁻¹ = τ^r`.

Here `H = Subgroup.zpowers g`, the target is
`(ZMod N)[G₀/H] ⋊ (G₀ × H)`, and `τ` is the element
`([H], (g, g))`.  If `z τ^n` is equal to a power of `τ` times `z`, and the image of
`n` in `ZMod N` is nonzero with `N ∣ orderOf g`, then the first projection of `z`
lies in `H`. -/
private theorem lemma_1_2_freeprocenter_coset_target_natPower
    {G₀ : Type u} [Group G₀] (g : G₀) (N n : ℕ)
    [DecidableEq ((G₀ ⧸ Subgroup.zpowers g))]
    (hN : N ∣ orderOf g) (hn : (n : ZMod N) ≠ 0)
    (z : FreeprocenterCosetTarget (Subgroup.zpowers g) N)
    (hz :
      ∃ r : ℕ,
        z * (cosetTestElement (Subgroup.zpowers g) N g
              (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩)) ^ n =
          (cosetTestElement (Subgroup.zpowers g) N g
              (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩)) ^ r * z) :
    z.right.1 ∈ Subgroup.zpowers g := by
  let H : Subgroup G₀ := Subgroup.zpowers g
  let hg : g ∈ H := by
    dsimp [H]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩
  let τ : FreeprocenterCosetTarget H N := cosetTestElement H N g hg
  change z.right.1 ∈ H
  rcases hz with ⟨r, hzr⟩
  change z * τ ^ n = τ ^ r * z at hzr
  have hzr' :
      z * cosetTestPowerElement H N g hg n =
        cosetTestPowerElement H N g hg r * z := by
    simpa [τ, cosetTestElement_pow] using hzr
  have hright := congrArg (fun y : FreeprocenterCosetTarget H N => y.right) hzr'
  have hrightH := congrArg Prod.snd hright
  change
      z.right.2 * (⟨g ^ n, H.pow_mem hg n⟩ : H) =
        (⟨g ^ r, H.pow_mem hg r⟩ : H) * z.right.2 at hrightH
  letI : IsMulCommutative H := by
    dsimp [H]
    infer_instance
  have hHpow :
      (⟨g ^ n, H.pow_mem hg n⟩ : H) =
        (⟨g ^ r, H.pow_mem hg r⟩ : H) := by
    rw [mul_comm z.right.2 (⟨g ^ n, H.pow_mem hg n⟩ : H)] at hrightH
    exact mul_right_cancel hrightH
  have hpow_g : g ^ n = g ^ r := congrArg Subtype.val hHpow
  have hmod_order :
      (n : ℤ) ≡ (r : ℤ) [ZMOD (orderOf g : ℤ)] := by
    exact
      (zpow_eq_zpow_iff_modEq (x := g) (m := n) (n := r)).mp (by
        simpa only [zpow_natCast] using hpow_g)
  have hmod_N :
      (n : ℤ) ≡ (r : ℤ) [ZMOD (N : ℤ)] := by
    exact Int.ModEq.of_dvd (Int.ofNat_dvd.mpr hN) hmod_order
  have hcast : (n : ZMod N) = (r : ZMod N) := by
    have hcastInt : ((n : ℤ) : ZMod N) = ((r : ℤ) : ZMod N) :=
      (ZMod.intCast_eq_intCast_iff (n : ℤ) (r : ℤ) N).2 hmod_N
    simpa using hcastInt
  have hleft := congrArg (fun y : FreeprocenterCosetTarget H N => y.left.toAdd) hzr'
  have hmodule0 :
      z.left.toAdd + cosetModuleAddEquiv H N z.right.1 (n • cosetBasis H N) =
        r • cosetBasis H N + cosetModuleAddEquiv H N (g ^ r) z.left.toAdd := by
    change
        z.left.toAdd +
            ((cosetModuleAction H N z.right)
              (Multiplicative.ofAdd (n • cosetBasis H N))).toAdd =
          (r • cosetBasis H N) +
            ((cosetModuleAction H N (g ^ r, ⟨g ^ r, H.pow_mem hg r⟩))
              z.left).toAdd at hleft
    simpa using hleft
  have hbasis : r • cosetBasis H N = n • cosetBasis H N := by
    ext q
    simp only [Pi.smul_apply, nsmul_eq_mul]
    rw [hcast.symm]
  exact
    mem_of_coset_centralizer_module_equation H N hn z.left.toAdd z.right.1
      (g ^ r) (H.pow_mem hg r) (by simpa [hbasis] using hmodule0)

/-- Lemma 1.2 in the paper: if `z τ^n z⁻¹` lies in the cyclic subgroup generated by
`τ = ([H], (g, g))`, then the first projection of `z` lies in `H = Subgroup.zpowers g`. -/
theorem lemma_1_2_freeprocenter_coset_target
    {G₀ : Type u} [Group G₀] (g : G₀) (N n : ℕ)
    [DecidableEq ((G₀ ⧸ Subgroup.zpowers g))]
    (hfin : IsOfFinOrder g) (hN : N ∣ orderOf g) (hn : (n : ZMod N) ≠ 0)
    (z : FreeprocenterCosetTarget (Subgroup.zpowers g) N)
    (hz :
      let τ := cosetTestElement (Subgroup.zpowers g) N g
        (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩)
      z * τ ^ n * z⁻¹ ∈ Subgroup.zpowers τ) :
    z.right.1 ∈ Subgroup.zpowers g := by
  let H : Subgroup G₀ := Subgroup.zpowers g
  let hg : g ∈ H := by
    dsimp [H]
    exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩
  let τ : FreeprocenterCosetTarget H N := cosetTestElement H N g hg
  change
    z.right.1 ∈ H
  change z * τ ^ n * z⁻¹ ∈ Subgroup.zpowers τ at hz
  have hcastOrder : (orderOf g : ZMod N) = 0 :=
    (ZMod.natCast_eq_zero_iff (orderOf g) N).2 hN
  have hτpow : τ ^ orderOf g = 1 :=
    cosetTestElement_pow_eq_one_of H N g hg (pow_orderOf_eq_one g) hcastOrder
  have hτfin : IsOfFinOrder τ :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf g, hfin.orderOf_pos, hτpow⟩
  rcases (hτfin.mem_powers_iff_mem_zpowers).2 hz with ⟨r, hr⟩
  have hzr : z * τ ^ n = τ ^ r * z := by
    calc
      z * τ ^ n = (z * τ ^ n * z⁻¹) * z := by simp only [mul_assoc, inv_mul_cancel, mul_one]
      _ = τ ^ r * z := by rw [← hr]
  exact
    lemma_1_2_freeprocenter_coset_target_natPower g N n hN hn z ⟨r, by
      change z * τ ^ n = τ ^ r * z
      exact hzr⟩

private def cosetTargetTopLeftHom
    {G₀ : Type u} [Group G₀] (H : Subgroup G₀) (K : ℕ) :
    FreeprocenterCosetTarget H K →* G₀ where
  toFun z := z.right.1
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem cosetTarget_topDerivedTop_eq_bot_of_base
    {G₀ : Type u} [TopologicalSpace G₀] [Group G₀] [IsTopologicalGroup G₀] [T1Space G₀]
    (H : Subgroup G₀) (K : ℕ) [IsMulCommutative H]
    {m : ℕ} (hm : 2 ≤ m)
    (hG : topDerivedTop G₀ (m - 1) = (⊥ : Subgroup G₀)) :
    topDerivedTop (FreeprocenterCosetTarget H K) m = ⊥ := by
  let T : Type u := FreeprocenterCosetTarget H K
  let topLeftT : T →* G₀ := cosetTargetTopLeftHom H K
  let rightSubT : T →* H :=
    { toFun := fun z => z.right.2
      map_one' := rfl
      map_mul' := by
        intro _ _
        rfl }
  let topLeftTₜ : T →ₜ* G₀ :=
    { toMonoidHom := topLeftT
      continuous_toFun := continuous_of_discreteTopology }
  let rightSubTₜ : T →ₜ* H :=
    { toMonoidHom := rightSubT
      continuous_toFun := continuous_of_discreteTopology }
  let D : Subgroup T := topDerivedTop T (m - 1)
  have hD_left : D ≤ topLeftT.ker := by
    intro z hz
    have hzG : topLeftT z ∈ topDerivedTop G₀ (m - 1) :=
      (topDerivedTop_le_comap (f := topLeftTₜ) (m := m - 1)) hz
    rw [hG] at hzG
    exact (MonoidHom.mem_ker).2 (by simpa using hzG)
  have hm_pred : 1 ≤ m - 1 := by omega
  letI : CommGroup H := inferInstance
  have hH : topDerivedTop H (m - 1) = (⊥ : Subgroup H) :=
    topDerivedTop_eq_bot_of_commGroup hm_pred
  have hD_right : D ≤ rightSubT.ker := by
    intro z hz
    have hzH : rightSubT z ∈ topDerivedTop H (m - 1) :=
      (topDerivedTop_le_comap (f := rightSubTₜ) (m := m - 1)) hz
    rw [hH] at hzH
    exact (MonoidHom.mem_ker).2 (by simpa using hzH)
  have commutator_eq_one_of_right_eq_one :
      ∀ {z w : FreeprocenterCosetTarget H K}, z.right = 1 → w.right = 1 → ⁅z, w⁆ = 1 := by
    intro z w hz hw
    apply SemidirectProduct.ext
    · simp only [commutatorElement_def, SemidirectProduct.mul_left, hz, map_one,
        MulAut.one_apply, SemidirectProduct.mul_right, hw, mul_one,
        SemidirectProduct.inv_left, inv_one, mul_inv_cancel_comm,
        SemidirectProduct.inv_right, mul_inv_cancel, SemidirectProduct.one_left]
    · simp only [commutatorElement_def, SemidirectProduct.mul_right, hz, hw, mul_one,
        SemidirectProduct.inv_right, inv_one, SemidirectProduct.one_right]
  have hcomm : ⁅D, D⁆ ≤ (⊥ : Subgroup T) := by
    rw [Subgroup.commutator_le]
    intro z hz w hw
    have hzL := (MonoidHom.mem_ker).1 (hD_left hz)
    have hzR := (MonoidHom.mem_ker).1 (hD_right hz)
    have hwL := (MonoidHom.mem_ker).1 (hD_left hw)
    have hwR := (MonoidHom.mem_ker).1 (hD_right hw)
    have hzRight : z.right = 1 := Prod.ext hzL hzR
    have hwRight : w.right = 1 := Prod.ext hwL hwR
    have hzw : ⁅z, w⁆ = (1 : T) :=
      commutator_eq_one_of_right_eq_one hzRight hwRight
    simpa [Subgroup.mem_bot] using hzw
  have hclosed : IsClosed (((⊥ : Subgroup T) : Set T)) := by
    exact isClosed_discrete _
  have hclosedComm : closedCommutator D D ≤ (⊥ : Subgroup T) := by
    exact Subgroup.topologicalClosure_minimal ⁅D, D⁆ hcomm hclosed
  have hmEq : m = (m - 1) + 1 := (Nat.sub_add_cancel (le_trans (by decide : 1 ≤ 2) hm)).symm
  apply le_antisymm ?_ bot_le
  rw [hmEq, topDerivedTop_succ]
  exact hclosedComm

private theorem cosetTarget_isProC_sigmaGroup
    {sigmaSet : Set ℕ} {G₀ : Type u} [Group G₀]
    (H : Subgroup G₀) {ℓ r : ℕ} [Fact ℓ.Prime]
    (hG₀ : ProCGroups.FiniteGroupClass.sigmaGroup sigmaSet G₀)
    (hℓsigma : ℓ ∈ sigmaSet) :
    (ProCGroups.ProC.finiteGroupClassProCPredicate
      (ProCGroups.FiniteGroupClass.sigmaGroup sigmaSet))
        (G := FreeprocenterCosetTarget H (ℓ ^ r)) := by
  classical
  letI : Finite G₀ := hG₀.1
  let hH : ProCGroups.FiniteGroupClass.sigmaGroup sigmaSet H :=
    (ProCGroups.FiniteGroupClass.sigmaGroup_subgroupClosed sigmaSet) H hG₀
  letI : Finite H := hH.1
  letI : Finite ((G₀ ⧸ H)) := inferInstance
  have hK :
      ProCGroups.FiniteGroupClass.IsSigmaNumber sigmaSet (ℓ ^ r) :=
    ProCGroups.FiniteGroupClass.IsSigmaNumber.prime_pow_of_mem
      (sigma := sigmaSet) hℓsigma (Fact.out : ℓ.Prime)
  have hZ :
      ProCGroups.FiniteGroupClass.IsSigmaNumber sigmaSet (Nat.card (ZMod (ℓ ^ r))) := by
    simpa [Nat.card_zmod] using hK
  have hM :
      ProCGroups.FiniteGroupClass.IsSigmaNumber sigmaSet
        (Nat.card ((G₀ ⧸ H) → ZMod (ℓ ^ r))) := by
    letI : Fintype ((G₀ ⧸ H)) := Fintype.ofFinite ((G₀ ⧸ H))
    simpa [Nat.card_pi] using
      ProCGroups.FiniteGroupClass.IsSigmaNumber.prod (sigma := sigmaSet) Finset.univ
        (fun _ : (G₀ ⧸ H) => Nat.card (ZMod (ℓ ^ r))) (fun _ _ => hZ)
  have hMmul :
      ProCGroups.FiniteGroupClass.IsSigmaNumber sigmaSet
        (Nat.card (Multiplicative ((G₀ ⧸ H) → ZMod (ℓ ^ r)))) := by
    simpa using hM
  have hRight :
      ProCGroups.FiniteGroupClass.IsSigmaNumber sigmaSet (Nat.card (G₀ × H)) := by
    rw [Nat.card_prod]
    exact ProCGroups.FiniteGroupClass.IsSigmaNumber.mul hG₀.2 hH.2
  letI : Finite (Multiplicative ((G₀ ⧸ H) → ZMod (ℓ ^ r))) := inferInstance
  letI : Finite (G₀ × H) := inferInstance
  letI : Finite (FreeprocenterCosetTarget H (ℓ ^ r)) :=
    Finite.of_equiv
      (Multiplicative ((G₀ ⧸ H) → ZMod (ℓ ^ r)) × (G₀ × H))
      (SemidirectProduct.equivProd
        (N := Multiplicative ((G₀ ⧸ H) → ZMod (ℓ ^ r)))
        (G := G₀ × H)
        (φ := cosetModuleAction H (ℓ ^ r))).symm
  have hTclass :
      ProCGroups.FiniteGroupClass.sigmaGroup sigmaSet
        (FreeprocenterCosetTarget H (ℓ ^ r)) := by
    refine ⟨inferInstance, ?_⟩
    rw [SemidirectProduct.card]
    exact ProCGroups.FiniteGroupClass.IsSigmaNumber.mul hMmul hRight
  exact
    ProCGroups.ProC.IsProCGroup.of_finite_discrete
      (C := ProCGroups.FiniteGroupClass.sigmaGroup sigmaSet)
      (G := FreeprocenterCosetTarget H (ℓ ^ r))
      (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed sigmaSet)
      hTclass

private def topLeftOnlyCosetTargetHom
    {G₀ H₀ : Type u} [Group G₀] [Group H₀] {H : Subgroup G₀} (K : ℕ)
    (q : H₀ →* G₀) :
    H₀ →* FreeprocenterCosetTarget H K where
  toFun h := ⟨Multiplicative.ofAdd 0, (q h, 1)⟩
  map_one' := by
    apply SemidirectProduct.ext
    · rfl
    · ext <;> simp
  map_mul' a b := by
    apply SemidirectProduct.ext
    · apply Multiplicative.ofAdd.injective
      ext x
      simp only [ofAdd_zero, toAdd_ofAdd, toAdd_one, Pi.zero_apply, SemidirectProduct.mk_eq_inl_mul_inr, map_one,
  one_mul, SemidirectProduct.mul_left, SemidirectProduct.left_inr, SemidirectProduct.right_inr, mul_one]
    · ext <;> simp

private noncomputable def cosetTargetCyclicHom
    {G₀ : Type u} [Group G₀] (K : ℕ) (g : G₀)
    [DecidableEq ((G₀ ⧸ Subgroup.zpowers g))]
    (hK : K ∣ orderOf g) :
    ↥(Subgroup.zpowers g) →*
      FreeprocenterCosetTarget (Subgroup.zpowers g) K := by
  let H : Subgroup G₀ := Subgroup.zpowers g
  let gH : H := ⟨g, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩⟩
  let targetGen : FreeprocenterCosetTarget H K :=
    cosetTestElement H K g (show g ∈ H by exact gH.2)
  have hcast : (orderOf g : ZMod K) = 0 := (ZMod.natCast_eq_zero_iff (orderOf g) K).2 hK
  have hpow : targetGen ^ orderOf g = 1 :=
    cosetTestElement_pow_eq_one_of H K g (show g ∈ H by exact gH.2)
      (pow_orderOf_eq_one g) hcast
  have htargetOrder : orderOf targetGen ∣ orderOf g :=
    (orderOf_dvd_iff_pow_eq_one (x := targetGen) (n := orderOf g)).2 hpow
  have hcycOrder : orderOf gH = orderOf g := by
    simp only [Subgroup.orderOf_mk, gH]
  have htargetOrder' : orderOf targetGen ∣ orderOf gH := by
    simpa [hcycOrder] using htargetOrder
  have hgen : ∀ z : H, z ∈ Subgroup.zpowers gH := by
    simpa [H, gH] using
      zpowers_subtype_topologically_generated_by_generator (G₀ := G₀) g
  exact
    monoidHomOfForallMemZpowers
      (G := H) (G' := FreeprocenterCosetTarget H K)
      (g := gH) (g' := targetGen) hgen htargetOrder'

private theorem quotient_closedSubgroup_image_mem_of_cosetTarget
    {Q G₀ : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q] [Group G₀]
    (q : Q →* G₀) (x y : Q) (n : ℤ)
    (K : ℕ) [DecidableEq ((G₀ ⧸ Subgroup.zpowers (q x)))]
    (hn : (n.natAbs : ZMod K) ≠ 0)
    (ψ : Q →* FreeprocenterCosetTarget (Subgroup.zpowers (q x)) K)
    (hleftψ : (cosetTargetTopLeftHom (Subgroup.zpowers (q x)) K).comp ψ = q)
    (hψx :
      ψ x =
        cosetTestElement (Subgroup.zpowers (q x)) K (q x)
          (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩))
    (hy : y ∈ centralizerOf (x ^ n)) :
    q y ∈
      ((closedSubgroupGenerated ({x} : Set Q) : ClosedSubgroup Q) :
        Subgroup Q).map q := by
  have hn_ne_zero : n ≠ 0 := by
    intro h0
    exact hn (by simp only [h0, Int.natAbs_zero, Nat.cast_zero])
  have hyψz : ψ y ∈ centralizerOf ((ψ x) ^ n) := by
    rw [mem_centralizerOf_iff] at hy ⊢
    calc
      ψ y * (ψ x) ^ n = ψ y * ψ (x ^ n) := by simp only [map_zpow]
      _ = ψ (y * x ^ n) := by simp only [map_zpow, map_mul]
      _ = ψ (x ^ n * y) := by rw [hy]
      _ = ψ (x ^ n) * ψ y := by simp only [map_mul, map_zpow]
      _ = (ψ x) ^ n * ψ y := by simp only [map_zpow]
  have hyψNat :
      ψ y ∈ centralizerOf ((ψ x) ^ (n.natAbs : ℤ)) :=
    mem_centralizerOf_zpow_natAbs_of_mem_zpow hn_ne_zero hyψz
  have hyψNat' :
      ψ y ∈ centralizerOf ((ψ x) ^ n.natAbs) := by
    rw [zpow_natCast] at hyψNat
    exact hyψNat
  have hyTarget :
      ψ y ∈ centralizerOf
        (cosetTestPowerElement (Subgroup.zpowers (q x)) K (q x)
          (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩) n.natAbs) := by
    rw [hψx, cosetTestElement_pow] at hyψNat'
    exact hyψNat'
  have hcyc :
      (ψ y).right.1 ∈ Subgroup.zpowers (q x) :=
    centralizer_cosetTestPower_first_mem
      (Subgroup.zpowers (q x)) K (n := n.natAbs) hn (g := q x)
      (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩) (ψ y)
      (mem_centralizerOf_iff.mp hyTarget)
  have hqy : q y ∈ Subgroup.zpowers (q x) := by
    have hleft_y := congrArg (fun f : Q →* G₀ => f y) hleftψ
    change (ψ y).right.1 = q y at hleft_y
    simpa [hleft_y.symm] using hcyc
  exact zpowers_image_le_closedSubgroupGenerated_map q x hqy

omit [IsTopologicalGroup P] in
/-- In the free product quotient used in `freeprocenter`, a nontrivial power from the procyclic
left factor does not lie in the previous derived subgroup. -/
private theorem free_proC_product_left_power_not_mem_lastDerived
    {sigma : Set ℕ}
    (ιC : A →ₜ* Ω) (ιP : P →ₜ* Ω)
    (hOmega : IsFreeProSigmaProduct[sigma] ιC ιP)
    (hAProSigma : ProSigmaGroup[sigma] A)
    (hAprocyclic : ProCGroups.ProC.IsProcyclicGroup A)
    (x : A) (m : ℕ) (hm : 2 ≤ m) (n : ℤ) (hn : x ^ n ≠ 1) :
    let qx : MaxSolvQuot Ω m := continuousToMaxSolvQuot Ω m (ιC x)
    qx ^ n ∉ topDerivedTop (MaxSolvQuot Ω m) (m - 1) := by
  intro qx hmem
  let rΩA : Ω →ₜ* A :=
    hOmega.lift hAProSigma (ContinuousMonoidHom.id A) (1 : P →ₜ* A)
  have hr_left : rΩA.comp ιC = ContinuousMonoidHom.id A := by
    exact hOmega.lift_left hAProSigma (ContinuousMonoidHom.id A) (1 : P →ₜ* A)
  have hm_pos : 1 ≤ m := le_trans (by decide : 1 ≤ 2) hm
  have hDmA : topDerivedTop A m = (⊥ : Subgroup A) :=
    topDerivedTop_eq_bot_of_procyclic hAprocyclic hm_pos
  have hker : topDerivedTop Ω m ≤ (rΩA : Ω →* A).ker := by
    intro z hz
    have hzA : rΩA z ∈ topDerivedTop A m :=
      (topDerivedTop_le_comap (f := rΩA) m) hz
    rw [hDmA] at hzA
    simpa using hzA
  let rQ : MaxSolvQuot Ω m →ₜ* A :=
    QuotientGroup.liftₜ (topDerivedTop Ω m) rΩA hker
  have hm_pred : 1 ≤ m - 1 := by
    simpa using Nat.sub_le_sub_right hm 1
  have hDpredA : topDerivedTop A (m - 1) = (⊥ : Subgroup A) :=
    topDerivedTop_eq_bot_of_procyclic hAprocyclic hm_pred
  have hmemA : rQ (qx ^ n) ∈ topDerivedTop A (m - 1) :=
    (topDerivedTop_le_comap (f := rQ) (m - 1)) hmem
  rw [hDpredA] at hmemA
  have hrqx : rQ qx = x := by
    change rΩA (ιC x) = x
    have h := congrArg (fun f : A →ₜ* A => f x) hr_left
    simpa using h
  have hxone : x ^ n = 1 := by
    have hmap : rQ (qx ^ n) = x ^ n := by
      simp only [map_zpow, hrqx]
    change rQ (qx ^ n) = 1 at hmemA
    simpa [hmap] using hmemA
  exact hn hxone

omit [IsTopologicalGroup A] [IsTopologicalGroup P] in
/-- Maximal solvable quotients of a free pro-`Σ` product remain pro-`Σ`. -/
private theorem maxSolvQuot_isProC_sigmaGroup_of_freeProCProduct
    {sigma : Set ℕ}
    (ιC : A →ₜ* Ω) (ιP : P →ₜ* Ω)
    (hOmega : IsFreeProSigmaProduct[sigma] ιC ιP)
    (m : ℕ) :
    ProSigmaGroup[sigma] (MaxSolvQuot Ω m) := by
  exact
    ProCGroups.ProC.quotient_closedNormalSubgroup
      (C := SigmaGroup[sigma])
      (ProCGroups.FiniteGroupClass.sigmaGroup_isomClosed sigma)
      (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed sigma)
      hOmega.isProC
      (topDerivedTop Ω m)
      (show IsClosed ((topDerivedTop Ω m : Subgroup Ω) : Set Ω) by infer_instance)

omit [IsTopologicalGroup A] [IsTopologicalGroup P] in
/-- Open normal quotients of `Q_m(Ω)` in the free pro-`Σ` product setting are finite
`Σ`-groups. -/
private theorem maxSolvQuot_openQuotient_sigmaGroup_of_freeProCProduct
    {sigma : Set ℕ}
    (ιC : A →ₜ* Ω) (ιP : P →ₜ* Ω)
    (hOmega : IsFreeProSigmaProduct[sigma] ιC ιP)
    (m : ℕ) (V : OpenNormalSubgroup (MaxSolvQuot Ω m)) :
    SigmaGroup[sigma] ((MaxSolvQuot Ω m) ⧸ (V : Subgroup (MaxSolvQuot Ω m))) := by
  exact
    ProCGroups.ProC.IsProCGroup.quotient_mem
      (C := SigmaGroup[sigma])
      (ProCGroups.FiniteGroupClass.sigmaGroup_formation sigma)
      (maxSolvQuot_isProC_sigmaGroup_of_freeProCProduct
        (sigma := sigma) ιC ιP hOmega m)
      V

omit [IsTopologicalGroup P] in
/-- Finite coset-module input for Proposition `freeprocenter`.

For every open normal quotient of `Q_m(Ω)`, this chooses a smaller quotient which still detects
`x^n`, kills the last derived subgroup, and satisfies the cyclic containment obtained from the
permutation module on the left cosets of the cyclic image of `x`. -/
private theorem free_proC_product_centralizer_cofinal_coset_lift
    {sigma : Set ℕ}
    (ιC : A →ₜ* Ω) (ιP : P →ₜ* Ω)
    (hOmega : IsFreeProSigmaProduct[sigma] ιC ιP)
    (hAProSigma : ProSigmaGroup[sigma] A)
    (x : A) (hxgen : ProCGroups.Generation.TopologicallyGenerates (G := A) ({x} : Set A))
    (m : ℕ) (hm : 2 ≤ m) (n : ℤ) (hn : x ^ n ≠ 1) :
    ∀ U : OpenNormalSubgroup (MaxSolvQuot Ω m),
      ∃ W : OpenNormalSubgroup (MaxSolvQuot Ω m),
        (W : Subgroup (MaxSolvQuot Ω m)) ≤ (U : Subgroup (MaxSolvQuot Ω m)) ∧
        let qx : MaxSolvQuot Ω m := continuousToMaxSolvQuot Ω m (ιC x)
        let K : Subgroup (MaxSolvQuot Ω m) := topDerivedTop (MaxSolvQuot Ω m) (m - 1)
        let V : OpenNormalSubgroup (MaxSolvQuot Ω m) := openNormalSubgroup_sup_normal K W
        ∀ y : MaxSolvQuot Ω m, y ∈ centralizerOf (qx ^ n) →
          QuotientGroup.mk' (V : Subgroup (MaxSolvQuot Ω m)) y ∈
            ((closedSubgroupGenerated ({qx} : Set (MaxSolvQuot Ω m)) :
                ClosedSubgroup (MaxSolvQuot Ω m)) :
              Subgroup (MaxSolvQuot Ω m)).map
                (QuotientGroup.mk' (V : Subgroup (MaxSolvQuot Ω m))) := by
  /-
  The finite-stage argument uses the quotient `G₀` of `Q_m(Ω)`, the cyclic subgroup
  `H = <ρ(x)>`, and the permutation module `(Z / ℓ^r Z)[G₀/H]`.  The chosen prime
  power divides the order of `ρ(x)` but not `n`, so the coset coefficient of `[H]`
  detects whether the first projection of a centralizing element lies in `H`.
  -/
  have hAprocyclic : ProCGroups.ProC.IsProcyclicGroup A := by
    exact
      ProCGroups.ProC.isProcyclicGroup_of_topologicallyGenerates_singleton
      (G := A) hAProSigma.isProfinite hxgen
  letI : CompactSpace A := hAProSigma.isProfinite.compactSpace
  letI : T2Space A := hAProSigma.isProfinite.t2Space
  letI : TotallyDisconnectedSpace A := hAProSigma.isProfinite.totallyDisconnectedSpace
  let qx : MaxSolvQuot Ω m := continuousToMaxSolvQuot Ω m (ιC x)
  let K : Subgroup (MaxSolvQuot Ω m) := topDerivedTop (MaxSolvQuot Ω m) (m - 1)
  have hnotK : qx ^ n ∉ K := by
    change qx ^ n ∉ topDerivedTop (MaxSolvQuot Ω m) (m - 1)
    exact
      free_proC_product_left_power_not_mem_lastDerived
        (sigma := sigma) ιC ιP hOmega hAProSigma hAprocyclic x m hm n hn
  let Q : Type u := MaxSolvQuot Ω m
  let hΩprof : ProCGroups.IsProfiniteGroup Ω :=
    ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate
      (ProCGroups.FiniteGroupClass.sigmaGroup sigma) hOmega.isProC
  let hQprof : ProCGroups.IsProfiniteGroup Q := by
    simpa [Q, MaxSolvQuot] using
      (ProCGroups.Generation.isProfinite_quotient_closedNormal
        (G := Ω) hΩprof
        (show IsClosed ((topDerivedTop Ω m : Subgroup Ω) : Set Ω) by infer_instance))
  letI : CompactSpace Q := hQprof.compactSpace
  letI : T2Space Q := hQprof.t2Space
  letI : TotallyDisconnectedSpace Q := hQprof.totallyDisconnectedSpace
  haveI : K.Normal := by
    dsimp [K]
    infer_instance
  have hKclosed : IsClosed (K : Set (MaxSolvQuot Ω m)) := by
    dsimp [K]
    infer_instance
  refine
    cofinal_openNormal_cyclic_containment_of_finite_lift
      (Q := Q) qx n K hKclosed hnotK ?_
  intro W hdetect
  change
    let V : OpenNormalSubgroup Q := openNormalSubgroup_sup_normal K W
    ∀ y : Q, y ∈ centralizerOf (qx ^ n) →
      QuotientGroup.mk' (V : Subgroup Q) y ∈
        ((closedSubgroupGenerated ({qx} : Set Q) : ClosedSubgroup Q) :
          Subgroup Q).map (QuotientGroup.mk' (V : Subgroup Q))
  let V : OpenNormalSubgroup Q := openNormalSubgroup_sup_normal K W
  let G₀ : Type u := Q ⧸ (V : Subgroup Q)
  let q : Q →* G₀ := QuotientGroup.mk' (V : Subgroup Q)
  let g : G₀ := q qx
  have hG₀pi : SigmaGroup[sigma] G₀ := by
    simpa [Q, G₀, V] using
      maxSolvQuot_openQuotient_sigmaGroup_of_freeProCProduct
        (sigma := sigma) ιC ιP hOmega m V
  letI : Finite G₀ := hG₀pi.1
  letI : Fintype G₀ := Fintype.ofFinite G₀
  letI : DecidableEq G₀ := Classical.decEq G₀
  have hgpow_ne : g ^ n ≠ 1 := by
    intro hg
    apply hdetect
    change qx ^ n ∈ (V : Subgroup Q)
    exact (QuotientGroup.eq_one_iff (N := (V : Subgroup Q)) (qx ^ n)).1 (by
      simpa [q, g, map_zpow] using hg)
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    apply hgpow_ne
    simp only [hn0, zpow_zero]
  have hg_finiteOrder : IsOfFinOrder g := isOfFinOrder_of_finite g
  have horder_ne : orderOf g ≠ 0 :=
    Nat.ne_of_gt ((orderOf_pos_iff).2 hg_finiteOrder)
  letI : NeZero (orderOf g) := ⟨horder_ne⟩
  rcases
      ProCGroups.FiniteGroupClass.exists_prime_power_orderOf_gt_padicValNat_of_zpow_ne_one
        (sigma := sigma) hG₀pi hgpow_ne with
    ⟨ℓ, r, hℓprime, hrpos, hℓsigma, hpadicInt, hℓr_order⟩
  have hpadic : padicValNat ℓ n.natAbs < r := by
    simpa using hpadicInt
  letI : Fact ℓ.Prime := ⟨hℓprime⟩
  letI : Fact (0 < r) := ⟨hrpos⟩
  have hnAbs_ne : n.natAbs ≠ 0 := by
    exact Int.natAbs_ne_zero.mpr hn_ne_zero
  have hn_not_dvd : ¬ ℓ ^ r ∣ n.natAbs := by
    intro hdvd
    have hle :
        r ≤ padicValNat ℓ n.natAbs :=
      (padicValNat_dvd_iff_le (p := ℓ) (a := n.natAbs) (n := r) hnAbs_ne).1 hdvd
    exact (not_le_of_gt hpadic) hle
  have hnCoeff : (n.natAbs : ZMod (ℓ ^ r)) ≠ 0 := by
    intro hzero
    exact hn_not_dvd ((ZMod.natCast_eq_zero_iff n.natAbs (ℓ ^ r)).1 hzero)
  let H : Subgroup G₀ := Subgroup.zpowers g
  let T : Type u := FreeprocenterCosetTarget H (ℓ ^ r)
  letI : DecidableEq ((G₀ ⧸ H)) := Classical.decEq _
  letI : IsMulCommutative H := by
    dsimp [H]
    infer_instance
  let πΩ : Ω →ₜ* Q := continuousToMaxSolvQuot Ω m
  let qΩ : Ω →* G₀ := q.comp πΩ
  have hqΩcont : Continuous qΩ := by
    simpa [qΩ, πΩ, q] using
      (continuous_quotient_mk'.comp
        (continuousToMaxSolvQuot Ω m).continuous_toFun :
        Continuous (fun z : Ω => QuotientGroup.mk' (V : Subgroup Q)
          (continuousToMaxSolvQuot Ω m z)))
  have hqΩ_mem_zpowers : ∀ a : A, qΩ (ιC a) ∈ H := by
    intro a
    simpa [Q, qΩ, πΩ, q, qx, g, H] using
      (maxSolvQuot_leftFactor_image_mem_zpowers
        (q := q) (hq := (continuous_quotient_mk' : Continuous q))
        ιC (x := x) (a := a) hxgen)
  let qAcyc : A →* H :=
    { toFun := fun a =>
        ⟨qΩ (ιC a), hqΩ_mem_zpowers a⟩
      map_one' := by
        apply Subtype.ext
        simp only [map_one, OneMemClass.coe_one, qΩ]
      map_mul' := by
        intro a b
        apply Subtype.ext
        simp only [map_mul, MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, MulMemClass.mk_mul_mk, qΩ]}
  have hqAcyc_cont : Continuous qAcyc := by
    change Continuous (fun a : A => (⟨qΩ (ιC a), hqΩ_mem_zpowers a⟩ : H))
    exact Continuous.subtype_mk (hqΩcont.comp ιC.continuous_toFun) hqΩ_mem_zpowers
  let qAcycT : A →ₜ* H :=
    { toMonoidHom := qAcyc
      continuous_toFun := hqAcyc_cont }
  let φH : H →* T := by
    change H →* FreeprocenterCosetTarget (Subgroup.zpowers g) (ℓ ^ r)
    exact cosetTargetCyclicHom (ℓ ^ r) g hℓr_order
  have htopLeftφH :
      (cosetTargetTopLeftHom H (ℓ ^ r)).comp φH = H.subtype := by
    change (cosetTargetTopLeftHom (Subgroup.zpowers g) (ℓ ^ r)).comp
        (cosetTargetCyclicHom (ℓ ^ r) g hℓr_order) =
      (Subgroup.zpowers g).subtype
    let Hcyc : Subgroup G₀ := Subgroup.zpowers g
    let gH : Hcyc := ⟨g, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩⟩
    have hgen : ∀ z : Hcyc, z ∈ Subgroup.zpowers gH := by
      simpa [Hcyc, gH] using
        zpowers_subtype_topologically_generated_by_generator (G₀ := G₀) g
    apply (MonoidHom.eq_iff_eq_on_generator hgen _ _).2
    unfold cosetTargetCyclicHom
    dsimp only
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    rw [monoidHomOfForallMemZpowers_apply_gen]
    rfl
  let φC₀ : A →* T :=
    φH.comp qAcyc
  let φG₀ : G₀ →* T :=
    topLeftOnlyCosetTargetHom (H := H) (ℓ ^ r) (MonoidHom.id G₀)
  let φP₀ : P →* T :=
    φG₀.comp (qΩ.comp ιP)
  let φC : A →ₜ* T :=
    { toMonoidHom := φC₀
      continuous_toFun := by
        exact (continuous_of_discreteTopology : Continuous φH).comp hqAcyc_cont }
  let φP : P →ₜ* T :=
    { toMonoidHom := φP₀
      continuous_toFun := by
        have hqPcont : Continuous (qΩ.comp ιP : P → G₀) :=
          hqΩcont.comp ιP.continuous_toFun
        exact (continuous_of_discreteTopology : Continuous φG₀).comp hqPcont }
  let ΦΩ : Ω →ₜ* T :=
    hOmega.lift (cosetTarget_isProC_sigmaGroup H hG₀pi hℓsigma) φC φP
  let topLeftT : T →* G₀ := cosetTargetTopLeftHom H (ℓ ^ r)
  let topLeftΦΩ : Ω →ₜ* G₀ :=
    { toMonoidHom := topLeftT.comp ΦΩ
      continuous_toFun := by
        exact (continuous_of_discreteTopology : Continuous topLeftT).comp ΦΩ.continuous_toFun }
  let qΩT : Ω →ₜ* G₀ :=
    { toMonoidHom := qΩ
      continuous_toFun := hqΩcont }
  have hG₀ProC :
      (ProCGroups.ProC.finiteGroupClassProCPredicate
        (SigmaGroup[sigma])) (G := G₀) := by
    exact
      ProCGroups.ProC.IsProCGroup.of_finite_discrete
        (C := ProCGroups.FiniteGroupClass.sigmaGroup sigma)
        (G := G₀)
        (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed sigma)
        hG₀pi
  have htopLeftΦΩ : topLeftΦΩ = qΩT := by
    apply hOmega.hom_ext hG₀ProC
    · ext a
      have hleft :
          ΦΩ (ιC a) = φC a := by
        have h := congrArg (fun f : A →ₜ* T => f a)
          (hOmega.lift_left
            (cosetTarget_isProC_sigmaGroup H hG₀pi hℓsigma) φC φP)
        exact h
      change topLeftT (ΦΩ (ιC a)) = qΩ (ιC a)
      rw [hleft]
      change ((cosetTargetTopLeftHom H (ℓ ^ r)).comp φH) (qAcyc a) = qΩ (ιC a)
      rw [htopLeftφH]
      rfl
    · ext p
      have hright :
          ΦΩ (ιP p) = φP p := by
        have h := congrArg (fun f : P →ₜ* T => f p)
          (hOmega.lift_right
            (cosetTarget_isProC_sigmaGroup H hG₀pi hℓsigma) φC φP)
        exact h
      change topLeftT (ΦΩ (ιP p)) = qΩ (ιP p)
      rw [hright]
      change ((cosetTargetTopLeftHom H (ℓ ^ r)).comp
          (topLeftOnlyCosetTargetHom (H := H) (ℓ ^ r) (MonoidHom.id G₀)))
          (qΩ (ιP p)) = qΩ (ιP p)
      rfl
  let qT : Q →ₜ* G₀ :=
    { toMonoidHom := q
      continuous_toFun := continuous_quotient_mk' }
  have hqsurj : Function.Surjective q := by
    simpa [q] using (QuotientGroup.mk_surjective (s := (V : Subgroup Q)))
  have hK_le_V : K ≤ (V : Subgroup Q) := by
    intro z hz
    change z ∈ K ⊔ (W : Subgroup Q)
    exact (le_sup_left : K ≤ K ⊔ (W : Subgroup Q)) hz
  have hK_map_q_bot : K.map q = (⊥ : Subgroup G₀) := by
    ext z
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact (Subgroup.mem_bot).2 (by
        exact (QuotientGroup.eq_one_iff (N := (V : Subgroup Q)) k).2 (hK_le_V hk))
    · intro hz
      rw [Subgroup.mem_bot] at hz
      subst z
      exact ⟨1, K.one_mem, by simp only [map_one, q]⟩
  have hG₀der : topDerivedTop G₀ (m - 1) = (⊥ : Subgroup G₀) := by
    have hclosed_comm :
        ∀ n : ℕ,
          IsClosed (((closedCommutator (topDerivedTop Q n) (topDerivedTop Q n)).map
            (qT : Q →* G₀) : Subgroup G₀) : Set G₀) := by
      intro _
      exact isClosed_discrete _
    have hmap :=
      topDerived_map_eq_of_surj (f := qT) hqsurj hclosed_comm (m - 1)
    rw [← hmap]
    simpa [K, qT] using hK_map_q_bot
  have hTder : topDerivedTop T m = (⊥ : Subgroup T) := by
    exact
      cosetTarget_topDerivedTop_eq_bot_of_base H (ℓ ^ r) hm hG₀der
  have hkerΦΩ : topDerivedTop Ω m ≤ (ΦΩ : Ω →* T).ker := by
    intro z hz
    have hzT : ΦΩ z ∈ topDerivedTop T m :=
      (topDerivedTop_le_comap (f := ΦΩ) (m := m)) hz
    rw [hTder] at hzT
    exact (MonoidHom.mem_ker).2 (by simpa using hzT)
  let ψ : Q →ₜ* T :=
    QuotientGroup.liftₜ (topDerivedTop Ω m) ΦΩ hkerΦΩ
  have hψ_topLeft : (cosetTargetTopLeftHom H (ℓ ^ r)).comp ψ = q := by
    ext ω
    simp only [MonoidHom.coe_comp, Function.comp_apply]
    have hψω :
        (ψ : Q →* T) ((QuotientGroup.mk' (topDerivedTop Ω m)) ω) = ΦΩ ω := by
      simpa [ψ] using
        (QuotientGroup.liftₜ_apply_mk (N := topDerivedTop Ω m)
          (f := ΦΩ) hkerΦΩ ω)
    rw [hψω]
    have happ := congrArg (fun f : Ω →ₜ* G₀ => f ω) htopLeftΦΩ
    simpa [topLeftΦΩ, qΩT, topLeftT, qΩ, πΩ] using happ
  have hψ_qx :
      ψ qx =
        cosetTestElement H (ℓ ^ r) g
          (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one, g]⟩) := by
    have hψπ :
        ψ (πΩ (ιC x)) = ΦΩ (ιC x) := by
      simpa [ψ, πΩ] using
        (QuotientGroup.liftₜ_apply_mk (N := topDerivedTop Ω m)
          (f := ΦΩ) hkerΦΩ (ιC x))
    have hleft :
        ΦΩ (ιC x) = φC x := by
      have h := congrArg (fun f : A →ₜ* T => f x)
        (hOmega.lift_left
          (cosetTarget_isProC_sigmaGroup H hG₀pi hℓsigma) φC φP)
      exact h
    change ψ (πΩ (ιC x)) =
      cosetTestElement H (ℓ ^ r) g
        (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one, g]⟩)
    rw [hψπ, hleft]
    change φH (qAcyc x) =
      cosetTestElement H (ℓ ^ r) g (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one, g]⟩)
    have hqAcyc_x :
        qAcyc x =
          (⟨g, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one, g]⟩⟩ : H) := by
      apply Subtype.ext
      rfl
    rw [hqAcyc_x]
    change cosetTargetCyclicHom (ℓ ^ r) g hℓr_order
        ⟨g, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩⟩ =
      cosetTestElement (Subgroup.zpowers g) (ℓ ^ r) g
        (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩)
    unfold cosetTargetCyclicHom
    dsimp only
    rw [monoidHomOfForallMemZpowers_apply_gen]
  show ∀ y : Q, y ∈ centralizerOf (qx ^ n) →
      QuotientGroup.mk' (V : Subgroup Q) y ∈
        ((closedSubgroupGenerated ({qx} : Set Q) : ClosedSubgroup Q) :
          Subgroup Q).map (QuotientGroup.mk' (V : Subgroup Q))
  intro yQ hy
  exact
    quotient_closedSubgroup_image_mem_of_cosetTarget
      (q := q) (x := qx) (y := yQ) (n := n) (K := ℓ ^ r)
      hnCoeff ψ hψ_topLeft hψ_qx hy

omit [IsTopologicalGroup P] in
/-- Proposition 1.3 (`freeprocenter`) in the paper: the centralizer containment for a free
pro-`Σ` product whose left factor is procyclic pro-`Σ`. -/
theorem proposition_1_3_free_proC_product_centralizer
    {sigma : Set ℕ}
    (ιC : A →ₜ* Ω) (ιP : P →ₜ* Ω)
    (hOmega : IsFreeProSigmaProduct[sigma] ιC ιP)
    (hAProSigma : ProSigmaGroup[sigma] A)
    (x : A) (hxgen : ProCGroups.Generation.TopologicallyGenerates (G := A) ({x} : Set A))
    (m : ℕ) (hm : 2 ≤ m) (n : ℤ) (hn : x ^ n ≠ 1) :
    centralizerOf (continuousToMaxSolvQuot Ω m ((ιC x) ^ n)) ≤
      (closedSubgroupGenerated ({continuousToMaxSolvQuot Ω m (ιC x)} : Set _) :
        Subgroup (MaxSolvQuot Ω m)) ⊔
        (topDerivedTop (MaxSolvQuot Ω m) (m - 1)) := by
  let Q : Type u := MaxSolvQuot Ω m
  let hΩprof : ProCGroups.IsProfiniteGroup Ω :=
    ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate
      (ProCGroups.FiniteGroupClass.sigmaGroup sigma) hOmega.isProC
  letI : CompactSpace Ω := hΩprof.compactSpace
  letI : T2Space Ω := hΩprof.t2Space
  letI : TotallyDisconnectedSpace Ω := hΩprof.totallyDisconnectedSpace
  let hQprof : ProCGroups.IsProfiniteGroup Q := by
    simpa [Q, MaxSolvQuot] using
      (ProCGroups.Generation.isProfinite_quotient_closedNormal
        (G := Ω) hΩprof
        (show IsClosed ((topDerivedTop Ω m : Subgroup Ω) : Set Ω) by infer_instance))
  letI : CompactSpace Q := hQprof.compactSpace
  letI : T2Space Q := hQprof.t2Space
  letI : TotallyDisconnectedSpace Q := hQprof.totallyDisconnectedSpace
  let qx : Q := continuousToMaxSolvQuot Ω m (ιC x)
  let K : Subgroup Q := topDerivedTop Q (m - 1)
  have hqpow : continuousToMaxSolvQuot Ω m ((ιC x) ^ n) = qx ^ n := by
    simp only [qx, map_zpow]
  haveI : K.Normal := by
    dsimp [K]
    infer_instance
  have hKclosed : IsClosed (K : Set Q) := by
    dsimp [K]
    infer_instance
  have hcriterion :
      centralizerOf (qx ^ n) ≤
        ((closedSubgroupGenerated ({qx} : Set Q) : ClosedSubgroup Q) :
          Subgroup Q) ⊔ K := by
    refine
      centralizerOf_zpow_le_cyclic_join_closedNormal_of_cofinal_openNormal_image
        (Q := Q) qx n K hKclosed ?_
    simpa only [Q, qx, K] using
      free_proC_product_centralizer_cofinal_coset_lift
        ιC ιP hOmega hAProSigma x hxgen m hm n hn
  simpa only [Q, qx, K, hqpow] using hcriterion

/-- Internal finite quotient class form of `lem:non-zero-div-free`.

The element is the completed group-algebra term `\bar x_i^n - 1`.  The paper only needs the
pro-`Σ` case; this version abstracts only the harmless choice between the concrete
`SigmaGroup[sigma]` class and the finite quotient class induced by `proSigmaProC`. -/
private theorem non_zero_divisor_completed_abelianization_of_sigma_finiteClass
    {sigma : Set ℕ} (C : ProCGroups.FiniteGroupClass.{u})
    (hC_to_sigma : ∀ {Q : Type u} [Group Q] [Finite Q], C Q → SigmaGroup[sigma] Q)
    (hsigma_to_C : ∀ {Q : Type u} [Group Q], SigmaGroup[sigma] Q → C Q)
    {r : ℕ} (X : Fin r → F)
    (hFree :
      ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate
          (SigmaGroup[sigma])) (Fin r) F X)
    (i : Fin r) (n : ℤ) (hn : n ≠ 0) :
    IsLeftRegular
      (FoxDifferential.zcGroupLike
          C
          (TopologicalAbelianization F)
          ((ProCGroups.Abelian.TopologicalAbelianization.mk F (X i)) ^ n) - 1) := by
  classical
  let HAb : Type u := TopologicalAbelianization F
  let xbar : HAb := ProCGroups.Abelian.TopologicalAbelianization.mk F (X i)
  change IsLeftRegular (FoxDifferential.zcGroupLike C HAb (xbar ^ n) - 1)
  rw [isLeftRegular_iff_right_eq_zero_of_mul]
  intro y hy
  apply FoxDifferential.zcCompletedGroupAlgebraProjection_ext
  intro j
  change FoxDifferential.zcCompletedGroupAlgebraProjection C HAb j y = 0
  let K : ℕ := j.1.modulus
  let U : ProCGroups.ProC.OpenNormalSubgroupInClass C HAb := OrderDual.ofDual j.2
  let Q : Type u := HAb ⧸ (U.1 : Subgroup HAb)
  let qU : HAb →ₜ* Q :=
    ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U
  let aQ : Q := qU xbar
  let a : Q := aQ ^ n
  have hQC : C Q := by
    simpa only [Q, U] using U.2
  letI : Finite Q := ProCGroups.FiniteGroupClass.finite (C := C) hQC
  have hQsigma : SigmaGroup[sigma] Q := hC_to_sigma hQC
  letI : Fintype Q := Fintype.ofFinite Q
  letI : DecidableEq Q := Classical.decEq Q
  let d : ℕ := orderOf a
  let A : ℕ := n.natAbs
  let B : ℕ := K * d
  let M : ℕ := B ^ (A + 1)
  have hKpos : 0 < K := by
    simpa only [K] using j.1.positive
  have hApos : 0 < A := by
    exact Int.natAbs_pos.mpr hn
  have hdpos : 0 < d := by
    simpa only [d] using orderOf_pos a
  have hBpos : 0 < B := by
    exact Nat.mul_pos hKpos hdpos
  have hMpos : 0 < M := by
    exact pow_pos hBpos (A + 1)
  have hKMpos : 0 < K * M := by
    exact Nat.mul_pos hKpos hMpos
  letI : NeZero (K * M) := ⟨Nat.ne_of_gt hKMpos⟩
  letI : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  have hKsigma : ProCGroups.FiniteGroupClass.IsSigmaNumber sigma K := by
    let T : Type u := ULift.{u} (Multiplicative (ZMod j.1.modulus))
    letI : Group T := inferInstance
    letI : Finite T := ProCGroups.FiniteGroupClass.finite (C := C) j.1.cyclic_mem
    have hTsigma : SigmaGroup[sigma] T := hC_to_sigma j.1.cyclic_mem
    rcases hTsigma with ⟨_, hsigmaT⟩
    letI : NeZero j.1.modulus := ⟨Nat.ne_of_gt j.1.positive⟩
    have hcard : Nat.card T = j.1.modulus := by
      calc
        Nat.card T = Nat.card (Multiplicative (ZMod j.1.modulus)) :=
          Nat.card_congr (MulEquiv.ulift :
            T ≃* Multiplicative (ZMod j.1.modulus)).toEquiv
        _ = j.1.modulus := by
          simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    simpa only [K, T, hcard] using hsigmaT
  have hdsigma : ProCGroups.FiniteGroupClass.IsSigmaNumber sigma d := by
    simpa only [d] using
      ProCGroups.FiniteGroupClass.IsSigmaNumber.of_dvd (sigma := sigma) hQsigma.2
        (orderOf_dvd_natCard a)
  have hBsigma : ProCGroups.FiniteGroupClass.IsSigmaNumber sigma B := by
    simpa only [B] using
      ProCGroups.FiniteGroupClass.IsSigmaNumber.mul hKsigma hdsigma
  have hMsigma : ProCGroups.FiniteGroupClass.IsSigmaNumber sigma M := by
    simpa only [M] using
      ProCGroups.FiniteGroupClass.IsSigmaNumber.pow (k := A + 1) hBsigma
  have hKMsigma : ProCGroups.FiniteGroupClass.IsSigmaNumber sigma (K * M) := by
    exact ProCGroups.FiniteGroupClass.IsSigmaNumber.mul hKsigma hMsigma
  rcases
      ProCGroups.FreeProC.exists_freeAbelianizationCyclicCoordinate
        (sigma := sigma) (r := r) (L := K * M) hKMpos hKMsigma X hFree i with
    ⟨χ, hχ⟩
  have hTargetLsigma : SigmaGroup[sigma] (Q × Multiplicative (ZMod (K * M))) :=
    ProCGroups.FiniteGroupClass.sigmaGroup_prod_multiplicativeZMod
      (sigma := sigma) (Q := Q) hQsigma hKMpos hKMsigma
  let ΦL : HAb →ₜ* Q × Multiplicative (ZMod (K * M)) :=
    ContinuousMonoidHom.prod qU χ
  let red : Multiplicative (ZMod (K * M)) →ₜ* Multiplicative (ZMod M) :=
    { toMonoidHom := finiteCyclicReduction M K
      continuous_toFun := continuous_of_discreteTopology }
  let χM : HAb →ₜ* Multiplicative (ZMod M) := red.comp χ
  have hTargetMsigma : SigmaGroup[sigma] (Q × Multiplicative (ZMod M)) :=
    ProCGroups.FiniteGroupClass.sigmaGroup_prod_multiplicativeZMod
      (sigma := sigma) (Q := Q) hQsigma hMpos hMsigma
  let ΦM : HAb →ₜ* Q × Multiplicative (ZMod M) :=
    ContinuousMonoidHom.prod qU χM
  let UL : ProCGroups.ProC.OpenNormalSubgroupInClass C HAb :=
    ProCGroups.ProC.OpenNormalSubgroupInClass.ofOpenNormal
      (ProCGroups.ProC.OpenNormalSubgroup.ker ΦL)
      (by
        have hquotSigma : SigmaGroup[sigma] (HAb ⧸ ΦL.toMonoidHom.ker) :=
          let e : HAb ⧸ ΦL.toMonoidHom.ker ≃* ΦL.toMonoidHom.range :=
            QuotientGroup.quotientKerEquivRange ΦL.toMonoidHom
          have hRange : SigmaGroup[sigma] ΦL.toMonoidHom.range :=
            (ProCGroups.FiniteGroupClass.sigmaGroup_subgroupClosed sigma)
              (H := ΦL.toMonoidHom.range) hTargetLsigma
          (ProCGroups.FiniteGroupClass.sigmaGroup_isomClosed sigma) ⟨e.symm⟩ hRange
        exact hsigma_to_C hquotSigma)
  let UM : ProCGroups.ProC.OpenNormalSubgroupInClass C HAb :=
    ProCGroups.ProC.OpenNormalSubgroupInClass.ofOpenNormal
      (ProCGroups.ProC.OpenNormalSubgroup.ker ΦM)
      (by
        have hquotSigma : SigmaGroup[sigma] (HAb ⧸ ΦM.toMonoidHom.ker) :=
          let e : HAb ⧸ ΦM.toMonoidHom.ker ≃* ΦM.toMonoidHom.range :=
            QuotientGroup.quotientKerEquivRange ΦM.toMonoidHom
          have hRange : SigmaGroup[sigma] ΦM.toMonoidHom.range :=
            (ProCGroups.FiniteGroupClass.sigmaGroup_subgroupClosed sigma)
              (H := ΦM.toMonoidHom.range) hTargetMsigma
          (ProCGroups.FiniteGroupClass.sigmaGroup_isomClosed sigma) ⟨e.symm⟩ hRange
        exact hsigma_to_C hquotSigma)
  have hULUM : (UL.1 : Subgroup HAb) ≤ (UM.1 : Subgroup HAb) := by
    intro z hz
    have hzL : ΦL z = 1 := by
      change z ∈ ΦL.toMonoidHom.ker at hz
      exact MonoidHom.mem_ker.mp hz
    have hq : qU z = 1 := congrArg Prod.fst hzL
    have hχz : χ z = 1 := congrArg Prod.snd hzL
    change ΦM z = 1
    change (qU z, χM z) = (1, 1)
    rw [hq]
    change (1, red (χ z)) = (1, 1)
    rw [hχz]
    simp only [Lean.Elab.WF.paramLet, map_one, red]
  have hUMU : (UM.1 : Subgroup HAb) ≤ (U.1 : Subgroup HAb) := by
    intro z hz
    have hzM : ΦM z = 1 := by
      change z ∈ ΦM.toMonoidHom.ker at hz
      exact MonoidHom.mem_ker.mp hz
    have hq : qU z = 1 := congrArg Prod.fst hzM
    exact
      (ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj_eq_one_iff
        (C := C) (U := U)).mp hq
  let kL : FoxDifferential.ZCCompletedGroupAlgebraIndex C HAb :=
    (j.1, OrderDual.toDual UL)
  let kM : FoxDifferential.ZCCompletedGroupAlgebraIndex C HAb :=
    (j.1, OrderDual.toDual UM)
  have hkML : kM ≤ kL := by
    constructor
    · exact dvd_rfl
    · change (UL.1 : Subgroup HAb) ≤ (UM.1 : Subgroup HAb)
      exact hULUM
  have hjM : j ≤ kM := by
    constructor
    · exact dvd_rfl
    · change (UM.1 : Subgroup HAb) ≤ (U.1 : Subgroup HAb)
      exact hUMU
  let yL : FoxDifferential.ZCCompletedGroupAlgebraStage C HAb kL :=
    FoxDifferential.zcCompletedGroupAlgebraProjection C HAb kL y
  let yM : FoxDifferential.ZCCompletedGroupAlgebraStage C HAb kM :=
    FoxDifferential.zcCompletedGroupAlgebraProjection C HAb kM y
  let embL :
      FoxDifferential.CompletedGroupAlgebraQuotientInClass HAb C (OrderDual.toDual UL) →*
        Q × Multiplicative (ZMod (K * M)) :=
    quotientKerEmbedding ΦL.toMonoidHom
  let embM :
      FoxDifferential.CompletedGroupAlgebraQuotientInClass HAb C (OrderDual.toDual UM) →*
        Q × Multiplicative (ZMod M) :=
    quotientKerEmbedding ΦM.toMonoidHom
  have hstageL :
      (MonoidAlgebra.of (ZMod K)
          (FoxDifferential.CompletedGroupAlgebraQuotientInClass HAb C (OrderDual.toDual UL))
          ((QuotientGroup.mk' (UL.1 : Subgroup HAb) xbar :
            FoxDifferential.CompletedGroupAlgebraQuotientInClass HAb C (OrderDual.toDual UL)) ^ n) -
          1) * yL = 0 := by
    simpa only [yL, kL, K] using
      FoxDifferential.zcCompletedGroupAlgebra_projection_zpow_sub_one_mul_eq_zero
        C HAb xbar n y kL hy
  have hembL_x :
      embL
          (QuotientGroup.mk' (UL.1 : Subgroup HAb) xbar :
            FoxDifferential.CompletedGroupAlgebraQuotientInClass HAb C (OrderDual.toDual UL)) =
        (aQ, Multiplicative.ofAdd (1 : ZMod (K * M))) := by
    have hχx : χ xbar = Multiplicative.ofAdd (1 : ZMod (K * M)) := by
      simpa only [xbar, ProCGroups.Abelian.TopologicalAbelianization.mk] using hχ
    change
      quotientKerEmbedding ΦL.toMonoidHom
          (QuotientGroup.mk' ΦL.toMonoidHom.ker xbar) =
        (aQ, Multiplicative.ofAdd (1 : ZMod (K * M)))
    rw [quotientKerEmbedding_mk]
    change (qU xbar, χ xbar) = (aQ, Multiplicative.ofAdd (1 : ZMod (K * M)))
    simp only [hχx, aQ]
  have hembL_x_pow :
      (embL
          (QuotientGroup.mk' (UL.1 : Subgroup HAb) xbar :
            FoxDifferential.CompletedGroupAlgebraQuotientInClass HAb C (OrderDual.toDual UL))) ^ n =
        (a, Multiplicative.ofAdd (n : ZMod (K * M))) := by
    rw [hembL_x]
    ext
    · simp only [Prod.pow_mk, aQ, a]
    · change (Multiplicative.ofAdd (1 : ZMod (K * M))) ^ n =
        Multiplicative.ofAdd (n : ZMod (K * M))
      change Multiplicative.ofAdd (n • (1 : ZMod (K * M))) =
        Multiplicative.ofAdd (n : ZMod (K * M))
      simp only [zsmul_eq_mul, mul_one]
  have hrelProd :
      (MonoidAlgebra.of (ZMod K) (Q × Multiplicative (ZMod (K * M)))
          (a, Multiplicative.ofAdd (n : ZMod (K * M))) - 1) *
        MonoidAlgebra.mapDomainRingHom (ZMod K) embL yL = 0 := by
    have hpush :=
      finiteGroupAlgebra_mapDomain_zpow_sub_one_mul_eq_zero
        (R := ZMod K)
        (G := FoxDifferential.CompletedGroupAlgebraQuotientInClass HAb C
          (OrderDual.toDual UL))
        (H := Q × Multiplicative (ZMod (K * M)))
        embL
        (QuotientGroup.mk' (UL.1 : Subgroup HAb) xbar :
          FoxDifferential.CompletedGroupAlgebraQuotientInClass HAb C (OrderDual.toDual UL))
        n yL hstageL
    rw [hembL_x_pow] at hpush
    exact hpush
  have hd_order : a ^ d = 1 := by
    simp only [pow_orderOf_eq_one, d]
  have hnatAbs_mul : (((d : ℤ) * n).natAbs) = d * A := by
    simp only [Int.natAbs_mul, Int.natAbs_natCast, A]
  have hgcd : Nat.gcd (((d : ℤ) * n).natAbs) (K * M) ∣ M := by
    simpa only [M, B, A, hnatAbs_mul] using
      ProCGroups.FiniteGroupClass.gcd_mul_dvd_pow_depth
        (K := K) (d := d) (A := A) hKpos hdpos hApos
  have hzProd :
      MonoidAlgebra.mapDomainRingHom (ZMod K) (finiteProductCyclicReduction Q M K)
        (MonoidAlgebra.mapDomainRingHom (ZMod K) embL yL) = 0 := by
    exact
      finiteProductCyclicGroupAlgebra_projection_eq_zero_of_pair_relation_of_order
        (Q := Q) (M := M) (K := K) (a := a) (n := n) (d := d)
        hd_order hgcd (MonoidAlgebra.mapDomainRingHom (ZMod K) embL yL) hrelProd
  have hpoint :
      ∀ q : FoxDifferential.CompletedGroupAlgebraQuotientInClass HAb C (OrderDual.toDual UL),
        embM
          (ProCGroups.ProC.OpenNormalSubgroupInClass.map
            (C := C) (G := HAb) (U := UM) (V := UL) hULUM q) =
          finiteProductCyclicReduction Q M K (embL q) := by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    change
      quotientKerEmbedding ΦM.toMonoidHom
          (QuotientGroup.mk' ΦM.toMonoidHom.ker z) =
        finiteProductCyclicReduction Q M K
          (quotientKerEmbedding ΦL.toMonoidHom
            (QuotientGroup.mk' ΦL.toMonoidHom.ker z))
    rw [quotientKerEmbedding_mk, quotientKerEmbedding_mk]
    change (qU z, red (χ z)) = (qU z, finiteCyclicReduction M K (χ z))
    rfl
  let qmapLM :
      FoxDifferential.CompletedGroupAlgebraQuotientInClass HAb C (OrderDual.toDual UL) →*
        FoxDifferential.CompletedGroupAlgebraQuotientInClass HAb C (OrderDual.toDual UM) :=
    ProCGroups.ProC.OpenNormalSubgroupInClass.map
      (C := C) (G := HAb) (U := UM) (V := UL) hULUM
  have hcomp :
      embM.comp qmapLM = (finiteProductCyclicReduction Q M K).comp embL := by
    apply MonoidHom.ext
    intro q
    exact hpoint q
  have htransitionMap :
      FoxDifferential.zcCompletedGroupAlgebraTransition C HAb hkML =
        MonoidAlgebra.mapDomainRingHom (ZMod K) qmapLM := by
    simpa only [kM, kL, K, qmapLM] using
      FoxDifferential.zcCompletedGroupAlgebraTransition_sameCoeff
        (C := C) (H := HAb) (coeff := j.1) (U := UM) (V := UL) hULUM
  have hmapTransition :
      MonoidAlgebra.mapDomainRingHom (ZMod K) embM
          (FoxDifferential.zcCompletedGroupAlgebraTransition C HAb hkML yL) =
        MonoidAlgebra.mapDomainRingHom (ZMod K) (finiteProductCyclicReduction Q M K)
          (MonoidAlgebra.mapDomainRingHom (ZMod K) embL yL) := by
    calc
      MonoidAlgebra.mapDomainRingHom (ZMod K) embM
          (FoxDifferential.zcCompletedGroupAlgebraTransition C HAb hkML yL)
          = MonoidAlgebra.mapDomainRingHom (ZMod K) embM
              (MonoidAlgebra.mapDomainRingHom (ZMod K) qmapLM yL) := by
              rw [htransitionMap]
      _ = MonoidAlgebra.mapDomainRingHom (ZMod K) (embM.comp qmapLM) yL := by
              rw [← RingHom.comp_apply,
                CompletedGroupAlgebra.finiteGroupAlgebra_mapDomainRingHom_comp]
      _ = MonoidAlgebra.mapDomainRingHom (ZMod K)
            ((finiteProductCyclicReduction Q M K).comp embL) yL := by
              rw [hcomp]
      _ = MonoidAlgebra.mapDomainRingHom (ZMod K) (finiteProductCyclicReduction Q M K)
            (MonoidAlgebra.mapDomainRingHom (ZMod K) embL yL) := by
              rw [← RingHom.comp_apply,
                CompletedGroupAlgebra.finiteGroupAlgebra_mapDomainRingHom_comp]
  have hmapMzero : MonoidAlgebra.mapDomainRingHom (ZMod K) embM yM = 0 := by
    have htrans :
        FoxDifferential.zcCompletedGroupAlgebraTransition C HAb hkML yL = yM := by
      simp only [FoxDifferential.zcCompletedGroupAlgebraTransition_projection, yL, yM]
    rw [← htrans]
    exact hmapTransition.trans hzProd
  have hyM : yM = 0 := by
    exact
      (MonoidAlgebra.mapDomain_injective (R := ZMod K)
        (quotientKerEmbedding_injective ΦM.toMonoidHom))
        (by simpa only [MonoidAlgebra.mapDomainRingHom_apply, embM] using hmapMzero)
  calc
    FoxDifferential.zcCompletedGroupAlgebraProjection C HAb j y =
        FoxDifferential.zcCompletedGroupAlgebraTransition C HAb hjM yM := by
          simp only [FoxDifferential.zcCompletedGroupAlgebraTransition_projection, yM]
    _ = 0 := by simp only [hyM, map_zero]

/-- The non-zero-divisor statement for completed abelianization over the concrete `Σ` class. -/
theorem lemma_1_4_non_zero_divisor_completed_abelianization
    {sigma : Set ℕ}
    {r : ℕ} (X : Fin r → F)
    (hFree :
      ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate
          (SigmaGroup[sigma])) (Fin r) F X)
    (i : Fin r) (n : ℤ) (hn : n ≠ 0) :
    IsLeftRegular
      (FoxDifferential.zcGroupLike
          (SigmaGroup[sigma])
          (TopologicalAbelianization F)
          ((ProCGroups.Abelian.TopologicalAbelianization.mk F (X i)) ^ n) - 1) :=
  non_zero_divisor_completed_abelianization_of_sigma_finiteClass
    (ProCGroups.FiniteGroupClass.sigmaGroup sigma)
    (fun hQ => hQ)
    (fun hQ => hQ)
    X hFree i n hn

/-- The closed cyclic subgroups generated by two distinct free generators have trivial
intersection. -/
private theorem closedSubgroupGenerated_singleton_inf_bot_of_distinct_free_generators
    {ι : Type v} (X : ι → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) ι F X)
    {i j : ι} (hij : i ≠ j) (m : ℕ) :
    (closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X i)} : Set _) :
        Subgroup (MaxSolvQuot F m)) ⊓
      (closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X j)} : Set _) :
        Subgroup (MaxSolvQuot F m)) = ⊥ := by
  classical
  let S : Finset ι := {i}
  let r : MaxSolvQuot F m →ₜ* MaxSolvQuot F m :=
    ProCGroups.FiniteStepSolvableQuotients.topMaxSolvQuotMap
      (hFree.collapseToFinset S) m
  let Fix : Subgroup (MaxSolvQuot F m) :=
    (r : MaxSolvQuot F m →* MaxSolvQuot F m).eqLocus (MonoidHom.id _)
  have hFixClosed : IsClosed (Fix : Set (MaxSolvQuot F m)) := by
    change IsClosed {x : MaxSolvQuot F m | r x = x}
    exact isClosed_eq r.continuous continuous_id
  have hcycFix :
      closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X i)} : Set _) ≤ Fix := by
    have hself : hFree.collapseToFinset S (X i) = X i := by
      exact hFree.collapseToFinset_apply_mem (S := S) (by simp only [Finset.mem_singleton, S])
    have hri :
        r (continuousToMaxSolvQuot F m (X i)) =
          continuousToMaxSolvQuot F m (X i) := by
      change
        QuotientGroup.map
              (N := topDerivedTop F m)
              (M := topDerivedTop F m)
              (f := (hFree.collapseToFinset S : F →* F))
              (ProCGroups.FiniteStepSolvableQuotients.topDerivedTop_le_comap
                (G := F) (Q := F) (f := hFree.collapseToFinset S) m)
            ((QuotientGroup.mk' (topDerivedTop F m)) (X i)) =
          (QuotientGroup.mk' (topDerivedTop F m)) (X i)
      rw [QuotientGroup.map_mk']
      exact congrArg (QuotientGroup.mk' (topDerivedTop F m)) hself
    have hsingle :
        ({continuousToMaxSolvQuot F m (X i)} : Set (MaxSolvQuot F m)) ⊆ Fix := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hri
    exact
      Subgroup.topologicalClosure_minimal _
        ((Subgroup.closure_le (K := Fix)).2 hsingle) hFixClosed
  have hkerClosed : IsClosed (((r : MaxSolvQuot F m →* MaxSolvQuot F m).ker :
      Subgroup (MaxSolvQuot F m)) : Set (MaxSolvQuot F m)) := by
    change IsClosed {x : MaxSolvQuot F m | r x = 1}
    exact isClosed_singleton.preimage r.continuous
  have hcycKer :
      closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X j)} : Set _) ≤
        (r : MaxSolvQuot F m →* MaxSolvQuot F m).ker := by
    have hne : hFree.collapseToFinset S (X j) = 1 := by
      have hjS : j ∉ S := by
        simpa [S] using hij.symm
      exact hFree.collapseToFinset_apply_not_mem (S := S) hjS
    have hrj :
        r (continuousToMaxSolvQuot F m (X j)) = 1 := by
      change
        QuotientGroup.map
              (N := topDerivedTop F m)
              (M := topDerivedTop F m)
              (f := (hFree.collapseToFinset S : F →* F))
              (ProCGroups.FiniteStepSolvableQuotients.topDerivedTop_le_comap
                (G := F) (Q := F) (f := hFree.collapseToFinset S) m)
            ((QuotientGroup.mk' (topDerivedTop F m)) (X j)) = 1
      rw [QuotientGroup.map_mk']
      simpa using congrArg (QuotientGroup.mk' (topDerivedTop F m)) hne
    have hsingle :
        ({continuousToMaxSolvQuot F m (X j)} : Set (MaxSolvQuot F m)) ⊆
          (r : MaxSolvQuot F m →* MaxSolvQuot F m).ker := by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hrj
    exact
      Subgroup.topologicalClosure_minimal _
        ((Subgroup.closure_le
          (K := (r : MaxSolvQuot F m →* MaxSolvQuot F m).ker)).2 hsingle) hkerClosed
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hfix : z ∈ Fix := hcycFix hz.1
  have hker : z ∈ (r : MaxSolvQuot F m →* MaxSolvQuot F m).ker := hcycKer hz.2
  change r z = z at hfix
  change r z = 1 at hker
  calc
    z = r z := hfix.symm
    _ = 1 := hker

omit hCVariety hCIsomClosed in
/-- Transfer a finite basis family to the finite-rank case indexed by `Fin r`. -/
private theorem finiteFamily_to_finiteRank
    {ι : Type v} [Fintype ι] (X : ι → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) ι F X) :
    let r : ℕ := Fintype.card ι
    let e : ι ≃ Fin r := Fintype.equivFin ι
    ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) (Fin r) F (fun k : Fin r => X (e.symm k)) := by
  classical
  let r : ℕ := Fintype.card ι
  let e : ι ≃ Fin r := Fintype.equivFin ι
  exact
    ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet.precompEquiv
      hFree e.symm

omit hCVariety hCIsomClosed in
/-- A finite-rank free pro-`Σ` group splits as the free pro-`Σ` product of the retract generated
by one chosen basis element and the retract generated by the complementary finite set. -/
private theorem finiteRank_singleton_complement_isFreeProSigmaProduct
    {sigma : Set ℕ} {r : ℕ} (X : Fin (r + 2) → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma]))
      (Fin (r + 2)) F X)
    (i : Fin (r + 2)) :
    let S : Finset (Fin (r + 2)) := {i}
    let T : Finset (Fin (r + 2)) := Finset.univ.erase i
    IsFreeProSigmaProduct[sigma]
      (hFree.collapseToFinsetInclusion S)
      (hFree.collapseToFinsetInclusion T) := by
  classical
  let S : Finset (Fin (r + 2)) := {i}
  let T : Finset (Fin (r + 2)) := Finset.univ.erase i
  let A : Type u := hFree.FinsetSupportRetract S
  let P : Type u := hFree.FinsetSupportRetract T
  let ιA : A →ₜ* F := hFree.collapseToFinsetInclusion S
  let ιP : P →ₜ* F := hFree.collapseToFinsetInclusion T
  have hιA_basis (s : S) :
      ιA (hFree.finsetSupportBasis S s) = X s.1 := rfl
  have hιP_basis (t : T) :
      ιP (hFree.finsetSupportBasis T t) = X t.1 := rfl
  change IsFreeProSigmaProduct[sigma] ιA ιP
  refine ⟨hFree.isProC, ?_⟩
  intro K _ _ _ hK φA φP
  let φ : Fin (r + 2) → K := fun j =>
    if hj : j ∈ S then
      φA (hFree.finsetSupportBasis S ⟨j, hj⟩)
    else
      φP (hFree.finsetSupportBasis T ⟨j, by
        simp only [Finset.mem_singleton, Finset.mem_erase, ne_eq, Finset.mem_univ, and_true, S, T] at hj ⊢
        exact hj⟩)
  have hφconv : ProCGroups.FreeProC.FamilyConvergesToOne (G := K) φ :=
    ProCGroups.FreeProC.FamilyConvergesToOne.of_finite_domain (G := K) φ
  rcases
      hFree.existsUnique_liftHom_of_convergesToOne_of_finiteGroupClass
        (SigmaGroup[sigma])
        (ProCGroups.FiniteGroupClass.sigmaGroup_isomClosed sigma)
        (ProCGroups.FiniteGroupClass.sigmaGroup_subgroupClosed sigma)
        (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed sigma)
        hK φ hφconv with
    ⟨ψ, hψ, hψuniq⟩
  refine ⟨ψ, ?_, ?_⟩
  · constructor
    · let hKprof : ProCGroups.IsProfiniteGroup K :=
        ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate
          (SigmaGroup[sigma]) hK
      letI : T2Space K := hKprof.t2Space
      apply
        ProCGroups.Generation.continuousMonoidHom_ext_of_topologicallyGenerates
          (hFree.isFreeProCGroupOnConvergingSet_finsetSupportBasis S).generates_range
      rintro _ ⟨s, rfl⟩
      have hψi := hψ i
      change ψ (ιA (hFree.finsetSupportBasis S s)) =
        φA (hFree.finsetSupportBasis S s)
      rw [hιA_basis]
      have hsEq : (s : Fin (r + 2)) = i :=
        Finset.mem_singleton.mp s.2
      have hsSubtype : s = (⟨i, by simp only [Finset.mem_singleton, S]⟩ : S) := Subtype.ext hsEq
      rw [hsSubtype]
      simpa [φ, S] using hψi
    · let hKprof : ProCGroups.IsProfiniteGroup K :=
        ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate
          (SigmaGroup[sigma]) hK
      letI : T2Space K := hKprof.t2Space
      apply
        ProCGroups.Generation.continuousMonoidHom_ext_of_topologicallyGenerates
          (hFree.isFreeProCGroupOnConvergingSet_finsetSupportBasis T).generates_range
      rintro _ ⟨t, rfl⟩
      have htS : (t : Fin (r + 2)) ∉ S := by
        have hne : (t : Fin (r + 2)) ≠ i := by
          exact (Finset.mem_erase.mp t.2).1
        simpa [S] using hne
      have hψt := hψ (t : Fin (r + 2))
      change ψ (ιP (hFree.finsetSupportBasis T t)) =
        φP (hFree.finsetSupportBasis T t)
      rw [hιP_basis]
      have htNe : (t : Fin (r + 2)) ≠ i := by
        simpa [S] using htS
      simpa [φ, S, htNe] using hψt
  · intro χ hχ
    apply hψuniq χ
    intro j
    by_cases hj : j ∈ S
    · have hleft := congrArg (fun f : A →ₜ* K =>
          f (hFree.finsetSupportBasis S ⟨j, hj⟩)) hχ.1
      change χ (ιA (hFree.finsetSupportBasis S ⟨j, hj⟩)) =
        φA (hFree.finsetSupportBasis S ⟨j, hj⟩) at hleft
      rw [hιA_basis] at hleft
      have hjEq : j = i := by
        simpa [S] using hj
      simpa [φ, S, hjEq] using hleft
    · have hjT : j ∈ T := by
        have hne : j ≠ i := by
          simpa [S] using hj
        exact Finset.mem_erase.mpr ⟨hne, by simp only [Finset.mem_univ]⟩
      have hright := congrArg (fun f : P →ₜ* K =>
          f (hFree.finsetSupportBasis T ⟨j, hjT⟩)) hχ.2
      change χ (ιP (hFree.finsetSupportBasis T ⟨j, hjT⟩)) =
        φP (hFree.finsetSupportBasis T ⟨j, hjT⟩) at hright
      rw [hιP_basis] at hright
      have hjNe : j ≠ i := by
        simpa [S] using hj
      simpa [φ, S, hjNe] using hright

private theorem closedSubgroupGenerated_singleton_inf_topDerivedTop_one_eq_bot_of_free_generator
    {ι : Type v} (X : ι → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) ι F X)
    (i : ι) (m : ℕ) :
    (closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X i)} : Set _) :
        Subgroup (MaxSolvQuot F m)) ⊓
      topDerivedTop (MaxSolvQuot F m) 1 = ⊥ := by
  classical
  let S : Finset ι := {i}
  let R : Type u := hFree.FinsetSupportRetract S
  let B : S → R := hFree.finsetSupportBasis S
  let iS : S := ⟨i, by simp only [Finset.mem_singleton, S]⟩
  let QF : Type u := MaxSolvQuot F m
  let QR : Type u := MaxSolvQuot R m
  let xQ : QF := continuousToMaxSolvQuot F m (X i)
  let xR : QR := continuousToMaxSolvQuot R m (B iS)
  let ρ : QF →ₜ* QR := finsetSupportRangeQuot X hFree S m
  let ιQ : QR →ₜ* QF := finsetSupportInclusionQuot X hFree S m
  let collapse : QF →ₜ* QF := collapseToFinsetQuot X hFree S m
  have hxρ : ρ xQ = xR := by
    have hxRange : hFree.collapseToFinsetRange S (X i) = B iS := by
      apply Subtype.ext
      change (hFree.collapseToFinset S (X i) : F) = X i
      simpa [B, ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet.collapseToFinsetRange,
        ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet.finsetSupportBasis] using
        hFree.collapseToFinset_apply_mem (S := S) (by simp only [Finset.mem_singleton, S])
    change
      finsetSupportRangeQuot X hFree S m (continuousToMaxSolvQuot F m (X i)) =
        continuousToMaxSolvQuot R m (B iS)
    rw [finsetSupportRangeQuot_apply]
    exact congrArg (continuousToMaxSolvQuot R m) hxRange
  have hcomp : ∀ z : QF, ιQ (ρ z) = collapse z := by
    intro z
    obtain ⟨a, rfl⟩ := continuousToMaxSolvQuot_surjective (G := F) m z
    have hcompF :
        (hFree.collapseToFinsetInclusion S).comp (hFree.collapseToFinsetRange S) =
          hFree.collapseToFinset S := by
      ext a
      rfl
    change
      finsetSupportInclusionQuot X hFree S m
          (finsetSupportRangeQuot X hFree S m (continuousToMaxSolvQuot F m a)) =
        collapseToFinsetQuot X hFree S m (continuousToMaxSolvQuot F m a)
    rw [finsetSupportRangeQuot_apply, finsetSupportInclusionQuot_apply]
    exact congrArg
      (fun y : F => continuousToMaxSolvQuot F m y)
      (congrArg (fun f : F →ₜ* F => f a) hcompF)
  let Fix : Subgroup QF := (collapse : QF →* QF).eqLocus (MonoidHom.id QF)
  have hFixClosed : IsClosed (Fix : Set QF) := by
    change IsClosed {z : QF | collapse z = z}
    exact isClosed_eq collapse.continuous continuous_id
  have hcycFix :
      closedSubgroupGenerated ({xQ} : Set QF) ≤ Fix := by
    have hself : hFree.collapseToFinset S (X i) = X i := by
      exact hFree.collapseToFinset_apply_mem (S := S) (by simp only [Finset.mem_singleton, S])
    have hri : collapse xQ = xQ := by
      change
        QuotientGroup.map
              (N := topDerivedTop F m)
              (M := topDerivedTop F m)
              (f := (hFree.collapseToFinset S : F →* F))
              (ProCGroups.FiniteStepSolvableQuotients.topDerivedTop_le_comap
                (G := F) (Q := F) (f := hFree.collapseToFinset S) m)
            ((QuotientGroup.mk' (topDerivedTop F m)) (X i)) =
          (QuotientGroup.mk' (topDerivedTop F m)) (X i)
      rw [QuotientGroup.map_mk']
      exact congrArg (QuotientGroup.mk' (topDerivedTop F m)) hself
    have hsingle : ({xQ} : Set QF) ⊆ Fix := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact hri
    exact
      Subgroup.topologicalClosure_minimal _
        ((Subgroup.closure_le (K := Fix)).2 hsingle) hFixClosed
  have hFreeR :
      ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) S R B :=
    hFree.isFreeProCGroupOnConvergingSet_finsetSupportBasis S
  have hRangeB : Set.range B = ({B iS} : Set R) := by
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      have hsEq : (s : ι) = i := Finset.mem_singleton.mp s.2
      have hsSubtype : s = iS := Subtype.ext hsEq
      simp only [hsSubtype, Set.mem_singleton_iff, B]
    · intro hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact ⟨iS, rfl⟩
  have hgenR :
      ProCGroups.Generation.TopologicallyGenerates (G := R) ({B iS} : Set R) := by
    simpa [hRangeB] using hFreeR.generates_range
  have hgenQR :
      ProCGroups.Generation.TopologicallyGenerates (G := QR) ({xR} : Set QR) := by
    let qR : R →ₜ* QR := continuousToMaxSolvQuot R m
    have hsurj : Function.Surjective qR := by
      simpa [qR, QR] using continuousToMaxSolvQuot_surjective (G := R) m
    have himage :
        ProCGroups.Generation.TopologicallyGenerates (G := QR)
          (qR '' ({B iS} : Set R)) := by
      exact
        ProCGroups.Generation.topologicallyGenerates_image_of_continuousSurjective
          (f := qR.toMonoidHom) qR.continuous hsurj hgenR
    have hImageEq : qR '' ({B iS} : Set R) = ({xR} : Set QR) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases Set.mem_singleton_iff.mp hz with rfl
        change qR (B iS) = xR
        rfl
      · intro hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        refine ⟨B iS, by simp only [Set.mem_singleton_iff], ?_⟩
        change qR (B iS) = xR
        rfl
    simpa [hImageEq] using himage
  have hQRder : topDerivedTop QR 1 = ⊥ :=
    topDerivedTop_one_eq_bot_of_topologicallyGenerates_singleton
      (Q := QR) xR hgenQR
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have hfix : z ∈ Fix := by
    simpa [xQ] using hcycFix hz.1
  have hzρder : ρ z ∈ topDerivedTop QR 1 := by
    exact topDerived_map_le (f := ρ) (m := 1) ⟨z, hz.2, rfl⟩
  have hzρ_one : ρ z = 1 := by
    change ρ z ∈ topDerivedTop QR 1 at hzρder
    rw [hQRder] at hzρder
    exact Subgroup.mem_bot.mp hzρder
  have hcollapse_one : collapse z = 1 := by
    calc
      collapse z = ιQ (ρ z) := (hcomp z).symm
      _ = 1 := by simp only [hzρ_one, map_one]
  change collapse z = z at hfix
  calc
    z = collapse z := hfix.symm
    _ = 1 := hcollapse_one

/-- Finite-rank Theorem 1.5 inputs satisfy the cyclic-join containment supplied by
Proposition 1.3. -/
private theorem finiteRank_centralizer_le_cyclic_join_lastDerived
    {sigma : Set ℕ} (hsigma : ∃ p, p ∈ sigma ∧ Nat.Prime p)
    {r m : ℕ} (X : Fin (r + 2) → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma]))
      (Fin (r + 2)) F X)
    (i : Fin (r + 2)) (hm : 2 ≤ m) (n : ℤ) (hn : n ≠ 0) :
    centralizerOf (continuousToMaxSolvQuot F m ((X i) ^ n)) ≤
      (closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X i)} : Set _) :
        Subgroup (MaxSolvQuot F m)) ⊔
        topDerivedTop (MaxSolvQuot F m) (m - 1) := by
  classical
  let S : Finset (Fin (r + 2)) := {i}
  let T : Finset (Fin (r + 2)) := Finset.univ.erase i
  let A : Type u := hFree.FinsetSupportRetract S
  let P : Type u := hFree.FinsetSupportRetract T
  let ιA : A →ₜ* F := hFree.collapseToFinsetInclusion S
  let ιP : P →ₜ* F := hFree.collapseToFinsetInclusion T
  let xA : A := hFree.finsetSupportBasis S ⟨i, by simp only [Finset.mem_singleton, S]⟩
  have hΩ : IsFreeProSigmaProduct[sigma] ιA ιP := by
    simpa [S, T, ιA, ιP] using
      finiteRank_singleton_complement_isFreeProSigmaProduct
        (F := F) (sigma := sigma) (r := r) X hFree i
  have hAProSigma : ProSigmaGroup[sigma] A := by
    simpa [A, S] using hFree.isProCGroup_finsetSupportRetract S
  have hxgen : ProCGroups.Generation.TopologicallyGenerates (G := A) ({xA} : Set A) := by
    have hFreeS :=
      hFree.isFreeProCGroupOnConvergingSet_finsetSupportBasis S
    have hRange :
        Set.range (hFree.finsetSupportBasis S) = ({xA} : Set A) := by
      ext y
      constructor
      · rintro ⟨s, rfl⟩
        have hsEq : (s : Fin (r + 2)) = i :=
          Finset.mem_singleton.mp s.2
        have hsSubtype : s = (⟨i, by simp only [Finset.mem_singleton, S]⟩ : S) := Subtype.ext hsEq
        simp only [hsSubtype, Set.mem_singleton_iff, xA]
      · intro hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact ⟨⟨i, by simp only [Finset.mem_singleton, S]⟩, rfl⟩
    simpa [hRange, xA] using hFreeS.generates_range
  have hιAx : ιA xA = X i := rfl
  have hxzn : xA ^ n ≠ 1 :=
    (hFree.isFreeProCGroupOnConvergingSet_finsetSupportBasis S).generator_zpow_ne_one_of_sigma
      hsigma
      ⟨i, by simp only [Finset.mem_singleton, S]⟩ n hn
  have hle :=
    proposition_1_3_free_proC_product_centralizer
      ιA ιP hΩ hAProSigma xA hxgen m hm n hxzn
  simpa [S, T, A, P, ιA, ιP, xA, hιAx, map_zpow] using hle

/-- The non-zero-divisor lemma in the finite quotient class induced by `proSigmaProC`.
This is the coefficient class used by the CES finite-coordinate APIs. -/
private theorem non_zero_divisor_completed_abelianization_proSigmaFiniteQuotientClass
    {sigma : Set ℕ}
    {r : ℕ} (X : Fin r → F)
    (hFree :
      ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate
          (SigmaGroup[sigma])) (Fin r) F X)
    (i : Fin r) (n : ℤ) (hn : n ≠ 0) :
    IsLeftRegular
      (FoxDifferential.zcGroupLike
          (ProCGroups.ProC.proSigmaProC.{u} sigma).finiteQuotientClass
          (TopologicalAbelianization F)
          ((ProCGroups.Abelian.TopologicalAbelianization.mk F (X i)) ^ n) - 1) :=
  non_zero_divisor_completed_abelianization_of_sigma_finiteClass
    (ProCGroups.ProC.proSigmaProC.{u} sigma).finiteQuotientClass
    (fun hQ =>
      (ProCGroups.ProC.proSigmaProC_finiteQuotientClass_iff (sigma := sigma)).1 hQ)
    (fun hQ => by
      letI : Finite _ := ProCGroups.FiniteGroupClass.finite hQ
      exact (ProCGroups.ProC.proSigmaProC_finiteQuotientClass_iff (sigma := sigma)).2 hQ)
    X hFree i n hn

omit hCVariety hCIsomClosed in
/-- The finite-rank rank-one case of Theorem 1.5. -/
private theorem thm_center_free_freegroup_finiteRank_rankOne
    (X : Fin 1 → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) (Fin 1) F X)
    (m : ℕ) (n : ℤ) :
    centralizerOf (continuousToMaxSolvQuot F m ((X 0) ^ n)) =
      closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X 0)} : Set _) := by
  let x : F := X 0
  let q : F →ₜ* MaxSolvQuot F m := continuousToMaxSolvQuot F m
  let qx : MaxSolvQuot F m := q x
  let hQprof : ProCGroups.IsProfiniteGroup (MaxSolvQuot F m) :=
    ProCGroups.Generation.isProfinite_quotient_closedNormal
      (G := F) (ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate C hFree.isProC)
      (N := topDerivedTop F m) (by infer_instance)
  letI : CompactSpace (MaxSolvQuot F m) := hQprof.compactSpace
  letI : T2Space (MaxSolvQuot F m) := hQprof.t2Space
  have hRangeX : Set.range X = ({x} : Set F) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      have hj : j = 0 := by
        fin_cases j
        rfl
      simp only [Fin.isValue, hj, Set.mem_singleton_iff, x]
    · intro hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      exact ⟨0, rfl⟩
  have hgenFset : ProCGroups.Generation.TopologicallyGenerates (G := F) ({x} : Set F) := by
    have hXgen := hFree.generates_range
    simpa [hRangeX] using hXgen
  have hgenQset :
      ProCGroups.Generation.TopologicallyGenerates (G := MaxSolvQuot F m)
        ({qx} : Set (MaxSolvQuot F m)) := by
    have hsurj : Function.Surjective q := continuousToMaxSolvQuot_surjective (G := F) m
    have himage :
        ProCGroups.Generation.TopologicallyGenerates (G := MaxSolvQuot F m)
          (q '' ({x} : Set F)) := by
      exact
        ProCGroups.Generation.topologicallyGenerates_image_of_continuousSurjective
          (f := q.toMonoidHom) q.continuous hsurj hgenFset
    have hImageEq : q '' ({x} : Set F) = ({qx} : Set (MaxSolvQuot F m)) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases Set.mem_singleton_iff.mp hz with rfl
        simp only [Set.mem_singleton_iff, qx]
      · intro hy
        rcases Set.mem_singleton_iff.mp hy with rfl
        exact ⟨x, by simp only [Set.mem_singleton_iff], rfl⟩
    simpa [hImageEq] using himage
  simpa [x, q, qx, map_zpow] using
    centralizerOf_zpow_eq_closedSubgroupGenerated_of_topologicallyGenerates
      (G := MaxSolvQuot F m) qx n hgenQset

/-- The pro-`Σ` finite-rank metabelian case of Theorem 1.5. -/
private theorem thm_center_free_freegroup_finiteRank_metabelian
    {sigma : Set ℕ} (_hsigma : ∃ p, p ∈ sigma ∧ Nat.Prime p)
    {r : ℕ} (X : Fin (r + 2) → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma]))
      (Fin (r + 2)) F X)
    (i : Fin (r + 2)) (n : ℤ) (hn : n ≠ 0) :
    centralizerOf (continuousToMaxSolvQuot F 2 ((X i) ^ n)) =
      closedSubgroupGenerated ({continuousToMaxSolvQuot F 2 (X i)} : Set _) := by
  apply le_antisymm
  · intro g hg
    let q : F →ₜ* MaxSolvQuot F 2 := continuousToMaxSolvQuot F 2
    let x : MaxSolvQuot F 2 := q (X i)
    let Cx : Subgroup (MaxSolvQuot F 2) :=
      closedSubgroupGenerated ({x} : Set (MaxSolvQuot F 2))
    let D : Subgroup (MaxSolvQuot F 2) :=
      topDerivedTop (MaxSolvQuot F 2) 1
    have hqpow : q ((X i) ^ n) = x ^ n := by
      simp only [x, map_zpow]
    have hjoin : g ∈ Cx ⊔ D := by
      have hle :=
        finiteRank_centralizer_le_cyclic_join_lastDerived
          (F := F) _hsigma X hFree i (m := 2) (by decide) n hn
      have hgpow : g ∈ centralizerOf (x ^ n) := by
        simpa only [hqpow] using hg
      exact hle hgpow
    have hDnormal : D.Normal := by
      change (topDerivedTop (MaxSolvQuot F 2) 1).Normal
      infer_instance
    letI : D.Normal := hDnormal
    rcases (Subgroup.mem_sup_of_normal_right (s := Cx) (t := D)).1 hjoin with
      ⟨c, hc, d, hd, hcd⟩
    have hcCent : c ∈ centralizerOf (x ^ n) :=
      mem_centralizerOf_zpow_of_mem_closedSubgroupGenerated
        (G := MaxSolvQuot F 2) (x := x) n (by simpa [Cx] using hc)
    have hcdCent : c * d ∈ centralizerOf (x ^ n) := by
      rw [hcd]
      simpa only [hqpow] using hg
    have hdCent : d ∈ centralizerOf (x ^ n) :=
      right_factor_mem_centralizerOf_of_mul_mem_and_left_mem hcCent hcdCent
    have hd_eq_one : d = 1 := by
      classical
      let hFprof : ProCGroups.IsProfiniteGroup F :=
        ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate
          (SigmaGroup[sigma]) hFree.isProC
      letI : CompactSpace F := hFprof.compactSpace
      letI : T2Space F := hFprof.t2Space
      let hQprof : ProCGroups.IsProfiniteGroup (MaxSolvQuot F 2) :=
        ProCGroups.Generation.isProfinite_quotient_closedNormal
          (G := F) hFprof (N := topDerivedTop F 2) (by infer_instance)
      letI : T2Space (MaxSolvQuot F 2) := hQprof.t2Space
      have hmap1 :
          (topDerivedTop F 1).map (q : F →* MaxSolvQuot F 2) =
            topDerivedTop (MaxSolvQuot F 2) 1 := by
        exact
          topDerived_map_eq_of_surj
            (f := q) (continuousToMaxSolvQuot_surjective (G := F) 2)
            (closedCommutator_topDerived_map_isClosed_of_compact (f := q)) 1
      have hdmap : d ∈ (topDerivedTop F 1).map (q : F →* MaxSolvQuot F 2) := by
        rw [hmap1]
        simpa [D] using hd
      rcases hdmap with ⟨a, ha_der, hqa⟩
      let HAb : Type u := TopologicalAbelianization F
      let ψ : F →ₜ* HAb := ProCGroups.Abelian.TopologicalAbelianization.mkₜ F
      have hψa : ψ a = 1 := by
        change ProCGroups.Abelian.TopologicalAbelianization.mk F a = 1
        change a ∈ ProCGroups.ProC.ProfiniteKernelSubgroup
          (ProCGroups.Abelian.TopologicalAbelianization.mkₜ F)
        rw [topologicalAbelianization_profiniteKernelSubgroup_eq_topDerivedTop_one]
        exact ha_der
      have hcommQ : ⁅x ^ n, d⁆ = 1 := by
        exact
          commutatorElement_eq_one_iff_mul_comm.2
            ((mem_centralizerOf_iff.mp hdCent).symm)
      have hqcomm : q ⁅(X i) ^ n, a⁆ = 1 := by
        rw [map_commutatorElement]
        rw [map_zpow]
        have hqa' : q a = d := by simpa using hqa
        rw [hqa']
        simpa [x] using hcommQ
      have hcomm_der2 : ⁅(X i) ^ n, a⁆ ∈ topDerivedTop F 2 :=
        (continuousToMaxSolvQuot_eq_one_iff (G := F) (m := 2)
          (x := ⁅(X i) ^ n, a⁆)).1 hqcomm
      have hψcomm : ψ ⁅(X i) ^ n, a⁆ = 1 := by
        change
          ProCGroups.Abelian.TopologicalAbelianization.mk F ⁅(X i) ^ n, a⁆ = 1
        change ⁅(X i) ^ n, a⁆ ∈ ProCGroups.ProC.ProfiniteKernelSubgroup
          (ProCGroups.Abelian.TopologicalAbelianization.mkₜ F)
        rw [topologicalAbelianization_profiniteKernelSubgroup_eq_topDerivedTop_one]
        exact (topDerivedTop_antitone (G := F) (by decide : 1 ≤ 2)) hcomm_der2
      let ProC := ProCGroups.ProC.proSigmaProC.{u} sigma
      let C : ProCGroups.FiniteGroupClass.{u} := ProC.finiteQuotientClass
      let δ := FoxDifferential.zcSeparatedUniversalDifferential C ψ.toMonoidHom
      have hcommKernel :
          (⟨⁅(X i) ^ n, a⁆, hψcomm⟩ : ProCGroups.ProC.ProfiniteKernelSubgroup ψ) ∈
            Subgroup.closedCommutator (ProCGroups.ProC.ProfiniteKernelSubgroup ψ) :=
        (mem_topDerivedTop_two_iff_mem_closedCommutator_topologicalAbelianizationKernel
          (G := F) hψcomm).1 hcomm_der2
      have hboundary :=
        CrowellExactSequence.separatedBoundaryKillsTopologicalCommutatorProCInteger
          (G := F) (H := HAb) C ψ hcommKernel
      have hδcomm_zero : δ ⁅(X i) ^ n, a⁆ = 0 := by
        change Multiplicative.ofAdd (δ ⁅(X i) ^ n, a⁆) = 1 at hboundary
        simpa using congrArg Multiplicative.toAdd hboundary
      have hδcomm_formula :
          δ ⁅(X i) ^ n, a⁆ =
            (FoxDifferential.zcGroupLike C HAb (ψ ((X i) ^ n)) - 1) • δ a := by
        exact
          FoxDifferential.zcSeparatedUniversalDifferential_commutator_right_kernel
            C ψ.toMonoidHom ((X i) ^ n) a hψa
      have hsmul_zero :
          (FoxDifferential.zcGroupLike C HAb
              ((ProCGroups.Abelian.TopologicalAbelianization.mk F (X i)) ^ n) - 1) •
              δ a = 0 := by
        have hψ_pow :
            ψ ((X i) ^ n) =
              (ProCGroups.Abelian.TopologicalAbelianization.mk F (X i)) ^ n := by
          change
            ProCGroups.Abelian.TopologicalAbelianization.mk F ((X i) ^ n) =
              (ProCGroups.Abelian.TopologicalAbelianization.mk F (X i)) ^ n
          simp only [map_zpow]
        rw [hδcomm_formula] at hδcomm_zero
        simpa only [hψ_pow] using hδcomm_zero
      let E :=
        CrowellExactSequence.finiteRank_topologicalAbelianization_sepCoordinateMap
          (F := F) X hFree
      have hE_smul_zero : E ((FoxDifferential.zcGroupLike C HAb
              ((ProCGroups.Abelian.TopologicalAbelianization.mk F (X i)) ^ n) - 1) •
              δ a) = 0 := by
        rw [hsmul_zero]
        simp only [ContinuousMonoidHom.coe_toMonoidHom, map_zero]
      have hE_delta_zero : E (δ a) = 0 := by
        funext j
        have hj := congrFun hE_smul_zero j
        have hreg :=
          non_zero_divisor_completed_abelianization_proSigmaFiniteQuotientClass
            (F := F) X hFree i n hn
        exact
          (isLeftRegular_iff_right_eq_zero_of_mul.mp hreg)
            (E (δ a) j)
              (by
                simpa only [LinearMap.map_smul, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
                  using hj)
      have ha_der2 : a ∈ topDerivedTop F 2 :=
        CrowellExactSequence.mem_topDerivedTop_two_of_finiteRank_topologicalAbelianization_sepCoordinateMap_eq_zero
          (F := F) X hFree hψa hE_delta_zero
      have hqa_one : q a = 1 :=
        (continuousToMaxSolvQuot_eq_one_iff (G := F) (m := 2) (x := a)).2 ha_der2
      calc
        d = q a := hqa.symm
        _ = 1 := hqa_one
    have hg_eq_c : g = c := by
      calc
        g = c * d := hcd.symm
        _ = c := by rw [hd_eq_one, mul_one]
    rw [hg_eq_c]
    simpa only [Cx] using hc
  · simpa [map_zpow] using
      (closedSubgroupGenerated_singleton_le_centralizerOf_zpow
        (G := MaxSolvQuot F 2) (continuousToMaxSolvQuot F 2 (X i)) n)

/-- The Reidemeister--Schreier input used in the induction step for Section 1.

For an open subgroup of a finite-rank free pro-`C` group, if the first positive power `x^N` of a
basis element `x` lies in the subgroup, one can choose a finite-rank Reidemeister--Schreier basis
whose image contains `x^N`.  The hypothesis `hpow_ne` is the nontriviality input actually needed:
it supplies, from outside this lemma, that no positive power of the free generator is trivial. -/
private theorem exists_rs_basis_openSubgroup_containing_minimal_power
    [hExtFact : Fact (ProCGroups.FiniteGroupClass.ExtensionClosed C)]
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Finite X]
    {ι : X → F}
    (hF : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) (x : X)
    (hpow_ne : ∀ N : ℕ, 0 < N → (ι x) ^ N ≠ 1) :
    ∃ N : ℕ, ∃ _hN : 0 < N,
      ∃ hpow : (ι x) ^ N ∈ (H : Subgroup F),
        (∀ m : ℕ, 0 < m → m < N → (ι x) ^ m ∉ (H : Subgroup F)) ∧
        ∃ Fdata : ProCGroups.FreeProC.FreeProCGroupOnConvergingSetData
            (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
          ∃ e : Fdata.carrier ≃ₜ* ↥(H : Subgroup F),
            (⟨(ι x) ^ N, hpow⟩ : ↥(H : Subgroup F)) ∈
              Set.range (e ∘ Fdata.inclusion) ∧
            Cardinal.mk Fdata.basis =
              (_root_.ReidemeisterSchreier.Schreier.rankTransform
                (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) : Cardinal) := by
  classical
  let hFprof : ProCGroups.IsProfiniteGroup F :=
    ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate C hF.isProC
  letI : CompactSpace F := hFprof.compactSpace
  letI : T2Space F := hFprof.t2Space
  letI : Finite (Set.range ι) := (Set.finite_range ι).to_subtype
  letI : DiscreteTopology (Set.range ι) :=
    DiscreteTopology.of_finite_of_isClosed_singleton fun _ => isClosed_singleton
  let P : ℕ → Prop := fun N => 0 < N ∧ (ι x) ^ N ∈ (H : Subgroup F)
  have hP : ∃ N : ℕ, P N :=
    ProCGroups.exists_pos_pow_mem_openSubgroup (G := F) H (ι x)
  let N : ℕ := Nat.find hP
  have hNpow : P N := Nat.find_spec hP
  have hmin : ∀ m : ℕ, 0 < m → m < N → (ι x) ^ m ∉ (H : Subgroup F) := by
    intro m hm hlt hmH
    exact Nat.find_min hP hlt ⟨hm, hmH⟩
  have hVar : ProCGroups.FiniteGroupClass.Variety C := Fact.out
  have hIso : ProCGroups.FiniteGroupClass.IsomClosed C := hCIsomClosed.out
  have hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C := hExtFact.out
  rcases
      ReidemeisterSchreier.Profinite.exists_basis_openSubgroup_of_extensionClosed_finiteRank_of_minimalGeneratorPower
        (C := C) hVar hIso hExt hcyc hF H x hNpow.1 hNpow.2
        (hpow_ne N hNpow.1) hmin with
    ⟨Fdata, e, hpower_range, hcard⟩
  exact ⟨N, hNpow.1, hNpow.2, hmin, Fdata, e, hpower_range, hcard⟩

/-- The pro-`Σ` finite-rank induction step for Theorem 1.5. -/
private theorem thm_center_free_freegroup_finiteRank_openSubgroupStep
    {sigma : Set ℕ} (_hsigma : ∃ p, p ∈ sigma ∧ Nat.Prime p)
    {r m : ℕ} (X : Fin (r + 2) → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma]))
      (Fin (r + 2)) F X)
    (hm : 3 ≤ m)
    (ih :
      ∀ {F' : Type u} [TopologicalSpace F'] [Group F'] [IsTopologicalGroup F'],
        ∀ {r' : ℕ} (Y : Fin r' → F'),
        ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
          (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma]))
          (Fin r') F' Y →
        ∀ i : Fin r', ∀ n : ℤ, n ≠ 0 →
          centralizerOf (continuousToMaxSolvQuot F' (m - 1) ((Y i) ^ n)) =
            closedSubgroupGenerated ({continuousToMaxSolvQuot F' (m - 1) (Y i)} : Set _))
    (i : Fin (r + 2)) (n : ℤ) (hn : n ≠ 0) :
    centralizerOf (continuousToMaxSolvQuot F m ((X i) ^ n)) =
      closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X i)} : Set _) := by
  apply le_antisymm
  · intro g hg
    let q : F →ₜ* MaxSolvQuot F m := continuousToMaxSolvQuot F m
    let x : MaxSolvQuot F m := q (X i)
    let Cx : Subgroup (MaxSolvQuot F m) :=
      closedSubgroupGenerated ({x} : Set (MaxSolvQuot F m))
    let D : Subgroup (MaxSolvQuot F m) :=
      topDerivedTop (MaxSolvQuot F m) (m - 1)
    have hqpow : q ((X i) ^ n) = x ^ n := by
      simp only [x, map_zpow]
    have hjoin : g ∈ Cx ⊔ D := by
      have hle :=
        finiteRank_centralizer_le_cyclic_join_lastDerived
          (F := F) _hsigma X hFree i (m := m) (Nat.le_trans (by decide) hm) n hn
      have hgpow : g ∈ centralizerOf (x ^ n) := by
        simpa only [hqpow] using hg
      exact hle hgpow
    have hDnormal : D.Normal := by
      change (topDerivedTop (MaxSolvQuot F m) (m - 1)).Normal
      infer_instance
    letI : D.Normal := hDnormal
    rcases (Subgroup.mem_sup_of_normal_right (s := Cx) (t := D)).1 hjoin with
      ⟨c, hc, d, hd, hcd⟩
    have hcCent : c ∈ centralizerOf (x ^ n) :=
      mem_centralizerOf_zpow_of_mem_closedSubgroupGenerated
        (G := MaxSolvQuot F m) (x := x) n (by simpa [Cx] using hc)
    have hcdCent : c * d ∈ centralizerOf (x ^ n) := by
      rw [hcd]
      simpa only [hqpow] using hg
    have hdCent : d ∈ centralizerOf (x ^ n) :=
      right_factor_mem_centralizerOf_of_mul_mem_and_left_mem hcCent hcdCent
    have hd_eq_one : d = 1 := by
      classical
      let hFprof : ProCGroups.IsProfiniteGroup F :=
        ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate
          (SigmaGroup[sigma]) hFree.isProC
      letI : CompactSpace F := hFprof.compactSpace
      letI : T2Space F := hFprof.t2Space
      let hQprof : ProCGroups.IsProfiniteGroup (MaxSolvQuot F m) :=
        ProCGroups.Generation.isProfinite_quotient_closedNormal
          (G := F) hFprof (N := topDerivedTop F m) (by infer_instance)
      letI : CompactSpace (MaxSolvQuot F m) := hQprof.compactSpace
      letI : T2Space (MaxSolvQuot F m) := hQprof.t2Space
      letI : TotallyDisconnectedSpace (MaxSolvQuot F m) :=
        hQprof.totallyDisconnectedSpace
      have hQm : topDerivedTop (MaxSolvQuot F m) m = ⊥ := by
        have hmapm :
            (topDerivedTop F m).map (q : F →* MaxSolvQuot F m) =
              topDerivedTop (MaxSolvQuot F m) m := by
          exact
            topDerived_map_eq_of_surj
              (f := q) (continuousToMaxSolvQuot_surjective (G := F) m)
              (closedCommutator_topDerived_map_isClosed_of_compact (f := q)) m
        rw [← hmapm]
        refine
          (Subgroup.map_eq_bot_iff
            (f := (q : F →* MaxSolvQuot F m)) (H := topDerivedTop F m)).2 ?_
        intro y hy
        exact (MonoidHom.mem_ker).2
          ((continuousToMaxSolvQuot_eq_one_iff (G := F) (m := m) (x := y)).2 hy)
      exact
        eq_one_of_mem_all_openNormalSubgroup_derived
          (Q := MaxSolvQuot F m) hm hQm (by
            intro H hH
            let Q : Type u := MaxSolvQuot F m
            let Hopen : OpenSubgroup Q := H.toOpenSubgroup
            let Hpre : OpenSubgroup F := preimageOpenSubgroup q Hopen
            let qH : ↥(Hpre : Subgroup F) →ₜ* ↥(H : Subgroup Q) := by
              simpa [Hpre, Hopen, Q] using
                (q.restrictPreimage (H : Subgroup Q))
            have hmap_last :
                (topDerivedTop F (m - 1)).map (q : F →* Q) =
                  topDerivedTop Q (m - 1) := by
              exact
                topDerived_map_eq_of_surj
                  (f := q) (continuousToMaxSolvQuot_surjective (G := F) m)
                  (closedCommutator_topDerived_map_isClosed_of_compact (f := q)) (m - 1)
            have hdmap : d ∈ (topDerivedTop F (m - 1)).map (q : F →* Q) := by
              rw [hmap_last]
              simpa [D, Q] using hd
            rcases hdmap with ⟨a, ha_der, hqa⟩
            have hm_pred_one : 1 ≤ m - 1 := by omega
            have hm_one : 1 ≤ m := le_trans (by decide : 1 ≤ 3) hm
            have hF1_le_Hpre : topDerivedTop F 1 ≤ (Hpre : Subgroup F) := by
              intro y hy
              change q y ∈ (H : Subgroup Q)
              exact hH ((topDerivedTop_le_comap (f := q) (m := 1)) hy)
            have hD_le_one : topDerivedTop Q (m - 1) ≤ topDerivedTop Q 1 := by
              exact topDerivedTop_antitone (G := Q) hm_pred_one
            have hdH : d ∈ (H : Subgroup Q) :=
              hH (hD_le_one (by simpa [D, Q] using hd))
            have haHpre : a ∈ (Hpre : Subgroup F) := by
              change q a ∈ (H : Subgroup Q)
              have hqa' : q a = d := by simpa using hqa
              rw [hqa']
              exact hdH
            let aH : ↥(Hpre : Subgroup F) := ⟨a, haHpre⟩
            have hFm_le_Hpre :
                topDerivedTop F m ≤
                  (topDerivedTop ↥(Hpre : Subgroup F) (m - 1)).map
                    (Subgroup.subtype (Hpre : Subgroup F)) :=
              topDerivedTop_le_openSubgroup_pred_map_of_first_le
                (G := F) Hpre hm_one hF1_le_Hpre
            have haH_der_one : aH ∈ topDerivedTop ↥(Hpre : Subgroup F) 1 := by
              have hm_pred_pred_one : 1 ≤ (m - 1) - 1 := by
                omega
              have ha_map :
                  a ∈ (topDerivedTop ↥(Hpre : Subgroup F) ((m - 1) - 1)).map
                    (Subgroup.subtype (Hpre : Subgroup F)) :=
                topDerivedTop_le_openSubgroup_pred_map_of_first_le
                  (G := F) Hpre hm_pred_one hF1_le_Hpre ha_der
              rcases ha_map with ⟨b, hb, hba⟩
              have hb1 : b ∈ topDerivedTop ↥(Hpre : Subgroup F) 1 :=
                topDerivedTop_antitone (G := ↥(Hpre : Subgroup F)) hm_pred_pred_one hb
              have hb_eq : b = aH := by
                apply Subtype.ext
                simpa [aH] using hba
              simpa [hb_eq] using hb1
            have haH_last : aH ∈ topDerivedTop ↥(Hpre : Subgroup F) (m - 1) := by
              letI : Fact (ProCGroups.FiniteGroupClass.ExtensionClosed (SigmaGroup[sigma])) :=
                ⟨ProCGroups.FiniteGroupClass.sigmaGroup_extensionClosed sigma⟩
              let XU : ULift.{u} (Fin (r + 2)) → F := fun k => X k.down
              have hFreeU :
                  ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
                    (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma]))
                    (ULift.{u} (Fin (r + 2))) F XU := by
                simpa [XU] using
                  hFree.precompEquiv (Equiv.ulift : ULift.{u} (Fin (r + 2)) ≃ Fin (r + 2))
              rcases
                  exists_rs_basis_openSubgroup_containing_minimal_power
                    (C := SigmaGroup[sigma])
                    (hcyc := ProCGroups.FiniteGroupClass.sigmaGroup_nontrivialCyclic
                      (sigma := sigma) _hsigma)
                    (F := F) (X := ULift.{u} (Fin (r + 2))) (ι := XU)
                    hFreeU Hpre (ULift.up i)
                    (fun N hN =>
                      by
                        simpa [XU] using
                          hFree.generator_pow_ne_one_of_sigma _hsigma i N hN) with
                ⟨N, hNpos, hpow, _hmin, Fdata, e, hpower_range, hcard⟩
              have hFdataFinite : Finite Fdata.basis := by
                have hlt : Cardinal.mk Fdata.basis < Cardinal.aleph0 := by
                  rw [hcard]
                  exact Cardinal.natCast_lt_aleph0
                exact Cardinal.lt_aleph0_iff_finite.mp hlt
              letI : Fintype Fdata.basis := Fintype.ofFinite Fdata.basis
              let rH : ℕ := Fintype.card Fdata.basis
              let eFin : Fin rH ≃ Fdata.basis := (Fintype.equivFin Fdata.basis).symm
              let Y : Fin rH → ↥(Hpre : Subgroup F) :=
                fun k => e (Fdata.inclusion (eFin k))
              have hHpreProC :
                  ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma])
                    (G := ↥(Hpre : Subgroup F)) := by
                exact
                  ProCGroups.ProC.IsProCGroup.of_isClosed_subgroup
                    (ProCGroups.FiniteGroupClass.sigmaGroup_isomClosed sigma)
                    (ProCGroups.FiniteGroupClass.sigmaGroup_subgroupClosed sigma)
                    (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed sigma)
                    hFree.isProC (Hpre : Subgroup F)
                    (ProCGroups.openSubgroup_isClosed (G := F) Hpre)
              have hFreeY :
                  ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
                    (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma]))
                    (Fin rH) ↥(Hpre : Subgroup F) Y := by
                have hpre :=
                  Fdata.isFree.precompEquiv eFin
                exact hpre.ofContinuousMulEquiv e hHpreProC
              rcases hpower_range with ⟨b0, hb0⟩
              let j0 : Fin rH := eFin.symm b0
              let xN_H : ↥(Hpre : Subgroup F) := ⟨(XU (ULift.up i)) ^ N, hpow⟩
              have hYj0 : Y j0 = xN_H := by
                change e (Fdata.inclusion (eFin (eFin.symm b0))) = xN_H
                simpa [Y, j0, xN_H] using hb0
              have hdCentN : d ∈ centralizerOf ((x ^ N) ^ n) := by
                have hdNat :
                    d ∈ centralizerOf (x ^ (n.natAbs : ℤ)) :=
                  mem_centralizerOf_zpow_natAbs_of_mem_zpow hn hdCent
                have hdNatNat :
                    d ∈ centralizerOf (x ^ n.natAbs) := by
                  rw [zpow_natCast] at hdNat
                  exact hdNat
                have hdPow :
                    d ∈ centralizerOf ((x ^ n.natAbs) ^ N) :=
                  mem_centralizerOf_pow_of_mem hdNatNat N
                have hdTargetNat :
                    d ∈ centralizerOf ((x ^ N) ^ (n.natAbs : ℤ)) := by
                  have hpoweq : (x ^ N) ^ n.natAbs = (x ^ n.natAbs) ^ N := by
                    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
                  rw [zpow_natCast]
                  simpa [hpoweq] using hdPow
                rw [centralizerOf_zpow_eq_natAbs (x ^ N) hn]
                exact hdTargetNat
              have hcommQ : ⁅(x ^ N) ^ n, d⁆ = 1 := by
                exact
                  commutatorElement_eq_one_iff_mul_comm.2
                    ((mem_centralizerOf_iff.mp hdCentN).symm)
              have hqcommF : q ⁅((X i) ^ N) ^ n, a⁆ = 1 := by
                have hqa' : q a = d := by simpa using hqa
                rw [map_commutatorElement, map_zpow]
                change ⁅(q ((X i) ^ N)) ^ n, q a⁆ = 1
                have hqXiN : q ((X i) ^ N) = q (X i) ^ N := by simp only [map_pow]
                rw [hqXiN]
                change ⁅(q (X i) ^ N) ^ n, q a⁆ = 1
                rw [hqa']
                simpa [x] using hcommQ
              have hcommF_der :
                  ⁅((X i) ^ N) ^ n, a⁆ ∈ topDerivedTop F m :=
                (continuousToMaxSolvQuot_eq_one_iff
                  (G := F) (m := m) (x := ⁅((X i) ^ N) ^ n, a⁆)).1 hqcommF
              have hcommH_der :
                  ⁅xN_H ^ n, aH⁆ ∈ topDerivedTop ↥(Hpre : Subgroup F) (m - 1) := by
                have hcomm_map := hFm_le_Hpre hcommF_der
                rcases hcomm_map with ⟨w, hw, hwval⟩
                have hw_eq : w = ⁅xN_H ^ n, aH⁆ := by
                  apply Subtype.ext
                  simpa [xN_H, XU, aH, commutatorElement_def] using hwval
                rwa [← hw_eq]
              let qpre : ↥(Hpre : Subgroup F) →ₜ*
                  MaxSolvQuot ↥(Hpre : Subgroup F) (m - 1) :=
                continuousToMaxSolvQuot ↥(Hpre : Subgroup F) (m - 1)
              have hqpre_comm :
                  qpre ⁅xN_H ^ n, aH⁆ = 1 :=
                (continuousToMaxSolvQuot_eq_one_iff
                  (G := ↥(Hpre : Subgroup F)) (m := m - 1)
                  (x := ⁅xN_H ^ n, aH⁆)).2 hcommH_der
              have hcommQuot :
                  ⁅qpre (xN_H ^ n), qpre aH⁆ = 1 := by
                simpa [map_commutatorElement] using hqpre_comm
              have haH_cent :
                  qpre aH ∈ centralizerOf (qpre (xN_H ^ n)) := by
                rw [mem_centralizerOf_iff]
                exact (commutatorElement_eq_one_iff_mul_comm.1 hcommQuot).symm
              have hcent_formula :=
                ih Y hFreeY j0 n hn
              have haH_cyc :
                  qpre aH ∈
                    (closedSubgroupGenerated ({qpre (Y j0)} : Set _) :
                      Subgroup (MaxSolvQuot ↥(Hpre : Subgroup F) (m - 1))) := by
                rw [← hcent_formula]
                simpa [qpre, hYj0, map_zpow] using haH_cent
              have haHq_der :
                  qpre aH ∈
                    topDerivedTop (MaxSolvQuot ↥(Hpre : Subgroup F) (m - 1)) 1 := by
                exact topDerived_map_le (f := qpre) (m := 1) ⟨aH, haH_der_one, rfl⟩
              have hcycInf :
                  (closedSubgroupGenerated ({qpre (Y j0)} : Set _) :
                      Subgroup (MaxSolvQuot ↥(Hpre : Subgroup F) (m - 1))) ⊓
                    topDerivedTop (MaxSolvQuot ↥(Hpre : Subgroup F) (m - 1)) 1 = ⊥ := by
                simpa [qpre] using
                  closedSubgroupGenerated_singleton_inf_topDerivedTop_one_eq_bot_of_free_generator
                    (C := SigmaGroup[sigma]) (F := ↥(Hpre : Subgroup F))
                    Y hFreeY j0 (m - 1)
              have hqpre_a_bot :
                  qpre aH ∈
                    (⊥ : Subgroup (MaxSolvQuot ↥(Hpre : Subgroup F) (m - 1))) := by
                have hinf :
                    qpre aH ∈
                      (closedSubgroupGenerated ({qpre (Y j0)} : Set _) :
                          Subgroup (MaxSolvQuot ↥(Hpre : Subgroup F) (m - 1))) ⊓
                        topDerivedTop (MaxSolvQuot ↥(Hpre : Subgroup F) (m - 1)) 1 :=
                  ⟨haH_cyc, haHq_der⟩
                rw [← hcycInf]
                exact hinf
              have hqpre_a_one : qpre aH = 1 :=
                Subgroup.mem_bot.mp hqpre_a_bot
              exact
                (continuousToMaxSolvQuot_eq_one_iff
                  (G := ↥(Hpre : Subgroup F)) (m := m - 1) (x := aH)).1
                  hqpre_a_one
            have hqH_der :
                qH aH ∈ topDerivedTop ↥(H : Subgroup Q) (m - 1) := by
              exact topDerived_map_le (f := qH) (m := m - 1) ⟨aH, haH_last, rfl⟩
            refine ⟨qH aH, hqH_der, ?_⟩
            change (qH aH : Q) = d
            simpa [qH, aH, hqa])
    have hg_eq_c : g = c := by
      calc
        g = c * d := hcd.symm
        _ = c := by rw [hd_eq_one, mul_one]
    rw [hg_eq_c]
    simpa only [Cx] using hc
  · simpa [map_zpow] using
      (closedSubgroupGenerated_singleton_le_centralizerOf_zpow
        (G := MaxSolvQuot F m) (continuousToMaxSolvQuot F m (X i)) n)

/-- The pro-`Σ` finite-rank case, reduced to the metabelian base case and the induction step. -/
private theorem thm_center_free_freegroup_finiteRank
    {sigma : Set ℕ} (hsigma : ∃ p, p ∈ sigma ∧ Nat.Prime p)
    {r : ℕ} (X : Fin r → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma]))
      (Fin r) F X)
    (i : Fin r) (m : ℕ) (hm : 2 ≤ m) (n : ℤ) (hn : n ≠ 0) :
    centralizerOf (continuousToMaxSolvQuot F m ((X i) ^ n)) =
      closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X i)} : Set _) := by
  cases r with
  | zero =>
      exact Fin.elim0 i
  | succ r =>
      have hmain :
          ∀ m : ℕ, 2 ≤ m →
            ∀ {r' : ℕ} {F' : Type u}
              [TopologicalSpace F'] [Group F'] [IsTopologicalGroup F'],
              ∀ Y : Fin r' → F',
              ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
                (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma]))
                (Fin r') F' Y →
              ∀ i : Fin r', ∀ n : ℤ, n ≠ 0 →
                centralizerOf (continuousToMaxSolvQuot F' m ((Y i) ^ n)) =
                  closedSubgroupGenerated ({continuousToMaxSolvQuot F' m (Y i)} : Set _) := by
        intro m
        refine Nat.strong_induction_on m ?_
        intro m ih hm r' F' _ _ _ Y hFreeY i n hn
        cases r' with
        | zero =>
            exact Fin.elim0 i
        | succ r' =>
            cases r' with
            | zero =>
                have hi0 : i = 0 := by
                  fin_cases i
                  rfl
                simpa [hi0] using
                  thm_center_free_freegroup_finiteRank_rankOne
                    (C := SigmaGroup[sigma]) (F := F') Y hFreeY m n
            | succ r' =>
                by_cases hm2 : m = 2
                · subst hm2
                  exact
                    thm_center_free_freegroup_finiteRank_metabelian
                      (F := F') hsigma Y hFreeY i n hn
                · have hlt : 2 < m := lt_of_le_of_ne hm (Ne.symm hm2)
                  have hm3 : 3 ≤ m := Nat.succ_le_of_lt hlt
                  refine
                    thm_center_free_freegroup_finiteRank_openSubgroupStep
                      (F := F') hsigma Y hFreeY hm3 ?_ i n hn
                  intro F'' _ _ _ r'' Z hFreeZ j z hz
                  exact
                    ih (m - 1)
                      (Nat.sub_lt (show 0 < m by exact lt_trans (by decide) hlt) (by decide))
                      (Nat.le_sub_of_add_le hm3) Z hFreeZ j z hz
      exact hmain m hm (F' := F) X hFree i n hn

/-- Theorem 1.5 for a finite pro-`Σ` basis family. -/
private theorem thm_center_free_freegroup_finiteFamily
    {sigma : Set ℕ} (hsigma : ∃ p, p ∈ sigma ∧ Nat.Prime p)
    {ι : Type v} [Finite ι] (X : ι → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma])) ι F X)
    (i : ι) (m : ℕ) (hm : 2 ≤ m) (n : ℤ) (hn : n ≠ 0) :
    centralizerOf (continuousToMaxSolvQuot F m ((X i) ^ n)) =
      closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X i)} : Set _) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let r : ℕ := Fintype.card ι
  let e : ι ≃ Fin r := Fintype.equivFin ι
  let Xfin : Fin r → F := fun k => X (e.symm k)
  have hFreeFin : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma]))
      (Fin r) F Xfin :=
    finiteFamily_to_finiteRank (C := SigmaGroup[sigma]) X hFree
  have hcore :
      centralizerOf (continuousToMaxSolvQuot F m ((Xfin (e i)) ^ n)) =
        closedSubgroupGenerated ({continuousToMaxSolvQuot F m (Xfin (e i))} : Set _) :=
    thm_center_free_freegroup_finiteRank hsigma Xfin hFreeFin (e i) m hm n hn
  simpa [Xfin, e] using hcore

/-- The centralizer formula for maximal solvable quotients of free pro-`Σ` groups. -/
theorem theorem_1_5_center_free_freegroup
    {sigma : Set ℕ} (hsigma : ∃ p, p ∈ sigma ∧ Nat.Prime p)
    {ι : Type v} (X : ι → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma])) ι F X)
    (i : ι) (m : ℕ) (hm : 2 ≤ m) (n : ℤ) (hn : n ≠ 0) :
    centralizerOf (continuousToMaxSolvQuot F m ((X i) ^ n)) =
      closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X i)} : Set _) := by
  classical
  let Q : Type u := MaxSolvQuot F m
  let π : F →ₜ* Q := continuousToMaxSolvQuot F m
  let x : Q := π (X i)
  let hQprof : ProCGroups.IsProfiniteGroup Q :=
    ProCGroups.Generation.isProfinite_quotient_closedNormal
      (G := F)
      (ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate
        (SigmaGroup[sigma]) hFree.isProC)
      (N := topDerivedTop F m) (by infer_instance)
  letI : CompactSpace Q := hQprof.compactSpace
  letI : T2Space Q := hQprof.t2Space
  letI : TotallyDisconnectedSpace Q := hQprof.totallyDisconnectedSpace
  apply le_antisymm
  · intro g hg
    by_contra hgcyc
    let Cyc : ClosedSubgroup Q :=
      closedSubgroupGenerated ({x} : Set Q)
    obtain ⟨U, hC_le_U, hgU⟩ :=
      ProCGroups.ProC.exists_openSubgroup_ge_closedSubgroup_not_mem
        (G := Q) hQprof Cyc hgcyc
    let k : ℕ := Nat.card (Q ⧸ ((U : OpenSubgroup Q) : Subgroup Q))
    let hUfinite : Finite (Q ⧸ ((U : OpenSubgroup Q) : Subgroup Q)) :=
      ProCGroups.openSubgroup_finiteQuotient (G := Q) U
    let ψ : Q →ₜ* Equiv.Perm (Fin k) :=
      ProCGroups.FiniteGeneration.openSubgroupIndexContinuousHom
        (G := Q) (H := (U : Subgroup Q)) U.isOpen' hUfinite (n := k) rfl
    let b : Fin k :=
      ProCGroups.FiniteGeneration.openSubgroupIndexBasepoint
        (G := Q) (H := (U : Subgroup Q)) hUfinite (n := k) rfl
    have hψg_move : ψ g b ≠ b := by
      intro hfix
      have hgU' : g ∈ (U : Subgroup Q) := by
        rw [ProCGroups.FiniteGeneration.mem_openSubgroup_iff_indexAction_fix_basepoint
          (G := Q) (H := (U : Subgroup Q)) hUfinite (n := k) rfl (g := g)]
        simpa [ψ, b, k] using hfix
      exact hgU hgU'
    have hψ_not_image :
        ψ g ∉ ψ '' ((closedSubgroupGenerated ({x} : Set Q) : Subgroup Q) : Set Q) := by
      rintro ⟨c, hc, hcg⟩
      have hcfix :
          ψ c b = b := by
        have hcU : c ∈ (U : Subgroup Q) := hC_le_U hc
        rw [ProCGroups.FiniteGeneration.mem_openSubgroup_iff_indexAction_fix_basepoint
          (G := Q) (H := (U : Subgroup Q)) hUfinite (n := k) rfl (g := c)] at hcU
        simpa [ψ, b, k] using hcU
      have hgfix : ψ g b = b := by simpa [hcg] using hcfix
      exact hψg_move hgfix
    let Supp : Set ι := {j | ψ (π (X j)) ≠ 1}
    let oneU : OpenSubgroup (Equiv.Perm (Fin k)) :=
      { toSubgroup := ⊥
        isOpen' := by
          exact
            isOpen_discrete
              (s := (((⊥ : Subgroup (Equiv.Perm (Fin k))) :
                Set (Equiv.Perm (Fin k))))) }
    have hSuppFinite : Supp.Finite := by
      have hconvψ :
        ProCGroups.FreeProC.FamilyConvergesToOne (G := Equiv.Perm (Fin k))
            (fun j => ψ (π (X j))) :=
        ProCGroups.FreeProC.FamilyConvergesToOne.comp (G := F) (H := Equiv.Perm (Fin k))
          (μ := X) hFree.convergesToOne (ψ.comp π)
      simpa [Supp, oneU] using hconvψ oneU
    let S : Finset ι := insert i hSuppFinite.toFinset
    have hiS : i ∈ S := by simp only [Finset.mem_insert, Set.Finite.mem_toFinset, true_or, S]
    have hψOutside : ∀ j, j ∉ S → ψ (π (X j)) = 1 := by
      intro j hj
      by_contra hj1
      exact hj (by simp only [ne_eq, Finset.mem_insert, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hj1, not_false_eq_true,
  or_true, S, Supp])
    let R : Type u := hFree.FinsetSupportRetract S
    let B : S → R := hFree.finsetSupportBasis S
    let ρQ : Q →ₜ* MaxSolvQuot R m := finsetSupportRangeQuot X hFree S m
    let ιQ : MaxSolvQuot R m →ₜ* Q := finsetSupportInclusionQuot X hFree S m
    let iS : S := ⟨i, hiS⟩
    let xR : MaxSolvQuot R m := continuousToMaxSolvQuot R m (B iS)
    have hxR : ρQ x = xR := by
      have hxRange : hFree.collapseToFinsetRange S (X i) = B iS := by
        apply Subtype.ext
        change (hFree.collapseToFinset S (X i) : F) = X i
        simpa [B, ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet.collapseToFinsetRange,
          ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet.finsetSupportBasis] using
          hFree.collapseToFinset_apply_mem (S := S) hiS
      change
        finsetSupportRangeQuot X hFree S m (continuousToMaxSolvQuot F m (X i)) =
          continuousToMaxSolvQuot R m (B iS)
      rw [finsetSupportRangeQuot_apply]
      exact congrArg (continuousToMaxSolvQuot R m) hxRange
    have hιxR : ιQ xR = x := by
      change
        finsetSupportInclusionQuot X hFree S m
            (continuousToMaxSolvQuot R m (B iS)) =
          continuousToMaxSolvQuot F m (X i)
      rw [finsetSupportInclusionQuot_apply]
      rfl
    have hgRcent : ρQ g ∈ centralizerOf (xR ^ n) := by
      rw [mem_centralizerOf_iff]
      have hcomm :
          g * (continuousToMaxSolvQuot F m (X i)) ^ n =
            (continuousToMaxSolvQuot F m (X i)) ^ n * g := by
        have hg' :
            g ∈ centralizerOf ((continuousToMaxSolvQuot F m (X i)) ^ n) := by
          simpa [map_zpow] using hg
        exact mem_centralizerOf_iff.mp hg'
      have hxR' : ρQ (continuousToMaxSolvQuot F m (X i)) = xR := by
        simpa [x, π] using hxR
      have hxRn :
          ρQ ((continuousToMaxSolvQuot F m (X i)) ^ n) = xR ^ n := by
        calc
          ρQ ((continuousToMaxSolvQuot F m (X i)) ^ n)
              = (ρQ (continuousToMaxSolvQuot F m (X i))) ^ n := by simp only [map_zpow]
          _ = xR ^ n := by rw [hxR']
      simpa [map_mul, hxRn] using congrArg ρQ hcomm
    have hFreeR :
        ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
          (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma])) S R B :=
      hFree.isFreeProCGroupOnConvergingSet_finsetSupportBasis S
    have hcentR :
        centralizerOf (continuousToMaxSolvQuot R m ((B iS) ^ n)) =
          closedSubgroupGenerated ({continuousToMaxSolvQuot R m (B iS)} : Set _) :=
      thm_center_free_freegroup_finiteFamily
        (F := R) hsigma B hFreeR iS m hm n hn
    have hgRcyc : ρQ g ∈
        (closedSubgroupGenerated ({xR} : Set (MaxSolvQuot R m)) :
          Subgroup (MaxSolvQuot R m)) := by
      rw [← hcentR]
      simpa [xR, map_zpow] using hgRcent
    have hcollapsedC :
        collapseToFinsetQuot X hFree S m g ∈
          (closedSubgroupGenerated ({x} : Set Q) : Subgroup Q) := by
      have hmap :
          ιQ (ρQ g) ∈
            (closedSubgroupGenerated ({ιQ xR} : Set Q) : Subgroup Q) :=
        ProCGroups.Generation.map_mem_closedSubgroupGenerated_singleton ιQ xR hgRcyc
      have hcompg :
          ιQ (ρQ g) = collapseToFinsetQuot X hFree S m g := by
        obtain ⟨x, rfl⟩ := continuousToMaxSolvQuot_surjective (G := F) m g
        have hcomp :
            (hFree.collapseToFinsetInclusion S).comp (hFree.collapseToFinsetRange S) =
              hFree.collapseToFinset S := by
          ext x
          rfl
        change
          finsetSupportInclusionQuot X hFree S m
              (finsetSupportRangeQuot X hFree S m (continuousToMaxSolvQuot F m x)) =
            collapseToFinsetQuot X hFree S m (continuousToMaxSolvQuot F m x)
        rw [finsetSupportRangeQuot_apply, finsetSupportInclusionQuot_apply]
        exact congrArg
          (fun y : F => continuousToMaxSolvQuot F m y)
          (congrArg (fun f : F →ₜ* F => f x) hcomp)
      exact hcompg ▸ (by simpa [hιxR] using hmap)
    have hψfactor :
        ψ.comp (collapseToFinsetQuot X hFree S m) = ψ :=
      comp_collapseToFinsetQuot_eq_of_eq_one_outside (X := X) hFree S m ψ hψOutside
    have hψcollapsed : ψ (collapseToFinsetQuot X hFree S m g) = ψ g := by
      exact congrArg (fun f : Q →ₜ* Equiv.Perm (Fin k) => f g) hψfactor
    have hψimg : ψ g ∈
        ψ '' ((closedSubgroupGenerated ({x} : Set Q) : Subgroup Q) : Set Q) := by
      have : ψ (collapseToFinsetQuot X hFree S m g) ∈
          ψ '' ((closedSubgroupGenerated ({x} : Set Q) : Subgroup Q) : Set Q) :=
        ⟨collapseToFinsetQuot X hFree S m g, hcollapsedC, rfl⟩
      simpa [hψcollapsed] using this
    exact hψ_not_image hψimg
  · have hcyc :
      closedSubgroupGenerated ({continuousToMaxSolvQuot F m (X i)} : Set _) ≤
          centralizerOf
            ((continuousToMaxSolvQuot F m (X i)) ^ n) :=
      closedSubgroupGenerated_singleton_le_centralizerOf_zpow
        (continuousToMaxSolvQuot F m (X i)) n
    simpa [map_zpow] using hcyc

/-- A group is slim if two elements satisfy the centralizer formula and their closed cyclic
subgroups have trivial intersection. -/
private theorem isSlim_of_two_elements_with_centralizer_formula
    [CompactSpace G]
    (x x' : G)
    (hcentx : ∀ n : ℕ, 0 < n → centralizerOf (x ^ n) =
      (closedSubgroupGenerated ({x} : Set G) : Subgroup G))
    (hcentx' : ∀ n : ℕ, 0 < n → centralizerOf (x' ^ n) =
      (closedSubgroupGenerated ({x'} : Set G) : Subgroup G))
    (htriv : (closedSubgroupGenerated ({x} : Set G) : Subgroup G) ⊓
      (closedSubgroupGenerated ({x'} : Set G) : Subgroup G) = ⊥) :
    IsSlim G := by
  refine (isSlim_iff_openSubgroups_center_eq_bot (G := G)).2 ?_
  intro H
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  obtain ⟨n, hn, hxn⟩ := ProCGroups.exists_pos_pow_mem_openSubgroup (G := G) H x
  obtain ⟨n', hn', hx'n'⟩ := ProCGroups.exists_pos_pow_mem_openSubgroup (G := G) H x'
  have hzcentx : (z : G) ∈ centralizerOf (x ^ n) := by
    rw [mem_centralizerOf_iff]
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨x ^ n, hxn⟩)).symm
  have hzcentx' : (z : G) ∈ centralizerOf (x' ^ n') := by
    rw [mem_centralizerOf_iff]
    exact (congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨x' ^ n', hx'n'⟩)).symm
  have hzx : (z : G) ∈ (closedSubgroupGenerated ({x} : Set G) : Subgroup G) := by
    rw [← hcentx n hn]
    exact hzcentx
  have hzx' : (z : G) ∈ (closedSubgroupGenerated ({x'} : Set G) : Subgroup G) := by
    rw [← hcentx' n' hn']
    exact hzcentx'
  have hzbot : (z : G) ∈ (⊥ : Subgroup G) := by
    have hzinf : (z : G) ∈ (closedSubgroupGenerated ({x} : Set G) : Subgroup G) ⊓
        (closedSubgroupGenerated ({x'} : Set G) : Subgroup G) :=
      ⟨hzx, hzx'⟩
    simpa [htriv] using hzinf
  exact Subtype.ext (by simpa using hzbot)

/-- Slimness of maximal solvable quotients of free pro-`Σ` groups of rank not equal to one. -/
theorem corollary_1_6_slim_free
    {sigma : Set ℕ} (hsigma : ∃ p, p ∈ sigma ∧ Nat.Prime p)
    {ι : Type v} (X : ι → F)
    (hFree : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate (SigmaGroup[sigma])) ι F X)
    (hrank : ¬ Nonempty (Unique ι))
    (m : ℕ) (hm : 2 ≤ m) :
    IsSlim (MaxSolvQuot F m) := by
  classical
  let hFprof : ProCGroups.IsProfiniteGroup F :=
    (ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate
      (SigmaGroup[sigma]) hFree.isProC)
  letI : CompactSpace F := hFprof.compactSpace
  letI : T2Space F := hFprof.t2Space
  letI : TotallyDisconnectedSpace F := hFprof.totallyDisconnectedSpace
  by_cases hEmpty : IsEmpty ι
  · have hRangeEmpty : Set.range X = (∅ : Set F) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact (hEmpty.false i).elim
      · simp only [Set.mem_empty_iff_false, Set.mem_range, IsEmpty.exists_iff, imp_self]
    have hclosureEmpty : Subgroup.closure (∅ : Set F) = (⊥ : Subgroup F) := by
      ext y
      simp only [Subgroup.closure_empty, Subgroup.mem_bot]
    have hbotClosed : IsClosed (((⊥ : Subgroup F) : Set F)) := by
      exact isClosed_singleton
    have hbotClosure : (⊥ : Subgroup F).topologicalClosure = ⊥ := by
      apply le_antisymm
      · exact Subgroup.topologicalClosure_minimal _ le_rfl hbotClosed
      · exact Subgroup.le_topologicalClosure (s := (⊥ : Subgroup F))
    have hgen :
        ((⊥ : Subgroup F).topologicalClosure : Subgroup F) = ⊤ := by
      have htopGen := hFree.generates_range
      unfold ProCGroups.Generation.TopologicallyGenerates at htopGen
      simpa [hRangeEmpty, hclosureEmpty] using htopGen
    have htopbot : (⊤ : Subgroup F) = ⊥ := by
      rw [hbotClosure] at hgen
      exact hgen.symm
    have hFtriv : ∀ g : F, g = 1 := by
      intro g
      have hgTop : g ∈ (⊤ : Subgroup F) := by simp only [Subgroup.mem_top]
      have hgBot : g ∈ (⊥ : Subgroup F) := by simpa [htopbot] using hgTop
      simpa using hgBot
    have hQtriv : ∀ q : MaxSolvQuot F m, q = 1 := by
      intro q
      rcases continuousToMaxSolvQuot_surjective (G := F) m q with ⟨g, rfl⟩
      simp only [hFtriv g, map_one]
    intro H
    ext q
    constructor
    · intro hq
      have hq1 : (q : MaxSolvQuot F m) = 1 := hQtriv q
      simp only [hq1, one_mem]
    · intro hq
      have hq1 : (q : MaxSolvQuot F m) = 1 := hQtriv q
      simp only [hq1, one_mem]
  have hNotSubsingleton : ¬ Subsingleton ι := by
    intro hSub
    rcases not_isEmpty_iff.mp hEmpty with ⟨i0⟩
    exact hrank ⟨
      { default := i0
        uniq := fun i => @Subsingleton.elim _ hSub i i0 }⟩
  letI : Nontrivial ι := not_subsingleton_iff_nontrivial.mp hNotSubsingleton
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  let x : MaxSolvQuot F m := continuousToMaxSolvQuot F m (X i)
  let x' : MaxSolvQuot F m := continuousToMaxSolvQuot F m (X j)
  have hcentx :
      ∀ n : ℕ, 0 < n → centralizerOf (x ^ n) =
        (closedSubgroupGenerated ({x} : Set (MaxSolvQuot F m)) :
          Subgroup (MaxSolvQuot F m)) := by
    intro n hn
    have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    simpa [x, zpow_natCast] using
      (theorem_1_5_center_free_freegroup (F := F) hsigma X hFree i m hm (n : ℤ) hnz)
  have hcentx' :
      ∀ n : ℕ, 0 < n → centralizerOf (x' ^ n) =
        (closedSubgroupGenerated ({x'} : Set (MaxSolvQuot F m)) :
          Subgroup (MaxSolvQuot F m)) := by
    intro n hn
    have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    simpa [x', zpow_natCast] using
      (theorem_1_5_center_free_freegroup (F := F) hsigma X hFree j m hm (n : ℤ) hnz)
  have htriv :
      (closedSubgroupGenerated ({x} : Set (MaxSolvQuot F m)) :
          Subgroup (MaxSolvQuot F m)) ⊓
        (closedSubgroupGenerated ({x'} : Set (MaxSolvQuot F m)) :
          Subgroup (MaxSolvQuot F m)) = ⊥ := by
    simpa [x, x'] using
      closedSubgroupGenerated_singleton_inf_bot_of_distinct_free_generators
        (C := SigmaGroup[sigma]) (F := F) X hFree hij m
  exact isSlim_of_two_elements_with_centralizer_formula x x' hcentx hcentx' htriv

/-! ## Subsection 2.1: Ab-torsion-freeness and ab-faithfulness -/

-- Local notation used only in this file to keep statements readable.

/-- The preimage of an open subgroup above the last derived term has the same
maximal abelian quotient. -/
theorem remark_2_2_preimage_open_subgroup_maxSolvQuot_one_equiv
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    {m : ℕ} (hm : 2 ≤ m)
    (P : OpenSubgroup (Qm G m))
    (hP : lastDerivedSubgroup (G := G) m ≤ (P : Subgroup (Qm G m))) :
    Nonempty
      (MaxSolvQuot
          ↥((preimageOpenSubgroup (continuousToMaxSolvQuot G m) P : OpenSubgroup G) :
            Subgroup G) 1 ≃*
        MaxSolvQuot ↥(P : Subgroup (Qm G m)) 1) := by
  let Q : Type u := Qm G m
  let π : G →ₜ* Q := continuousToMaxSolvQuot G m
  have hπsurj : Function.Surjective π := by
    simpa [π, Q] using continuousToMaxSolvQuot_surjective (G := G) m
  have hpre :
      topDerivedTop G (m - 1) ≤ ((P : Subgroup Q).comap (π : G →* Q)) := by
    intro x hx
    exact hP ((topDerivedTop_le_comap (f := π) (m := m - 1)) hx)
  have hm1 : 1 ≤ m := le_trans (by decide) hm
  have hker :
      (π : G →* Q).ker ≤
        (topDerivedTop
          ↥((preimageOpenSubgroup π P : OpenSubgroup G) : Subgroup G) 1).map
            (Subgroup.subtype
              ((preimageOpenSubgroup π P : OpenSubgroup G) : Subgroup G)) := by
    simpa [π, Q] using
      continuousToMaxSolvQuot_ker_le_topDerived_one_map_subtype_of_le
        (G := G) (m := m) hm1 P hpre
  have hclosed :
      IsClosedMap (π.restrictPreimage (P : Subgroup Q)) := by
    exact
      TopologicalGroup.restrictPreimage_isClosedMap_of_isClosedMap
        (π := π) (Q₁ := (P : Subgroup Q))
        ((continuousToMaxSolvQuot G m).continuous_toFun.isClosedMap)
        (Subgroup.isClosed_of_isOpen (P : Subgroup Q) P.isOpen')
  simpa [π, Q] using
    preimageOpenSubgroup_maxSolvQuot_mulEquiv_of_ker_le
      (G := G) (Q := Q) π hπsurj P hclosed 1 hker

/-- Open subgroups above the last derived term have torsion-free abelianization. -/
theorem remark_2_2_i_above_last_derived_ab_torsion_free
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    (hG : IsAbTorsionFree G)
    {m : ℕ} (hm : 2 ≤ m)
    (H : OpenSubgroup (Qm G m))
    (hH : aboveLastDerived (G := G) m H) :
    IsMulTorsionFree
      (AbTop ↥(H : Subgroup (Qm G m))) :=
  isMulTorsionFree_topologicalAbelianization_of_aboveLastDerived_of_isAbTorsionFree
    (G := G) hG hm H hH

/-- Open normal subgroups above the last derived term inherit faithful
conjugation action. -/
theorem remark_2_2_ii_contains_last_derived_ab_faithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbFaithful G)
    {m : ℕ} (hm : 2 ≤ m)
    (H : OpenSubgroup (Qm G m))
    (N : OpenNormalSubgroup ↥(H : Subgroup (Qm G m)))
    (hContain : containsLastDerived (G := G) m H N) :
    Function.Injective
      (quotientConjugationTopologicalAbelianizationMap
        (G := ↥(H : Subgroup (Qm G m)))
        (N := (N : Subgroup ↥(H : Subgroup (Qm G m))))) :=
  injective_quotientConjAbelianization_of_containsLastDerived_of_abFaithful
    (G := G) hG hm H N hContain

/-- Ab-torsion-freeness passes to closed subgroups. -/
theorem lemma_2_3_1_isAbTorsionFree_closedSubgroup
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbTorsionFree G)
    {K : Subgroup G} (hKClosed : IsClosed (K : Set G)) :
    IsAbTorsionFree ↥K :=
  isAbTorsionFree_closedSubgroup (G := G) hG hKClosed

/-- An ab-torsion-free profinite group is torsion-free. -/
theorem lemma_2_3_2_isTorsionFreeGroup_of_isAbTorsionFree
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbTorsionFree G) :
    IsTorsionFreeGroup G :=
  isTorsionFreeGroup_of_isAbTorsionFree (G := G) hG

/-- Maximal finite-step solvable quotients are torsion-free. -/
theorem lemma_2_3_3_isTorsionFreeGroup_maxSolvQuot
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbTorsionFree G)
    {m : ℕ} (hm : 1 ≤ m) :
    IsTorsionFreeGroup (Qm G m) :=
  isTorsionFreeGroup_maxSolvQuot_of_isAbTorsionFree (G := G) hG hm

/-- Closed normal subgroups inside the first derived subgroup have no nontrivial
fixed points on abelianization. -/
theorem lemma_2_3_4_noFixedPoints_of_isAbTorsionFree
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {K : Subgroup G} (hKClosed : IsClosed (K : Set G))
    (hKNormal : K.Normal) (hK : K ≤ topDerivedTop G 1)
    (hG : IsAbTorsionFree G) :
    let _ : K.Normal := hKNormal
    HasNoNontrivialFixedPoints
      (quotientConjugationTopologicalAbelianizationMap (G := G) (N := K)) :=
  noFixedPoints_of_isAbTorsionFree (G := G) hKClosed hKNormal hK hG

/-- An ab-faithful profinite group is center-free. -/
theorem lemma_2_4_1_center_eq_bot_of_isAbFaithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbFaithful G) :
    Subgroup.center G = ⊥ :=
  center_eq_bot_of_isAbFaithful (G := G) hG

/-- In maximal solvable quotients, the center is contained in the last derived
subgroup. -/
theorem lemma_2_4_2_center_le_lastDerivedSubgroup
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbFaithful G)
    {m : ℕ} (hm : 1 ≤ m) :
    Subgroup.center (Qm G m) ≤ lastDerivedSubgroup (G := G) m :=
  center_le_lastDerivedSubgroup_of_isAbFaithful (G := G) hG hm

/-- Maximal solvable quotients are torsion-free and center-free under ab-torsion-freeness and
ab-faithfulness. -/
theorem proposition_2_5_basic_prop_for_centerfree_m
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hTorsion : IsAbTorsionFree G) (hFaithful : IsAbFaithful G)
    {m : ℕ} (hm : 2 ≤ m) :
    IsTorsionFreeGroup (Qm G m) ∧
      Subgroup.center (Qm G m) = ⊥ := by
  exact
    ⟨isTorsionFreeGroup_maxSolvQuot_of_isAbTorsionFree
        (G := G) hTorsion (le_trans (by decide) hm),
      center_eq_bot_maxSolvQuot_of_isAbTorsionFree_of_isAbFaithful
        (G := G) hTorsion hFaithful hm⟩

/-- The centralizer of an open subgroup lies in the last derived subgroup under ab-torsion-freeness
and ab-faithfulness. -/
theorem proposition_2_6_centralizer_openSubgroup_le_lastDerived
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hTorsion : IsAbTorsionFree G) (hFaithful : IsAbFaithful G)
    {m : ℕ} (hm : 1 ≤ m)
    (H : OpenSubgroup (Qm G m)) :
    Subgroup.centralizer (H : Set (Qm G m))
      ≤ lastDerivedSubgroup (G := G) m :=
  centralizer_openSubgroup_le_lastDerived_of_abTorsionFree_faithful
    (G := G) hTorsion hFaithful hm H

end CenterFreenessFiniteStepSolvable
