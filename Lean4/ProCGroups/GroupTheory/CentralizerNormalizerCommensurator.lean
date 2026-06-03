import Mathlib.GroupTheory.Commensurable
import ProCGroups.Generation.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/GroupTheory/CentralizerNormalizerCommensurator.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Centralizers, normalizers, and commensurators

This file collects the subgroup centralizer, normalizer, and commensurator API used by
profinite-group applications.  The definitions are the mathlib definitions, exposed under the
`ProCGroups.GroupTheory` namespace so downstream files can use one focused PCG import.  It also
records closure and topological-closure facts that are repeatedly useful for profinite groups.
-/

open scoped Pointwise

namespace ProCGroups.GroupTheory

universe u

variable {G : Type u} [Group G]

/-- The centralizer of a set of elements. -/
abbrev centralizer (S : Set G) : Subgroup G :=
  Subgroup.centralizer S

/-- The centralizer of a single element. -/
abbrev centralizerOf (g : G) : Subgroup G :=
  centralizer ({g} : Set G)

/-- The normalizer of a subgroup. -/
abbrev normalizer (H : Subgroup G) : Subgroup G :=
  H.normalizer

/-- The commensurator of a subgroup. -/
abbrev commensurator (H : Subgroup G) : Subgroup G :=
  Subgroup.Commensurable.commensurator H

/-- Membership in the centralizer means commuting with every element of the set. -/
@[simp] theorem mem_centralizer_iff {S : Set G} {g : G} :
    g ∈ centralizer S ↔ ∀ h ∈ S, h * g = g * h :=
  Iff.rfl

/-- Membership in the centralizer, written as a vanishing commutator. -/
@[simp] theorem mem_centralizer_iff_commutator_eq_one {S : Set G} {g : G} :
    g ∈ centralizer S ↔ ∀ h ∈ S, h * g * h⁻¹ * g⁻¹ = 1 := by
  simpa [centralizer] using
    (Subgroup.mem_centralizer_iff_commutator_eq_one (g := g) (s := S))

/-- Membership in the centralizer of one element is commutation with that element. -/
@[simp] theorem mem_centralizerOf_iff {x g : G} :
    x ∈ centralizerOf g ↔ x * g = g * x := by
  simpa [centralizerOf, centralizer] using
    (Subgroup.mem_centralizer_singleton_iff (g := g) (k := x))

/-- Centralizing an element implies centralizing each of its natural powers. -/
theorem mem_centralizerOf_pow_of_mem {x y : G} (hy : y ∈ centralizerOf x) (n : ℕ) :
    y ∈ centralizerOf (x ^ n) := by
  rw [mem_centralizerOf_iff] at hy ⊢
  induction n with
  | zero =>
      simp only [pow_zero, mul_one, one_mul]
  | succ n ih =>
      calc
        y * x ^ (n + 1) = (y * x ^ n) * x := by rw [pow_succ, mul_assoc]
        _ = (x ^ n * y) * x := by rw [ih]
        _ = x ^ n * (y * x) := by rw [mul_assoc]
        _ = x ^ n * (x * y) := by rw [hy]
        _ = x ^ (n + 1) * y := by rw [pow_succ, mul_assoc]

/-- Centralizing an inverse is the same as centralizing the element. -/
theorem mem_centralizerOf_inv_iff {x y : G} :
    y ∈ centralizerOf x⁻¹ ↔ y ∈ centralizerOf x := by
  rw [mem_centralizerOf_iff, mem_centralizerOf_iff]
  constructor
  · intro h
    have h' := congrArg (fun z => x * z * x) h
    simpa [mul_assoc] using h'.symm
  · intro h
    have h' := congrArg (fun z => x⁻¹ * z * x⁻¹) h
    simpa [mul_assoc] using h'.symm

/-- Replacing a nonzero integer power by its positive absolute value does not change the
centralizer. -/
theorem centralizerOf_zpow_eq_natAbs (x : G) {n : ℤ} (_hn : n ≠ 0) :
    centralizerOf (x ^ n) = centralizerOf (x ^ (n.natAbs : ℤ)) := by
  cases n with
  | ofNat k =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast, Int.natAbs_natCast]
  | negSucc k =>
      ext y
      simp only [Int.natAbs, zpow_negSucc, zpow_natCast]
      exact mem_centralizerOf_inv_iff

/-- Membership form of `centralizerOf_zpow_eq_natAbs`. -/
theorem mem_centralizerOf_zpow_natAbs_of_mem_zpow {x y : G} {n : ℤ} (hn : n ≠ 0)
    (hy : y ∈ centralizerOf (x ^ n)) :
    y ∈ centralizerOf (x ^ (n.natAbs : ℤ)) := by
  rwa [← centralizerOf_zpow_eq_natAbs x hn]

/-- If an integer power is nontrivial, so is the corresponding positive absolute power. -/
theorem zpow_natAbs_ne_one_of_zpow_ne_one {x : G} {n : ℤ}
    (h : x ^ n ≠ 1) :
    x ^ (n.natAbs : ℤ) ≠ 1 := by
  cases n with
  | ofNat k =>
      simpa using h
  | negSucc k =>
      intro hpos
      have hposZ : x ^ (((k + 1 : ℕ) : ℤ)) = 1 := by
        simpa [Int.natAbs, Nat.cast_add, Nat.cast_one] using hpos
      have hpos' : x ^ (k + 1) = 1 := by
        rw [← zpow_natCast (a := x) (n := k + 1)]
        exact hposZ
      exact h (by simp [zpow_negSucc, hpos'])

/-- If `c` and `c * d` centralize `x`, then `d` centralizes `x`. -/
theorem right_factor_mem_centralizerOf_of_mul_mem_and_left_mem {x c d : G}
    (hc : c ∈ centralizerOf x) (hcd : c * d ∈ centralizerOf x) :
    d ∈ centralizerOf x := by
  rw [mem_centralizerOf_iff] at hc hcd ⊢
  calc
    d * x = c⁻¹ * (c * d * x) := by simp [mul_assoc]
    _ = c⁻¹ * (x * (c * d)) := by rw [hcd]
    _ = c⁻¹ * ((x * c) * d) := by simp [mul_assoc]
    _ = c⁻¹ * ((c * x) * d) := by rw [← hc]
    _ = x * d := by simp [mul_assoc]

/-- An element centralizes itself. -/
theorem centralizerOf_self_mem (g : G) :
    g ∈ centralizerOf g := by
  simp only [centralizerOf, mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]

/-- Centralizers are antitone in the set being centralized. -/
theorem centralizer_le {S T : Set G} (hST : S ⊆ T) :
    centralizer T ≤ centralizer S := by
  simpa [centralizer] using Subgroup.centralizer_le (G := G) hST

/-- Two subgroups centralize each other symmetrically. -/
theorem le_centralizer_iff {H K : Subgroup G} :
    H ≤ centralizer (K : Set G) ↔ K ≤ centralizer (H : Set G) := by
  simpa [centralizer] using (Subgroup.le_centralizer_iff (H := H) (K := K))

/-- A set has full centralizer exactly when it lies in the center. -/
theorem centralizer_eq_top_iff_subset {S : Set G} :
    centralizer S = ⊤ ↔ S ⊆ (Subgroup.center G : Set G) := by
  simp only [centralizer, Subgroup.centralizer_eq_top_iff_subset]

/-- The centralizer of a normal subgroup is normal. -/
instance centralizer_normal (H : Subgroup G) [H.Normal] :
    (centralizer (H : Set G)).Normal := by
  dsimp [centralizer]
  infer_instance

/-- The centralizer of a characteristic subgroup is characteristic. -/
instance centralizer_characteristic (H : Subgroup G) [H.Characteristic] :
    (centralizer (H : Set G)).Characteristic := by
  dsimp [centralizer]
  infer_instance

/-- In a Hausdorff topological group, the centralizer of one element is closed. -/
theorem centralizerOf_isClosed
    [TopologicalSpace G] [ContinuousMul G] [T2Space G] (g : G) :
    IsClosed ((centralizerOf g : Subgroup G) : Set G) := by
  simpa [centralizerOf, centralizer] using
    Set.isClosed_centralizer (M := G) ({g} : Set G)

/-- For fixed `g`, the set of elements commuting with `g` is closed. -/
theorem isClosed_setOf_commutingWith
    [TopologicalSpace G] [ContinuousMul G] [T2Space G] (g : G) :
    IsClosed {x : G | x * g = g * x} := by
  have hset :
      ((centralizerOf g : Subgroup G) : Set G) = {x : G | x * g = g * x} := by
    ext x
    exact mem_centralizerOf_iff
  rw [← hset]
  exact centralizerOf_isClosed (G := G) g

/-- Topological generation preserves containment in a closed centralizer. -/
theorem closedSubgroupGenerated_le_centralizer_of_subset
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {S T : Set G} (hS : S ⊆ (centralizer T : Set G)) :
    (ProCGroups.Generation.closedSubgroupGenerated (G := G) S : Subgroup G) ≤ centralizer T := by
  have hclosure : Subgroup.closure S ≤ centralizer T := by
    rw [Subgroup.closure_le]
    exact hS
  exact
    Subgroup.topologicalClosure_minimal
      _
      hclosure
      (by simpa [centralizer] using Set.isClosed_centralizer (M := G) T)

/-- A subgroup and its topological closure have the same centralizer. -/
theorem centralizer_eq_centralizer_topologicalClosure
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (S : Subgroup G) :
    centralizer ((S.topologicalClosure : Subgroup G) : Set G) = centralizer (S : Set G) := by
  apply le_antisymm
  · exact centralizer_le (Subgroup.le_topologicalClosure (s := S))
  · intro g hg
    rw [mem_centralizer_iff] at hg ⊢
    have hclosure : (S.topologicalClosure : Subgroup G) ≤ centralizerOf g := by
      exact
        Subgroup.topologicalClosure_minimal
          S
          (by
            intro x hx
            exact mem_centralizerOf_iff.mpr (hg x hx))
          (centralizerOf_isClosed (G := G) g)
    intro x hx
    exact mem_centralizerOf_iff.mp (hclosure hx)

/-- The closed subgroup topologically generated by `g` centralizes every integer power of `g`. -/
theorem closedSubgroupGenerated_singleton_le_centralizerOf_zpow
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (g : G) (n : ℤ) :
    (ProCGroups.Generation.closedSubgroupGenerated (G := G) ({g} : Set G) : Subgroup G) ≤
      centralizerOf (g ^ n) := by
  have hclosure :
      Subgroup.closure ({g} : Set G) ≤ centralizerOf (g ^ n) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact mem_centralizerOf_iff.mpr
      (by simpa using (Commute.zpow_zpow_self g (1 : ℤ) n).eq)
  exact
    Subgroup.topologicalClosure_minimal
      _
      hclosure
      (centralizerOf_isClosed (G := G) (g ^ n))

/-- Membership form of `closedSubgroupGenerated_singleton_le_centralizerOf_zpow`. -/
theorem mem_centralizerOf_zpow_of_mem_closedSubgroupGenerated
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {x c : G} (n : ℤ)
    (hc : c ∈ (ProCGroups.Generation.closedSubgroupGenerated (G := G) ({x} : Set G) :
      Subgroup G)) :
    c ∈ centralizerOf (x ^ n) :=
  (closedSubgroupGenerated_singleton_le_centralizerOf_zpow (G := G) x n) hc

/-- If a single element topologically generates the group, the centralizer of any of its powers is
the corresponding closed cyclic subgroup. -/
theorem centralizerOf_zpow_eq_closedSubgroupGenerated_of_topologicallyGenerates
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (x : G) (n : ℤ)
    (hgen : ProCGroups.Generation.TopologicallyGenerates (G := G) ({x} : Set G)) :
    centralizerOf (x ^ n) =
      (ProCGroups.Generation.closedSubgroupGenerated (G := G) ({x} : Set G) : Subgroup G) := by
  have hcyc :
      (ProCGroups.Generation.closedSubgroupGenerated (G := G) ({x} : Set G) : Subgroup G) =
        ⊤ := by
    unfold ProCGroups.Generation.TopologicallyGenerates at hgen
    simpa [ProCGroups.Generation.closedSubgroupGenerated] using hgen
  have hcent_top : centralizerOf (x ^ n) = ⊤ := by
    apply top_unique
    rw [← hcyc]
    exact closedSubgroupGenerated_singleton_le_centralizerOf_zpow (G := G) x n
  simpa [hcyc] using hcent_top

/-- Membership in the normalizer, stated by invariance under conjugation by the element. -/
@[simp] theorem mem_normalizer_iff {H : Subgroup G} {g : G} :
    g ∈ normalizer H ↔ ∀ h : G, h ∈ H ↔ g * h * g⁻¹ ∈ H := by
  simpa [normalizer] using (Subgroup.mem_normalizer_iff (H := H) (g := g))

/-- The centralizer of a subgroup is contained in its normalizer. -/
theorem centralizer_le_normalizer (H : Subgroup G) :
    centralizer (H : Set G) ≤ normalizer H := by
  intro g hg
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hcomm : h * g = g * h := (mem_centralizer_iff.mp hg) h hh
    simpa [← hcomm, mul_assoc] using hh
  · intro hh
    let k : G := g * h * g⁻¹
    have hk : k ∈ H := hh
    have hcomm : k * g = g * k := (mem_centralizer_iff.mp hg) k hk
    have h_eq_k : h = k := by
      calc
        h = g⁻¹ * (k * g) := by
          simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left, k]
        _ = g⁻¹ * (g * k) := by rw [hcomm]
        _ = k := by simp only [inv_mul_cancel_left]
    simpa [h_eq_k] using hk

/-- Membership in the commensurator, stated in terms of the conjugation action. -/
@[simp] theorem mem_commensurator_iff {H : Subgroup G} {g : G} :
    g ∈ commensurator H ↔
      Subgroup.Commensurable (ConjAct.toConjAct g • H) H := by
  rfl

/-- The normalizer of a subgroup is contained in its commensurator. -/
theorem normalizer_le_commensurator (H : Subgroup G) :
    normalizer H ≤ commensurator H := by
  intro g hg
  rw [mem_commensurator_iff]
  have hsmul : ConjAct.toConjAct g • H = H :=
    Subgroup.conjAct_pointwise_smul_eq_self (H := H) (g := g) (by
      simpa [normalizer] using hg)
  simpa [hsmul] using (Subgroup.Commensurable.refl H)

/-- An element of the normalizer is an element of the commensurator. -/
theorem mem_commensurator_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer H) :
    g ∈ commensurator H :=
  normalizer_le_commensurator H hg

/-- The centralizer of a subgroup is contained in its commensurator. -/
theorem centralizer_le_commensurator (H : Subgroup G) :
    centralizer (H : Set G) ≤ commensurator H :=
  (centralizer_le_normalizer H).trans (normalizer_le_commensurator H)

/-- Commensurable subgroups have the same commensurator. -/
theorem commensurator_eq_of_commensurable {H K : Subgroup G}
    (hHK : Subgroup.Commensurable H K) :
    commensurator H = commensurator K := by
  simpa [commensurator] using Subgroup.Commensurable.eq hHK

/-- Membership in the commensurator is invariant under replacing by a commensurable subgroup. -/
theorem mem_commensurator_iff_of_commensurable {H K : Subgroup G}
    (hHK : Subgroup.Commensurable H K) {g : G} :
    g ∈ commensurator H ↔ g ∈ commensurator K := by
  rw [commensurator_eq_of_commensurable hHK]

/-- Transport commensurator membership across commensurable subgroups. -/
theorem mem_commensurator_of_commensurable {H K : Subgroup G}
    (hHK : Subgroup.Commensurable H K) {g : G}
    (hg : g ∈ commensurator H) :
    g ∈ commensurator K :=
  (mem_commensurator_iff_of_commensurable hHK).mp hg

end ProCGroups.GroupTheory
