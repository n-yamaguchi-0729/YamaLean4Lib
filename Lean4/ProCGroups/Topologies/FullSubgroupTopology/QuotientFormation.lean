import Mathlib.Topology.Algebra.Group.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Topologies/FullSubgroupTopology/QuotientFormation.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Topological group constructions

Topological subgroup, quotient, continuous homomorphism, continuous equivalence, conjugation, and full-subgroup-topology lemmas.
-/

open Set
open scoped Topology

namespace ProCGroups.Topologies

universe u

/--
A quotient-level encoding of the distinguished open-normal family attached to a pro-`C` topology.

The intended reading of `C.contains N` is “the quotient `G/N` belongs to the chosen formation”.
The structure records just the closure properties needed for the basic algebra of the pro-`C`
topology, without committing to a concrete implementation of quotient classes.
-/
structure QuotientFormation where
  contains : ∀ {G : Type u} [Group G], Subgroup G → Prop
  top_mem : ∀ {G : Type u} [Group G], contains (G := G) (⊤ : Subgroup G)
  normal_of_mem : ∀ {G : Type u} [Group G] {N : Subgroup G}, contains (G := G) N → N.Normal
  upward_closed :
    ∀ {G : Type u} [Group G] {N K : Subgroup G},
      contains (G := G) N → N ≤ K → K.Normal → contains (G := G) K
  inf_closed :
    ∀ {G : Type u} [Group G] {N K : Subgroup G},
      contains (G := G) N → contains (G := G) K → contains (G := G) (N ⊓ K)

namespace QuotientFormation

variable (C : QuotientFormation)

/-- A subgroup is open in the pro-`C` topology iff it contains one of the basic kernels. -/
def IsOpenSubgroup {G : Type u} [Group G] (H : Subgroup G) : Prop :=
  ∃ N : Subgroup G, C.contains N ∧ N ≤ H

/-- Algebraic closure operator attached to the pro-`C` topology. -/
def proCClosure {G : Type u} [Group G] (H : Subgroup G) : Subgroup G :=
  sInf {K : Subgroup G | C.IsOpenSubgroup K ∧ H ≤ K}

/-- Closedness for the pro-`C` topology, formulated algebraically. -/
def IsClosedSubgroup {G : Type u} [Group G] (H : Subgroup G) : Prop :=
  C.proCClosure H = H

/-- Residuality for the pro-`C` topology: the identity is separated by the basic open kernels. -/
def IsResiduallyC {G : Type u} [Group G] : Prop :=
  C.proCClosure (⊥ : Subgroup G) = ⊥

variable {C}
variable {G : Type u} [Group G]

/-- The whole group is open for a quotient formation. -/
@[simp] theorem isOpenSubgroup_top (C : QuotientFormation) :
    C.IsOpenSubgroup (⊤ : Subgroup G) := by
  exact ⟨⊤, C.top_mem, le_rfl⟩

/-- A subgroup above an open subgroup for a quotient formation is open on the left. -/
theorem isOpenSubgroup_sup_left (C : QuotientFormation) {H K : Subgroup G}
    (hH : C.IsOpenSubgroup H) :
    C.IsOpenSubgroup (H ⊔ K) := by
  rcases hH with ⟨N, hN, hNH⟩
  exact ⟨N, hN, le_trans hNH le_sup_left⟩

/-- A subgroup above an open subgroup for a quotient formation is open on the right. -/
theorem isOpenSubgroup_sup_right (C : QuotientFormation) {H K : Subgroup G}
    (hK : C.IsOpenSubgroup K) :
    C.IsOpenSubgroup (H ⊔ K) := by
  simpa [sup_comm] using
    (C.isOpenSubgroup_sup_left (H := K) (K := H) hK)

/-- A subgroup is contained in its pro-`C` closure. -/
theorem le_proCClosure (C : QuotientFormation) (H : Subgroup G) :
    H ≤ C.proCClosure H := by
  change H ≤ sInf {K : Subgroup G | C.IsOpenSubgroup K ∧ H ≤ K}
  exact le_sInf fun K hK => hK.2

/-- The pro-`C` closure operation is monotone. -/
theorem proCClosure_mono (C : QuotientFormation) {H K : Subgroup G}
    (hHK : H ≤ K) :
    C.proCClosure H ≤ C.proCClosure K := by
  change
    sInf {L : Subgroup G | C.IsOpenSubgroup L ∧ H ≤ L} ≤
      sInf {L : Subgroup G | C.IsOpenSubgroup L ∧ K ≤ L}
  refine le_sInf ?_
  intro L hL
  exact sInf_le ⟨hL.1, hHK.trans hL.2⟩

/-- The pro-`C` closure operation is idempotent. -/
theorem proCClosure_idem (C : QuotientFormation) (H : Subgroup G) :
    C.proCClosure (C.proCClosure H) = C.proCClosure H := by
  refine le_antisymm ?_ (C.proCClosure_mono (C.le_proCClosure H))
  change
    sInf {L : Subgroup G | C.IsOpenSubgroup L ∧ C.proCClosure H ≤ L} ≤
      sInf {L : Subgroup G | C.IsOpenSubgroup L ∧ H ≤ L}
  refine le_sInf ?_
  intro L hL
  exact sInf_le ⟨hL.1, sInf_le hL⟩

/-- Closed subgroups for the quotient formation are exactly those containing the pro-`C` closure of every smaller subgroup. -/
theorem isClosedSubgroup_iff_proCClosure_le {C : QuotientFormation} {H : Subgroup G} :
    C.IsClosedSubgroup H ↔ C.proCClosure H ≤ H := by
  constructor
  · intro hH
    rw [QuotientFormation.IsClosedSubgroup] at hH
    rw [hH]
  · intro hH
    exact le_antisymm hH (C.le_proCClosure H)

/-- Residual `C`-ness is equivalent to the pro-`C` closure of the bottom subgroup being bottom. -/
@[simp] theorem isResiduallyC_iff_proCClosure_bot_eq_bot {C : QuotientFormation} :
    C.IsResiduallyC (G := G) ↔ C.proCClosure (⊥ : Subgroup G) = ⊥ :=
  Iff.rfl

/-- An element outside the pro-`C` closure is separated by an open subgroup in the quotient formation. -/
theorem exists_openSubgroup_not_mem_of_not_mem_proCClosure
    (C : QuotientFormation) {H : Subgroup G} {x : G}
    (hx : x ∉ C.proCClosure H) :
    ∃ K : Subgroup G, C.IsOpenSubgroup K ∧ H ≤ K ∧ x ∉ K := by
  rw [QuotientFormation.proCClosure, Subgroup.mem_sInf] at hx
  push_neg at hx
  rcases hx with ⟨K, hK, hxK⟩
  exact ⟨K, hK.1, hK.2, hxK⟩

/-- In a residually `C` group, a nontrivial element is excluded by some open subgroup in the quotient formation. -/
theorem exists_openSubgroup_not_mem_of_isResiduallyC
    (C : QuotientFormation) (hC : C.IsResiduallyC (G := G))
    {x : G} (hx : x ≠ 1) :
    ∃ K : Subgroup G, C.IsOpenSubgroup K ∧ x ∉ K := by
  have hxbot : x ∉ C.proCClosure (⊥ : Subgroup G) := by
    rw [hC]
    simpa using hx
  rcases C.exists_openSubgroup_not_mem_of_not_mem_proCClosure
      (H := (⊥ : Subgroup G)) hxbot with ⟨K, hKopen, _hbotK, hxK⟩
  exact ⟨K, hKopen, hxK⟩

/-- The normal core of an open subgroup again defines a quotient in the formation. -/
theorem normalCore_mem_of_open (C : QuotientFormation) {H : Subgroup G}
    (hH : C.IsOpenSubgroup H) :
    C.contains H.normalCore := by
  rcases hH with ⟨N, hN, hNH⟩
  let _ : N.Normal := C.normal_of_mem hN
  have hNcore : N ≤ H.normalCore := (Subgroup.normal_le_normalCore).2 hNH
  exact C.upward_closed hN hNcore inferInstance

/-- In a residually `C` group, a nontrivial element is excluded by an open normal kernel in the quotient formation. -/
theorem exists_openKernel_not_mem_of_isResiduallyC
    (C : QuotientFormation) (hC : C.IsResiduallyC (G := G))
    {x : G} (hx : x ≠ 1) :
    ∃ N : Subgroup G, C.contains N ∧ N.Normal ∧ x ∉ N := by
  rcases C.exists_openSubgroup_not_mem_of_isResiduallyC (G := G) hC hx with
    ⟨K, hKopen, hxK⟩
  refine ⟨K.normalCore, C.normalCore_mem_of_open hKopen, ?_, ?_⟩
  · exact C.normal_of_mem (C.normalCore_mem_of_open hKopen)
  · intro hxcore
    exact hxK (Subgroup.normalCore_le K hxcore)

/-- Closed subgroups are exactly intersections of open subgroups. -/
theorem isClosedSubgroup_iff_exists_sInf_openSubgroups
    {C : QuotientFormation} {H : Subgroup G} :
    C.IsClosedSubgroup H ↔
      ∃ S : Set (Subgroup G), (∀ K ∈ S, C.IsOpenSubgroup K) ∧ H = sInf S := by
  constructor
  · intro hH
    refine ⟨{K : Subgroup G | C.IsOpenSubgroup K ∧ H ≤ K}, ?_, ?_⟩
    · intro K hK
      exact hK.1
    · simpa [QuotientFormation.IsClosedSubgroup, QuotientFormation.proCClosure] using hH.symm
  · rintro ⟨S, hSopen, hEq⟩
    rw [QuotientFormation.IsClosedSubgroup]
    refine le_antisymm ?_ (C.le_proCClosure H)
    calc
      C.proCClosure H ≤ sInf S := by
        refine le_sInf ?_
        intro K hK
        have hHK : H ≤ K := by
          rw [hEq]
          exact sInf_le hK
        exact sInf_le ⟨hSopen K hK, hHK⟩
      _ = H := hEq.symm

end QuotientFormation

end ProCGroups.Topologies
