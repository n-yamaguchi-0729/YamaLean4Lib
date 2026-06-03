import FenchelNielsenZomorrodian.Discrete.Core.EllipticCompact
import Mathlib.GroupTheory.OrderOfElement

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Torsion/FuchsianFiniteSubgroupFrontier.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete finite-subgroup torsion frontier

Isolates the remaining discrete Fuchsian finite-subgroup theorem: every finite subgroup of a compact
Fuchsian presentation is conjugate into an elliptic stabilizer.
-/

namespace FenchelNielsen

/-!
The approved torsion-classification frontier.

Mathematically, this is the discrete form of the finite-subgroup theorem for
Fuchsian orbifold groups: every nontrivial finite subgroup lies in a conjugate
of an elliptic stabilizer.  It replaces the older, more downstream smooth-kernel
torsion-free axiom.
-/

/-- A subgroup is contained in a conjugate of one elliptic stabilizer, up to powers. -/
def subgroup_le_conj_ellipticStabilizer
    (σ : FuchsianSignature) (K : Subgroup (FuchsianPresentedGroup σ)) : Prop :=
  ∃ i : Fin σ.numPeriods, ∃ c : FuchsianPresentedGroup σ,
    ∀ k : K, ∃ n : ℤ,
      (k : FuchsianPresentedGroup σ) =
        c * ellipticElement σ i ^ n * c⁻¹

/- FRONTIER `fuchsian-finite-subgroup-elliptic-stabilizer`.

This is the sole approved discrete axiom frontier in `FenchelNielsen`.  It is the compact
no-cusp presentation currently consumed by the compact Fuchsian three-step route. -/
/-- Finite nontrivial Fuchsian subgroups lie in conjugates of elliptic stabilizers. -/
axiom finiteSubgroup_le_conj_ellipticStabilizer
    (σ : FuchsianSignature)
    (K : Subgroup (FuchsianPresentedGroup σ)) [Finite K]
    (hK : K ≠ ⊥) :
    subgroup_le_conj_ellipticStabilizer σ K

/-- A nontrivial finite-order element is conjugate to a power of an elliptic generator. -/
theorem finiteOrder_isConj_elliptic_zpow_of_frontier
    {G ι : Type*} [Group G] (elliptic : ι → G)
    (frontier : ∀ K : Subgroup G, Finite K → K ≠ ⊥ →
      ∃ i : ι, ∃ c : G, ∀ k : K, ∃ n : ℤ,
        (k : G) = c * elliptic i ^ n * c⁻¹)
    (g : G) (hg : IsOfFinOrder g) (hgne : g ≠ 1) :
    ∃ i : ι, ∃ n : ℤ, IsConj g (elliptic i ^ n) := by
  classical
  let K : Subgroup G := Subgroup.zpowers g
  letI : Fintype K := Fintype.ofEquiv (Fin (orderOf g)) (finEquivZPowers hg)
  let hKfinite : Finite K := Finite.of_fintype K
  have hKne : K ≠ ⊥ := by
    intro hK
    have hgmem : g ∈ K := Subgroup.mem_zpowers g
    have hgbot : g ∈ (⊥ : Subgroup G) := by
      simpa [K, hK] using hgmem
    exact hgne (Subgroup.mem_bot.mp hgbot)
  rcases frontier K hKfinite hKne with ⟨i, c, hcontain⟩
  rcases hcontain ⟨g, Subgroup.mem_zpowers g⟩ with ⟨n, hn⟩
  exact ⟨i, n, (isConj_iff.2 ⟨c, hn.symm⟩).symm⟩

/-- A finite-order element is either trivial or conjugate to a power of an elliptic generator. -/
theorem finiteOrder_eq_one_or_isConj_elliptic_zpow_of_frontier
    {G ι : Type*} [Group G] (elliptic : ι → G)
    (frontier : ∀ K : Subgroup G, Finite K → K ≠ ⊥ →
      ∃ i : ι, ∃ c : G, ∀ k : K, ∃ n : ℤ,
        (k : G) = c * elliptic i ^ n * c⁻¹)
    (g : G) (hg : IsOfFinOrder g) :
    g = 1 ∨ ∃ i : ι, ∃ n : ℤ, IsConj g (elliptic i ^ n) := by
  by_cases hgne : g = 1
  · exact Or.inl hgne
  · exact Or.inr
      (finiteOrder_isConj_elliptic_zpow_of_frontier elliptic frontier g hg hgne)

end FenchelNielsen
