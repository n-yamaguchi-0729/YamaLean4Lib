import FoxDifferential.Completed.FreeProC.StageApproximation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/QuotientKernelBasis.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Quotient-kernel neighbourhood bases

The completed density theorem uses quotient maps out of the completed Fox semidirect product.
This file adds the standard topological-group conversion from identity-neighbourhood kernel
bases to the left-coset kernel basis used by closure arguments.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology

universe u v

section QuotientKernelIdentityBasis

variable {Y : Type u} [Group Y] [TopologicalSpace Y]
variable {J : Type v} {Q : J → Type*} [∀ j, Group (Q j)]
variable (π : ∀ j : J, Y →* Q j)

/-- Quotient kernels form a neighbourhood basis at the identity.

For every open neighbourhood of `1`, some finite-stage kernel is contained in it.  In a
topological group this is the natural form obtained from finite quotient separation; it implies
the left-coset basis used by `subset_closure_of_quotientKernel_approximation`. -/
def HasIdentityQuotientKernelNeighbourhoodBasis : Prop :=
  ∀ U : Set Y, IsOpen U → (1 : Y) ∈ U →
    ∃ j : J, ∀ z : Y, z ∈ (π j).ker → z ∈ U

/-- Identity-neighbourhood quotient kernels give the left quotient-kernel basis. -/
theorem HasIdentityQuotientKernelNeighbourhoodBasis.to_left
    [IsTopologicalGroup Y]
    (hbasis : HasIdentityQuotientKernelNeighbourhoodBasis (Y := Y) π) :
    HasLeftQuotientKernelNeighbourhoodBasis (Y := Y) π := by
  intro y U hU hyU
  let W : Set Y := {z : Y | y * z ∈ U}
  have hWopen : IsOpen W := by
    have hmul : Continuous fun z : Y => y * z :=
      (continuous_const : Continuous fun _ : Y => y).mul continuous_id
    exact hU.preimage hmul
  have hWone : (1 : Y) ∈ W := by
    simp only [Set.mem_setOf_eq, mul_one, hyU, W]
  rcases hbasis W hWopen hWone with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  intro z hz
  exact hj z hz

/-- Closure criterion using identity-neighbourhood quotient kernels directly. -/
theorem subset_closure_of_identityQuotientKernel_approximation
    [IsTopologicalGroup Y]
    {S T : Set Y}
    (hbasis : HasIdentityQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (happrox :
      ∀ y : Y, y ∈ T → ∀ j : J,
        ∃ s : Y, s ∈ S ∧ π j s = π j y) :
    T ⊆ closure S :=
  subset_closure_of_quotientKernel_approximation
    (Y := Y) (S := S) (T := T) π
    (HasIdentityQuotientKernelNeighbourhoodBasis.to_left (Y := Y) (π := π) hbasis)
    happrox

/-- Stage-exact closure criterion with identity-neighbourhood quotient kernels. -/
theorem subset_closure_of_identityQuotientKernel_stage_exact
    [IsTopologicalGroup Y]
    {S T : Set Y}
    (hbasis : HasIdentityQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (Sstage Tstage : ∀ j : J, Set (Q j))
    (hTstage : ∀ y : Y, y ∈ T → ∀ j : J, π j y ∈ Tstage j)
    (hstage_exact : ∀ j : J, Tstage j ⊆ Sstage j)
    (hlift_stage : ∀ j : J, ∀ q : Q j, q ∈ Sstage j →
      ∃ s : Y, s ∈ S ∧ π j s = q) :
    T ⊆ closure S :=
  subset_closure_of_quotientKernel_stage_exact
    (Y := Y) (S := S) (T := T) π
    (HasIdentityQuotientKernelNeighbourhoodBasis.to_left (Y := Y) (π := π) hbasis)
    Sstage Tstage hTstage hstage_exact hlift_stage

end QuotientKernelIdentityBasis

end

end FoxDifferential
