import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Lift

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Derivative/Relators.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage completed Fox calculus

Finite quotient stages are used to compare completed Fox boundaries, derivatives, and relation modules with explicit finite group-algebra calculations.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- If a word lies in `N`, the finite-stage lift has trivial right component. -/
theorem finiteFoxStageLift_right_eq_one_of_mem
    {a : FreeGroup X} (ha : a ∈ N) :
    (finiteFoxStageLift (X := X) N n a).right = 1 := by
  rw [finiteFoxStageLift_right]
  apply QuotientGroup.eq.2
  simpa using ha

/-- Kernel membership for the finite-stage semidirect lift is exactly the conjunction of lying in
`N` and having zero finite Fox derivative vector. -/
theorem mem_ker_finiteFoxStageLift_iff
    {w : FreeGroup X} :
    w ∈ (finiteFoxStageLift (X := X) N n).ker ↔
      w ∈ N ∧ finiteFoxStageDerivativeVector (X := X) N n w = 0 := by
  constructor
  · intro hw
    have hlift : finiteFoxStageLift (X := X) N n w = 1 := by
      simpa [MonoidHom.mem_ker] using hw
    constructor
    · have hright := congrArg FiniteFoxStageSemidirect.right hlift
      rw [finiteFoxStageLift_right] at hright
      exact (QuotientGroup.eq_one_iff (N := N) w).1 hright
    · have hleft := congrArg FiniteFoxStageSemidirect.left hlift
      simpa [finiteFoxStageDerivativeVector] using hleft
  · rintro ⟨hwN, hder⟩
    rw [MonoidHom.mem_ker]
    apply FiniteFoxStageSemidirect.ext
    · simpa [finiteFoxStageDerivativeVector] using hder
    · rw [finiteFoxStageLift_right]
      exact (QuotientGroup.eq_one_iff (N := N) w).2 hwN

/-- The finite-stage Magnus reverse inclusion is equivalent to the derivative-zero criterion
inside `N`. -/
theorem ker_finiteFoxStageLift_le_finiteFoxCommutatorPowerSubgroup_iff :
    (finiteFoxStageLift (X := X) N n).ker ≤
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n ↔
      ∀ w : FreeGroup X,
        w ∈ N →
        finiteFoxStageDerivativeVector (X := X) N n w = 0 →
          w ∈ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n := by
  constructor
  · intro hle w hwN hder
    exact hle ((mem_ker_finiteFoxStageLift_iff (X := X) N n).2 ⟨hwN, hder⟩)
  · intro h w hw
    rcases (mem_ker_finiteFoxStageLift_iff (X := X) N n).1 hw with ⟨hwN, hder⟩
    exact h w hwN hder

omit [DecidableEq X] in
/-- In the finite-stage semidirect product, commutators of elements with trivial right component
are trivial. -/
theorem finiteFoxStageSemidirect_commutator_eq_one_of_right_one
    (a b : FiniteFoxStageSemidirect (X := X) N n)
    (ha : a.right = 1) (hb : b.right = 1) :
    ⁅a, b⁆ = 1 := by
  rw [commutatorElement_def]
  apply FiniteFoxStageSemidirect.ext
  · funext i
    have hone :
        (MonoidAlgebra.single
          (1 : finiteFoxStageTargetQuotient (X := X) N)
          (1 : ModNCompletedCoeff n) :
            finiteFoxStageTargetGroupAlgebra (X := X) N n) = 1 := by
      simp only [MonoidAlgebra.one_def]
    simp only [FiniteFoxStageSemidirect.mul_left, ha, MonoidAlgebra.of_apply, hone, one_smul,
  FiniteFoxStageSemidirect.mul_right, hb, mul_one, FiniteFoxStageSemidirect.inv_left, inv_one, smul_neg, add_assoc,
  add_neg_cancel_comm_assoc, FiniteFoxStageSemidirect.inv_right, Pi.add_apply, Pi.neg_apply, add_neg_cancel,
  FiniteFoxStageSemidirect.one_left, Pi.zero_apply]
  · simp only [FiniteFoxStageSemidirect.mul_right, ha, hb, mul_one, FiniteFoxStageSemidirect.inv_right, inv_one,
  FiniteFoxStageSemidirect.one_right]

/-- The finite-stage lift kills commutators of words in `N`. -/
theorem finiteFoxStageLift_commutator_eq_one_of_mem
    {a b : FreeGroup X} (ha : a ∈ N) (hb : b ∈ N) :
    finiteFoxStageLift (X := X) N n ⁅a, b⁆ = 1 := by
  rw [map_commutatorElement]
  exact finiteFoxStageSemidirect_commutator_eq_one_of_right_one
    (X := X) N n
    (finiteFoxStageLift (X := X) N n a)
    (finiteFoxStageLift (X := X) N n b)
    (finiteFoxStageLift_right_eq_one_of_mem (X := X) N n ha)
    (finiteFoxStageLift_right_eq_one_of_mem (X := X) N n hb)

omit [DecidableEq X] in
/-- Powers of a finite-stage semidirect element with trivial right component still have trivial
right component. -/
theorem finiteFoxStageSemidirect_pow_right_eq_one_of_right_one
    (a : FiniteFoxStageSemidirect (X := X) N n)
    (ha : a.right = 1) (m : ℕ) :
    (a ^ m).right = 1 := by
  induction m with
  | zero =>
      simp only [pow_zero, FiniteFoxStageSemidirect.one_right]
  | succ m ih =>
      rw [pow_succ]
      simp only [FiniteFoxStageSemidirect.mul_right, ih, ha, mul_one]

omit [DecidableEq X] in
/-- Powers of a finite-stage semidirect element with trivial right component scale the left
component by the exponent. -/
theorem finiteFoxStageSemidirect_pow_left_of_right_one
    (a : FiniteFoxStageSemidirect (X := X) N n)
    (ha : a.right = 1) (m : ℕ) :
    (a ^ m).left = m • a.left := by
  induction m with
  | zero =>
      simp only [pow_zero, FiniteFoxStageSemidirect.one_left, zero_nsmul]
  | succ m ih =>
      rw [pow_succ]
      have hright :
          (a ^ m).right = 1 :=
        finiteFoxStageSemidirect_pow_right_eq_one_of_right_one
          (X := X) N n a ha m
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (finiteFoxStageTargetQuotient (X := X) N) 1 :
              finiteFoxStageTargetGroupAlgebra (X := X) N n) = 1 := by
        simp only [MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk, OneHom.coe_mk, MonoidAlgebra.one_def]
      ext i q
      simp only [FiniteFoxStageSemidirect.mul_left, ih, nsmul_eq_mul, hright, hone, one_smul, Pi.add_apply,
  Pi.mul_apply, Pi.natCast_apply, MonoidAlgebra.coe_add, Pi.smul_apply, Nat.cast_succ, add_mul, one_mul]

omit [DecidableEq X] in
/-- The `n`th power of a finite-stage semidirect element with trivial right component is trivial
over `Z/nZ`. -/
theorem finiteFoxStageSemidirect_pow_char_eq_one_of_right_one
    (a : FiniteFoxStageSemidirect (X := X) N n)
    (ha : a.right = 1) :
    a ^ n = 1 := by
  apply FiniteFoxStageSemidirect.ext
  · rw [finiteFoxStageSemidirect_pow_left_of_right_one (X := X) N n a ha n]
    exact ZModModule.char_nsmul_eq_zero (n := n) a.left
  · exact finiteFoxStageSemidirect_pow_right_eq_one_of_right_one
      (X := X) N n a ha n

/-- The finite-stage lift kills `n`th powers of words in `N`. -/
theorem finiteFoxStageLift_pow_eq_one_of_mem
    {a : FreeGroup X} (ha : a ∈ N) :
    finiteFoxStageLift (X := X) N n (a ^ n) = 1 := by
  rw [map_pow]
  exact finiteFoxStageSemidirect_pow_char_eq_one_of_right_one
    (X := X) N n (finiteFoxStageLift (X := X) N n a)
    (finiteFoxStageLift_right_eq_one_of_mem (X := X) N n ha)

/-- The finite Fox commutator-power relators lie in the kernel of the finite-stage lift. -/
theorem finiteFoxCommutatorPowerRelatorSet_subset_ker_finiteFoxStageLift :
    finiteFoxCommutatorPowerRelatorSet (F := FreeGroup X) N n ⊆
      (finiteFoxStageLift (X := X) N n).ker := by
  intro g hg
  change finiteFoxStageLift (X := X) N n g = 1
  rcases hg with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
  · exact finiteFoxStageLift_commutator_eq_one_of_mem (X := X) N n ha hb
  · exact finiteFoxStageLift_pow_eq_one_of_mem (X := X) N n ha

/-- The finite Fox commutator-power subgroup lies in the kernel of the finite-stage lift. -/
theorem finiteFoxCommutatorPowerSubgroup_le_ker_finiteFoxStageLift :
    finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n ≤
      (finiteFoxStageLift (X := X) N n).ker := by
  exact Subgroup.normalClosure_le_normal
    (finiteFoxCommutatorPowerRelatorSet_subset_ker_finiteFoxStageLift
      (X := X) N n)


end

end FoxDifferential
