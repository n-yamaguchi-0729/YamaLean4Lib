import FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Target

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/Completion/Source/Index.lean
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

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


/-- The open normal subgroup associated to the finite Fox commutator-power quotient. -/
def finiteFoxCommutatorPowerOpenNormalSubgroup
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) (n : ℕ) :
    OpenNormalSubgroup (FreeGroup X) where
  toOpenSubgroup :=
    { toSubgroup := finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n
      isOpen' := isOpen_discrete _ }
  isNormal' := by
    change (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n).Normal
    infer_instance

omit [DecidableEq X] in
/-- The underlying subgroup of `finiteFoxCommutatorPowerOpenNormalSubgroup` is the corresponding
commutator-power subgroup. -/
@[simp]
theorem finiteFoxCommutatorPowerOpenNormalSubgroup_subgroup
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) (n : ℕ) :
    ((finiteFoxCommutatorPowerOpenNormalSubgroup (X := X) N n :
        OpenNormalSubgroup (FreeGroup X)) : Subgroup (FreeGroup X)) =
      finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n := rfl

/-- The completed group-algebra index corresponding to the finite Fox commutator-power source
quotient at the prime-power stage `a`. -/
def finiteFoxStagePrimePowerSourceCompletedIndex
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (a : ℕ) : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex (FreeGroup X) :=
  OrderDual.toDual
    (⟨finiteFoxCommutatorPowerOpenNormalSubgroup (X := X) N (ℓ ^ a),
      hfinite a⟩ :
      OpenNormalSubgroupInClass ProCGroups.FiniteGroupClass.allFinite (FreeGroup X))

omit [DecidableEq X] in
/-- The source completed index has the expected underlying commutator-power subgroup. -/
@[simp]
theorem finiteFoxStagePrimePowerSourceCompletedIndex_subgroup
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (a : ℕ) :
    (((OrderDual.ofDual
        (finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
          N hfinite a)).1 : OpenNormalSubgroup (FreeGroup X)) :
        Subgroup (FreeGroup X)) =
      finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a) := rfl

omit [DecidableEq X] in
/-- Monotonicity of the source completed indices along prime-power stages. -/
theorem finiteFoxStagePrimePowerSourceCompletedIndex_mono
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    {a b : ℕ} (hab : a ≤ b) :
    finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a ≤
      finiteFoxStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite b := by
  change finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ b) ≤
    finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)
  exact finiteFoxCommutatorPowerSubgroup_dvd (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab)



end

end FoxDifferential
