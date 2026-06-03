import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.AbelianizationKernel.Periods
import Mathlib.Data.Fintype.Sigma

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/AbelianizationKernel/Conditions.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Abelianization-kernel conditions for compact Fuchsian groups

Numerical and period-family criteria ensuring that abelianization kernels satisfy the conditions needed for torsion-free finite-index subgroups.
-/

namespace FenchelNielsen

def AbelianizationKernelConditionFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (periods : ι → ℕ) : Prop :=
  ∀ i, periods i ∣ otherPeriodsLcmFamily periods i ∨
    2 * otherPeriodsLcmFamily periods i ≤ otherPeriodsProductFamily periods i

def AbelianizationKernelCondition (σ : FenchelSignature) : Prop :=
  AbelianizationKernelConditionFamily σ.periods

def FenchelSignature.OneStepNumericalCondition (σ : FenchelSignature) : Prop :=
  σ.HasCusps ∨ σ.IsCompact ∧ σ.AbelianPeriodCondition

def FenchelSignature.DeltaOneAbelianPeriodCondition (σ : FenchelSignature) : Prop :=
  LCMConditionFamily
    (nonOneSubfamilyPeriods (abelianizationKernelRawPeriods σ.periods))

def FenchelSignature.TwoStepNumericalCondition (σ : FenchelSignature) : Prop :=
  (σ.orbitGenus, σ.numCusps) ≠ (0, 0) ∨
    (σ.orbitGenus, σ.numCusps) = (0, 0) ∧
      σ.DeltaOneAbelianPeriodCondition

end FenchelNielsen
