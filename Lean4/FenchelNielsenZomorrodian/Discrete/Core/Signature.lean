import FenchelNielsenZomorrodian.Discrete.Arithmetic.FamilyLcm
import Mathlib.Tactic.Linarith

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Core/Signature.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete Fenchel and compact Fuchsian core definitions

Signatures, generator indices, presentations, elliptic generators, quotient homomorphisms, and family-signature transformations.
-/

open scoped BigOperators

namespace FenchelNielsen

structure FenchelSignature where
  orbitGenus : ℕ
  numCusps : ℕ
  numPeriods : ℕ
  periods : Fin numPeriods → ℕ
  period_ge_two : ∀ i, 2 ≤ periods i

def FenchelSignature.eulerCharacteristic (σ : FenchelSignature) : ℚ :=
  (2 : ℚ) - 2 * σ.orbitGenus - σ.numCusps -
    ∑ i : Fin σ.numPeriods, (1 - ((σ.periods i : ℚ)⁻¹))

def FenchelSignature.hyperbolicDefect (σ : FenchelSignature) : ℚ :=
  -(σ.eulerCharacteristic)

def FenchelSignature.IsHyperbolic (σ : FenchelSignature) : Prop :=
  σ.eulerCharacteristic < 0

theorem FenchelSignature.isHyperbolic_iff_pos_hyperbolicDefect
    {σ : FenchelSignature} :
    σ.IsHyperbolic ↔ 0 < σ.hyperbolicDefect := by
  dsimp [FenchelSignature.IsHyperbolic, FenchelSignature.hyperbolicDefect]
  constructor <;> intro h <;> linarith

def FenchelSignature.HasCusps (σ : FenchelSignature) : Prop :=
  0 < σ.numCusps

def FenchelSignature.IsCompact (σ : FenchelSignature) : Prop :=
  σ.numCusps = 0


def otherPeriodsLcm (σ : FenchelSignature) (i : Fin σ.numPeriods) : ℕ :=
  otherPeriodsLcmFamily σ.periods i

def otherPeriodsProduct (σ : FenchelSignature) (i : Fin σ.numPeriods) : ℕ :=
  otherPeriodsProductFamily σ.periods i

def LCMCondition (σ : FenchelSignature) : Prop :=
  LCMConditionFamily σ.periods

def FenchelSignature.AbelianPeriodCondition (σ : FenchelSignature) : Prop :=
  LCMCondition σ

theorem exists_lcm_obstruction_of_not_lcmCondition
    (σ : FenchelSignature) (hNotLCM : ¬ LCMCondition σ) :
    ∃ i : Fin σ.numPeriods, ¬ σ.periods i ∣ otherPeriodsLcm σ i := by
  classical
  simpa [LCMCondition, LCMConditionFamily, otherPeriodsLcm] using
    not_forall.mp hNotLCM

end FenchelNielsen
