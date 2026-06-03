import FenchelNielsenZomorrodian.Discrete.Core.FamilySignature

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/AbelianizationKernel/Periods.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Abelianization-kernel conditions for compact Fuchsian groups

Numerical and period-family criteria ensuring that abelianization kernels satisfy the conditions needed for torsion-free finite-index subgroups.
-/

namespace FenchelNielsen

def abelianizationKernelPeriodFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (periods : ι → ℕ) (i : ι) : ℕ :=
  periods i / Nat.gcd (periods i) (otherPeriodsLcmFamily periods i)

def abelianizationKernelMultiplicityFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (periods : ι → ℕ) (i : ι) : ℕ :=
  otherPeriodsProductFamily periods i / otherPeriodsLcmFamily periods i

def abelianizationKernelRawPeriods {ι : Type*} [Fintype ι] [DecidableEq ι]
    (periods : ι → ℕ)
    (x : Sigma fun i : ι => Fin (abelianizationKernelMultiplicityFamily periods i)) : ℕ :=
  abelianizationKernelPeriodFamily periods x.1

def abelianizationKernelPeriods (σ : FuchsianSignature) :
    NonOneSubfamilyIndex (abelianizationKernelRawPeriods σ.periods) → ℕ :=
  nonOneSubfamilyPeriods (abelianizationKernelRawPeriods σ.periods)

end FenchelNielsen
