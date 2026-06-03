import FenchelNielsenZomorrodian.Discrete.Core.CompactFuchsianPresentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Profinite/CompactFuchsianSignature.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# FenchelNielsenZomorrodian / Profinite / CompactFuchsianSignature

Focused module in the public source tree. It contains declarations used by the library roots and by downstream proof modules.
-/

namespace FenchelNielsen

universe u

namespace ProfiniteFGroup

/-- Promote a compact Fenchel signature with at least three periods to the compact Fuchsian
signature used by the discrete compact three-step theorem. -/
def compactFuchsianSignature
    (σ : FenchelSignature) (hCompact : σ.IsCompact)
    (hPeriods : 3 ≤ σ.numPeriods) : FuchsianSignature where
  orbitGenus := σ.orbitGenus
  numCusps := σ.numCusps
  numPeriods := σ.numPeriods
  periods := σ.periods
  period_ge_two := σ.period_ge_two
  numCusps_eq_zero := hCompact
  numPeriods_ge_three := hPeriods

end ProfiniteFGroup

end FenchelNielsen
