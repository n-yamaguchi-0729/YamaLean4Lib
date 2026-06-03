import FenchelNielsenZomorrodian.Discrete.Coordinates.ZModFamily
import FenchelNielsenZomorrodian.Discrete.Core.Signature

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Coordinates/FenchelPeriodCoordinate.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite coordinate systems for Fenchel periods

ZMod coordinate families and Fenchel period-coordinate sums used to define finite quotient maps on period generators.
-/

open scoped BigOperators

namespace FenchelNielsen

abbrev FenchelPeriodCoordinate (σ : FenchelSignature) :=
  ZModCoordinateFamily σ.periods

def fenchelPeriodBasisVector (σ : FenchelSignature) (i : Fin σ.numPeriods) :
    FenchelPeriodCoordinate σ :=
  zmodBasisVector σ.periods i

def fenchelPeriodBasisSum (σ : FenchelSignature) : FenchelPeriodCoordinate σ :=
  ∑ i : Fin σ.numPeriods, fenchelPeriodBasisVector σ i

end FenchelNielsen
