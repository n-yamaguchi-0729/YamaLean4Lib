import FenchelNielsenZomorrodian.Discrete.Abelianization.PeriodCoordinate

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Abelianization/PeriodQuotient.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Abelianization of compact Fuchsian presentations

Finite cyclic coordinate calculations for elliptic generators, period classes, period quotients, and order formulas in compact Fuchsian abelianizations.
-/

namespace FenchelNielsen

noncomputable def periodCoordinate_finite
    (σ : FuchsianSignature) :
    Finite (PeriodCoordinate σ) := by
  exact zmodCoordinateFamily_finite σ.periods
    (fun i => lt_of_lt_of_le (by decide : 0 < 2) (σ.period_ge_two i))

noncomputable def periodAbelianization_finite
    (σ : FuchsianSignature) :
    Finite (PeriodAbelianization σ) := by
  haveI : Finite (PeriodCoordinate σ) := periodCoordinate_finite σ
  exact Finite.of_surjective
    (fun v : PeriodCoordinate σ => (v : PeriodAbelianization σ))
    QuotientAddGroup.mk_surjective

end FenchelNielsen
