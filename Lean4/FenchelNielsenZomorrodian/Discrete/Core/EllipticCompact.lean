import FenchelNielsenZomorrodian.Discrete.Core.CompactFuchsianPresentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Core/EllipticCompact.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete Fenchel and compact Fuchsian core definitions

Signatures, generator indices, presentations, elliptic generators, quotient homomorphisms, and family-signature transformations.
-/

namespace FenchelNielsen

def ellipticElement (σ : FuchsianSignature) (i : Fin σ.numPeriods) :
    FuchsianPresentedGroup σ :=
  PresentedGroup.of (rels := relators σ) (FuchsianGenerator.elliptic i)

@[simp] theorem ellipticElement_pow_period_eq_one
    (σ : FuchsianSignature) (i : Fin σ.numPeriods) :
    ellipticElement σ i ^ σ.periods i = 1 := by
  simpa [ellipticElement, xWord] using
    (PresentedGroup.one_of_mem (rels := relators σ)
      (x := (xWord σ i) ^ σ.periods i) (Or.inl ⟨i, rfl⟩))

theorem ellipticElement_pow_eq_one_of_period_dvd
    (σ : FuchsianSignature) (i : Fin σ.numPeriods) {n : ℕ}
    (hdiv : σ.periods i ∣ n) :
    ellipticElement σ i ^ n = 1 := by
  rcases hdiv with ⟨k, rfl⟩
  rw [pow_mul, ellipticElement_pow_period_eq_one, one_pow]

theorem ellipticElement_zpow_eq_one_of_period_int_dvd
    (σ : FuchsianSignature) (i : Fin σ.numPeriods) {n : ℤ}
    (hdiv : (σ.periods i : ℤ) ∣ n) :
    ellipticElement σ i ^ n = 1 := by
  rcases hdiv with ⟨k, rfl⟩
  rw [zpow_mul, zpow_natCast, ellipticElement_pow_period_eq_one, one_zpow]

end FenchelNielsen
