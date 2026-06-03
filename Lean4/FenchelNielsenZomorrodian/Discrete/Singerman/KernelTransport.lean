import FenchelNielsenZomorrodian.Discrete.Core.Signature

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Singerman/KernelTransport.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Singerman/Reidemeister-Schreier bridge

Cyclic quotient actions, cyclic product identities, Schreier kernel computations, free-group word identities, and kernel transport for the compact Fuchsian proof.
-/

namespace FenchelNielsen
def singermanTransportPeriodsFamily
    {ι : Type*} {ρ : ι → ℕ}
    (n : ∀ i : ι, Fin (ρ i) → ℕ) :
    (Σ i : ι, Fin (ρ i)) → ℕ
  | ⟨i, k⟩ => n i k
end FenchelNielsen
