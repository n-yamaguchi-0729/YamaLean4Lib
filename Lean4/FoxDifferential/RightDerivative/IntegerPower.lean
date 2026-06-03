import FoxDifferential.RightDerivative.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/RightDerivative/IntegerPower.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Right Fox derivatives

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

def signedGeomSeries {G : Type*} [Group G] (g : G) : ℤ → FoxDifferential.GroupRing G
  | Int.ofNat n => geomSeries g n
  | Int.negSucc n => -(MonoidAlgebra.of ℤ G g⁻¹ * geomSeries g⁻¹ (n + 1))

namespace RightDerivation

variable {G : Type*} [Group G]

theorem map_zpow_groupElement (D : RightDerivation G) (g : G) :
    ∀ n : ℤ,
      D (MonoidAlgebra.of ℤ G (g ^ n) : FoxDifferential.GroupRing G) =
        D (MonoidAlgebra.of ℤ G g : FoxDifferential.GroupRing G) * signedGeomSeries g n
  | Int.ofNat n => by
      simpa [signedGeomSeries] using D.map_pow_groupElement g n
  | Int.negSucc n => by
      have hpow := D.map_pow_groupElement g⁻¹ (n + 1)
      rw [map_inv_groupElement] at hpow
      simpa [signedGeomSeries, mul_assoc] using hpow

end RightDerivation

end

end FoxDifferential
