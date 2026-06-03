import FoxDifferential.Discrete.FreeExpansion

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Discrete/Naturality.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete group-ring Fox calculus

Ordinary Fox derivatives over group rings are developed through augmentation, relative differential modules, coordinates, Jacobians, and chain rules.
-/
namespace FoxDifferential

noncomputable section

namespace FoxCalculus

universe u v w

variable {H : Type v} {K : Type w} [Group H] [Group K]
variable {X : Type u} [DecidableEq X]
variable (ψ : FreeGroup X →* H) (φ : H →* K)

/-- Push forward a relative Fox-coordinate vector along a homomorphism of coefficient groups. -/
def relativeFreeFoxCoordinatesMap :
    RelativeFreeFoxCoordinates (H := H) X → RelativeFreeFoxCoordinates (H := K) X :=
  fun a x => groupRingMap φ (a x)

omit [DecidableEq X] in
/-- Evaluation formula for pushing forward a relative Fox-coordinate vector. -/
@[simp]
theorem relativeFreeFoxCoordinatesMap_apply
    (a : RelativeFreeFoxCoordinates (H := H) X) (x : X) :
    relativeFreeFoxCoordinatesMap (X := X) φ a x = groupRingMap φ (a x) :=
  rfl

/-- Relative Fox derivatives are natural under coefficient push-forward. -/
theorem relativeFreeGroupFoxDerivative_mapDomain (w : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := K) X (φ.comp ψ) w =
      relativeFreeFoxCoordinatesMap (X := X) φ
        (relativeFreeGroupFoxDerivative (H := H) X ψ w) := by
  let delta : FreeGroup X → RelativeFreeFoxCoordinates (H := K) X :=
    fun w => relativeFreeFoxCoordinatesMap (X := X) φ
      (relativeFreeGroupFoxDerivative (H := H) X ψ w)
  have hdelta :
      IsDifferentialMap
        (A := RelativeFreeFoxCoordinates (H := K) X) (φ.comp ψ) delta := by
    intro u v
    funext x
    simp only [relativeFreeFoxCoordinatesMap_apply, relativeFreeGroupFoxDerivative_mul, MonoidAlgebra.of_apply,
  Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, groupRingMap_single, groupRingScalar,
  MonoidHom.coe_comp, Function.comp_apply, relativeFreeFoxCoordinatesMap, delta]
  have hbasis :
      ∀ x : X, delta (FreeGroup.of x) = Pi.single x (1 : GroupRing K) := by
    intro x
    funext y
    by_cases hxy : x = y
    · subst y
      simp only [relativeFreeFoxCoordinatesMap_apply, relativeFreeGroupFoxDerivative_of, Pi.single_eq_same, map_one,
  delta]
    · simp only [relativeFreeFoxCoordinatesMap_apply, relativeFreeGroupFoxDerivative_of, ne_eq, hxy,
  not_false_eq_true, Pi.single_eq_of_ne', map_zero, delta]
  exact (congrFun
    (relativeFreeGroupFoxDerivative_unique (H := K) X (φ.comp ψ) delta hdelta hbasis) w).symm

/-- Component form of coefficient-push-forward naturality. -/
theorem relativeFreeGroupFoxDerivative_mapDomain_apply (w : FreeGroup X) (x : X) :
    relativeFreeGroupFoxDerivative (H := K) X (φ.comp ψ) w x =
      groupRingMap φ (relativeFreeGroupFoxDerivative (H := H) X ψ w x) := by
  have h := congrFun
    (relativeFreeGroupFoxDerivative_mapDomain (H := H) (K := K) ψ φ w) x
  simpa [relativeFreeFoxCoordinatesMap] using h

end FoxCalculus

end

end FoxDifferential
