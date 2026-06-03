import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Relators
import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Rules

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Derivative/Quotient/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage completed Fox calculus

Finite quotient stages are used to compare completed Fox boundaries, derivatives, and relation modules with explicit finite group-algebra calculations.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The finite-stage lift descended to the source quotient `F/[N,N]N^n`. -/
def finiteFoxStageQuotientLift :
    FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n →*
      FiniteFoxStageSemidirect (X := X) N n :=
  QuotientGroup.lift
    (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (finiteFoxStageLift (X := X) N n)
    (finiteFoxCommutatorPowerSubgroup_le_ker_finiteFoxStageLift
      (X := X) N n)

/-- Evaluation of the descended finite-stage lift on a representative. -/
@[simp]
theorem finiteFoxStageQuotientLift_mk (w : FreeGroup X) :
    finiteFoxStageQuotientLift (X := X) N n
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) =
      finiteFoxStageLift (X := X) N n w := by
  rfl

/-- The right component of the descended finite-stage lift is the quotient map from
`F/[N,N]N^n` to `F/N`. -/
@[simp]
theorem finiteFoxStageQuotientLift_right
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    (finiteFoxStageQuotientLift (X := X) N n q).right =
      finiteFoxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n q := by
  rcases QuotientGroup.mk'_surjective
      (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
  rw [finiteFoxStageQuotientLift_mk, finiteFoxStageLift_right,
    finiteFoxCommutatorPowerQuotientMapToNormalQuotient_mk]

/-- The finite-stage derivative vector descended to the source quotient `F/[N,N]N^n`. -/
def finiteFoxStageQuotientDerivativeVector
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageCoordinateVector (X := X) N n :=
  (finiteFoxStageQuotientLift (X := X) N n q).left

/-- Evaluation of the descended derivative vector on a representative. -/
@[simp]
theorem finiteFoxStageQuotientDerivativeVector_mk (w : FreeGroup X) :
    finiteFoxStageQuotientDerivativeVector (X := X) N n
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) =
      finiteFoxStageDerivativeVector (X := X) N n w := by
  rfl

/-- A coordinate of the descended finite-stage derivative on the source quotient. -/
def finiteFoxStageQuotientDerivative (i : X)
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageTargetGroupAlgebra (X := X) N n :=
  finiteFoxStageQuotientDerivativeVector (X := X) N n q i

/-- Evaluation of a descended derivative coordinate on a representative. -/
@[simp]
theorem finiteFoxStageQuotientDerivative_mk (i : X) (w : FreeGroup X) :
    finiteFoxStageQuotientDerivative (X := X) N n i
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) =
      finiteFoxStageDerivative (X := X) N n i w := by
  rfl

/-- Coefficient homomorphism for the finite-stage quotient crossed differential. -/
def finiteFoxStageQuotientCoefficient :
    (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) →*
      finiteFoxStageTargetGroupAlgebra (X := X) N n :=
  (MonoidAlgebra.of (ModNCompletedCoeff n)
    (finiteFoxStageTargetQuotient (X := X) N)).comp
      (finiteFoxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n)

omit [DecidableEq X] in
/-- Evaluation formula for the finite-stage quotient coefficient homomorphism. -/
@[simp]
theorem finiteFoxStageQuotientCoefficient_apply
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageQuotientCoefficient (X := X) N n q =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) N)
        (finiteFoxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n q) :=
  rfl

omit [DecidableEq X] in
/-- The quotient coefficient homomorphism agrees with the free-group coefficient homomorphism on
representatives. -/
@[simp]
theorem finiteFoxStageQuotientCoefficient_mk (w : FreeGroup X) :
    finiteFoxStageQuotientCoefficient (X := X) N n
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) =
      finiteFoxStageCoefficient (X := X) N n w := by
  rfl

/-- The descended finite-stage derivative vector sends the identity quotient class to zero. -/
@[simp]
theorem finiteFoxStageQuotientDerivativeVector_one :
    finiteFoxStageQuotientDerivativeVector (X := X) N n
        (1 : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) = 0 := by
  change (finiteFoxStageQuotientLift (X := X) N n 1).left = 0
  rw [map_one]
  rfl

/-- Component form of the identity rule for the descended finite-stage derivative. -/
@[simp]
theorem finiteFoxStageQuotientDerivative_one (i : X) :
    finiteFoxStageQuotientDerivative (X := X) N n i
        (1 : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) = 0 := by
  simp only [finiteFoxStageQuotientDerivative, finiteFoxStageQuotientDerivativeVector_one, Pi.zero_apply]

/-- Generator value for the descended finite-stage derivative vector. -/
@[simp]
theorem finiteFoxStageQuotientDerivativeVector_of (x : X) :
    finiteFoxStageQuotientDerivativeVector (X := X) N n
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) (FreeGroup.of x)) =
      Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n) := by
  rw [finiteFoxStageQuotientDerivativeVector_mk, finiteFoxStageDerivativeVector_of]

/-- Component form of the generator value for the descended finite-stage derivative. -/
@[simp]
theorem finiteFoxStageQuotientDerivative_of (i x : X) :
    finiteFoxStageQuotientDerivative (X := X) N n i
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) (FreeGroup.of x)) =
      (Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n) :
        X → finiteFoxStageTargetGroupAlgebra (X := X) N n) i := by
  rw [finiteFoxStageQuotientDerivative, finiteFoxStageQuotientDerivativeVector_of]

/-- Product rule for the descended finite-stage derivative vector on the finite source quotient. -/
theorem finiteFoxStageQuotientDerivativeVector_mul
    (q r : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageQuotientDerivativeVector (X := X) N n (q * r) =
      finiteFoxStageQuotientDerivativeVector (X := X) N n q +
        finiteFoxStageQuotientCoefficient (X := X) N n q •
          finiteFoxStageQuotientDerivativeVector (X := X) N n r := by
  change (finiteFoxStageQuotientLift (X := X) N n (q * r)).left =
    (finiteFoxStageQuotientLift (X := X) N n q).left +
      finiteFoxStageQuotientCoefficient (X := X) N n q •
        (finiteFoxStageQuotientLift (X := X) N n r).left
  rw [map_mul]
  simp only [FiniteFoxStageSemidirect.mul_left, finiteFoxStageQuotientLift_right, MonoidAlgebra.of_apply,
  finiteFoxStageQuotientCoefficient, MonoidHom.coe_comp, Function.comp_apply]

/-- Component form of the product rule for the descended finite-stage derivative. -/
theorem finiteFoxStageQuotientDerivative_mul
    (i : X) (q r : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageQuotientDerivative (X := X) N n i (q * r) =
      finiteFoxStageQuotientDerivative (X := X) N n i q +
        finiteFoxStageQuotientCoefficient (X := X) N n q *
          finiteFoxStageQuotientDerivative (X := X) N n i r := by
  have h := congrFun (finiteFoxStageQuotientDerivativeVector_mul (X := X) N n q r) i
  simpa [finiteFoxStageQuotientDerivative, Pi.smul_apply] using h

/-- The descended finite-stage derivative vector is a crossed differential on the finite source
quotient. -/
theorem finiteFoxStageQuotientDerivativeVector_isCrossedDifferential :
    IsCrossedDifferential
      (finiteFoxStageQuotientCoefficient (X := X) N n)
      (finiteFoxStageQuotientDerivativeVector (X := X) N n) := by
  intro q r
  exact finiteFoxStageQuotientDerivativeVector_mul (X := X) N n q r

/-- Uniqueness of the descended finite-stage Fox derivative vector among crossed differentials
on the finite source quotient with the standard coordinate values on the quotient generators. -/
theorem finiteFoxStageQuotientDerivativeVector_unique
    (delta :
      (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) →
        finiteFoxStageCoordinateVector (X := X) N n)
    (hdelta :
      IsCrossedDifferential (finiteFoxStageQuotientCoefficient (X := X) N n) delta)
    (hbasis :
      ∀ x : X,
        delta
          (QuotientGroup.mk'
            (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (FreeGroup.of x)) =
          Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n)) :
    delta = finiteFoxStageQuotientDerivativeVector (X := X) N n := by
  let C : Subgroup (FreeGroup X) :=
    finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n
  have hcomp :
      IsCrossedDifferential
        (finiteFoxStageCoefficient (X := X) N n)
        (fun w : FreeGroup X => delta (QuotientGroup.mk' C w)) := by
    intro u v
    have h := hdelta (QuotientGroup.mk' C u) (QuotientGroup.mk' C v)
    simpa only [C, finiteFoxStageQuotientCoefficient_mk] using h
  have hbasis_comp :
      ∀ x : X,
        delta (QuotientGroup.mk' C (FreeGroup.of x)) =
          Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n) := by
    intro x
    simpa [C] using hbasis x
  have hfree :
      (fun w : FreeGroup X => delta (QuotientGroup.mk' C w)) =
        finiteFoxStageDerivativeVector (X := X) N n :=
    finiteFoxStageDerivativeVector_unique (X := X) N n
      (fun w : FreeGroup X => delta (QuotientGroup.mk' C w)) hcomp hbasis_comp
  funext q
  rcases QuotientGroup.mk'_surjective C q with ⟨w, rfl⟩
  simpa [C] using congrFun hfree w

/-- Existence and uniqueness theorem for the descended finite-stage Fox derivative vector on the
finite source quotient. -/
theorem existsUnique_finiteFoxStageQuotientDerivativeVector :
    ∃! delta :
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) →
          finiteFoxStageCoordinateVector (X := X) N n,
      IsCrossedDifferential (finiteFoxStageQuotientCoefficient (X := X) N n) delta ∧
        ∀ x : X,
          delta
            (QuotientGroup.mk'
              (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (FreeGroup.of x)) =
            Pi.single x (1 : finiteFoxStageTargetGroupAlgebra (X := X) N n) := by
  refine ⟨finiteFoxStageQuotientDerivativeVector (X := X) N n, ?_, ?_⟩
  · exact ⟨finiteFoxStageQuotientDerivativeVector_isCrossedDifferential (X := X) N n,
      finiteFoxStageQuotientDerivativeVector_of (X := X) N n⟩
  · intro delta hdelta
    exact finiteFoxStageQuotientDerivativeVector_unique (X := X) N n
      delta hdelta.1 hdelta.2



end

end FoxDifferential
