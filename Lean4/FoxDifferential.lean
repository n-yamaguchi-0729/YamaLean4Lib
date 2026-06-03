import FoxDifferential.Common.CrossedDifferential
import FoxDifferential.Common.CrossedDifferentialModule
import FoxDifferential.Common.FiniteFamilyLinearMap
import FoxDifferential.Common.FoxBoundary
import FoxDifferential.Common.FreeCrossedDifferential
import FoxDifferential.Common.Jacobian
import FoxDifferential.Discrete.Absolute
import FoxDifferential.Discrete.DifferentialModule.Boundary
import FoxDifferential.Discrete.FoxCalculus.Boundary
import FoxDifferential.Discrete.FoxCalculus.Coordinates
import FoxDifferential.Discrete.FoxCalculus.Derivative
import FoxDifferential.Discrete.FoxCalculus.Semidirect
import FoxDifferential.Discrete.FoxCalculus.Universal
import FoxDifferential.Discrete.FreeExpansion
import FoxDifferential.Discrete.Jacobian.Automorphism
import FoxDifferential.Discrete.Naturality
import FoxDifferential.Discrete.KernelBoundary.IdentityAugmentation
import FoxDifferential.Discrete.KernelBoundary.Basic
import FoxDifferential.Discrete.KernelBoundary.Homology
import FoxDifferential.Discrete.KernelBoundary.Quotient
import FoxDifferential.Discrete.KernelBoundary.MagnusKernel
import FoxDifferential.Completed.DifferentialModule.Identity
import FoxDifferential.Completed.DifferentialModule.Map.Comap
import FoxDifferential.Completed.DifferentialModule.Map.GroupLike
import FoxDifferential.Completed.DifferentialModule.Map.Limit
import FoxDifferential.Completed.DifferentialModule.Map.Stage
import FoxDifferential.Completed.DifferentialModule.Map.Surjective
import FoxDifferential.Completed.DifferentialModule.TargetQuotient.Basic
import FoxDifferential.Completed.DifferentialModule.TargetQuotient.Fundamental
import FoxDifferential.Completed.DifferentialModule.TargetQuotient.Surjective
import FoxDifferential.Completed.Continuous.Automorphism
import FoxDifferential.Completed.Continuous.Free.DiscreteGenerators
import FoxDifferential.Completed.Continuous.Free.Rules
import FoxDifferential.Completed.Continuous.Topology
import FoxDifferential.Completed.Continuous.ChainRule.Basic
import FoxDifferential.Completed.Continuous.ChainRule.Iterated
import FoxDifferential.Completed.Continuous.Naturality
import FoxDifferential.Completed.Continuous.TailExactness
import FoxDifferential.Completed.Continuous.TopologicalGeneration
import FoxDifferential.Completed.Continuous.Universal.Basic
import FoxDifferential.Completed.Continuous.Universal.FiniteStage
import FoxDifferential.Completed.Continuous.Universal.NaturalTopology
import FoxDifferential.Completed.Continuous.Universal.System
import FoxDifferential.Completed.Continuous.SemidirectKernelBasis
import FoxDifferential.Completed.FreeProC.SemidirectLift
import FoxDifferential.Completed.FreeProC.Uniqueness.Derivative
import FoxDifferential.Completed.FreeProC.Uniqueness.Existence
import FoxDifferential.Completed.FreeProC.Uniqueness.Lift
import FoxDifferential.Completed.FreeProC.Uniqueness.Morphism
import FoxDifferential.Completed.FreeProC.Uniqueness.SemidirectHom
import FoxDifferential.Completed.FreeProC.Density
import FoxDifferential.Completed.FreeProC.QuotientKernelBasis
import FoxDifferential.Completed.FreeProC.CofinalQuotientKernelBasis
import FoxDifferential.Completed.FreeProC.FiniteQuotientStages
import FoxDifferential.Completed.FreeProC.SemidirectKernelBasis
import FoxDifferential.RightDerivative.GeometricSeries
import FoxDifferential.RightDerivative.Basic
import FoxDifferential.RightDerivative.Semidirect
import FoxDifferential.RightDerivative.IntegerPower
import FoxDifferential.RightDerivative.CommutatorFormula

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Fox differential calculus

Public entry point for the Fox-differential calculus library.  The library contains crossed
differentials, Fox derivatives on free groups and group rings, Fox boundaries, Jacobians,
completed/profinite Fox differentials, and right Fox-derivative formulas.

It may import `ProCGroups`, `ReidemeisterSchreier`, and `CompletedGroupAlgebra`.  The downstream
modules `CrowellExactSequence` and `MetabelianProductCentralizer` are intentionally not imported.
-/
