import FoxDifferential.Completed.FiniteStage.Basic
import FoxDifferential.Completed.FiniteStage.BoundaryCycles
import FoxDifferential.Completed.FiniteStage.BoundaryCycleHom
import FoxDifferential.Completed.FiniteStage.RelationModule
import FoxDifferential.Completed.FiniteStage.RelationAction
import FoxDifferential.Completed.FiniteStage.RelationSubmodule
import FoxDifferential.Completed.FiniteStage.BoundaryQuotient
import FoxDifferential.Completed.FiniteStage.SemidirectCycles
import FoxDifferential.Completed.FiniteStage.BoundarySubgroups
import FoxDifferential.Completed.FiniteStage.RelationRealization
import FoxDifferential.Completed.FiniteStage.RelationIdeal
import FoxDifferential.Completed.FiniteStage.SourceBoundary
import FoxDifferential.Completed.FiniteStage.RelationIdealDerivative
import FoxDifferential.Completed.FiniteStage.CoeffMap.Augmentation
import FoxDifferential.Completed.FiniteStage.CoeffMap.Semidirect
import FoxDifferential.Completed.FiniteStage.CoeffMap.Boundary
import FoxDifferential.Completed.FiniteStage.CoeffMap.BoundaryCycles
import FoxDifferential.Completed.FiniteStage.MagnusQuotient
import FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.Index
import FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.LimitMap
import FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.Representatives
import FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Target
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.CompletedSource
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.CompletedTarget
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Limit
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Vector
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.OnGroup.Vector
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.OnGroup.Projection
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Fundamental
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.GroupLike
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Mul
import FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.SpecialValues
import FoxDifferential.Completed.FiniteStage.PrimePower.System.Basic
import FoxDifferential.Completed.FiniteStage.PrimePower.System.Semidirect
import FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.AddCommGroup
import FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.CoeffMap
import FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.Mul
import FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.Semidirect
import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Boundary
import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Relators
import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Rules
import FoxDifferential.Completed.FiniteStage.Stage.Derivative.Quotient.Fundamental
import FoxDifferential.Completed.FiniteStage.Stage.Fundamental.Formula
import FoxDifferential.Completed.FiniteStage.Stage.KernelIdeal
import FoxDifferential.Completed.FiniteStage.Stage.Naturality
import FoxDifferential.Completed.FiniteStage.Stage.Semidirect
import FoxDifferential.Completed.FiniteStage.Stage.Source
import FoxDifferential.Completed.FiniteStage.TargetMap
import FoxDifferential.Completed.FiniteStage.Bifiltered.Transition
import FoxDifferential.Completed.FiniteStage.Bifiltered.System
import FoxDifferential.Completed.FiniteStage.Bifiltered.InverseSystem

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage completed Fox calculus

Finite quotient stages are used to compare completed Fox boundaries, derivatives, and relation modules with explicit finite group-algebra calculations.
-/
