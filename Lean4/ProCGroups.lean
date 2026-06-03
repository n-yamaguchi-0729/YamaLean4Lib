import ProCGroups.Abelian.TopologicalAbelianization
import ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import ProCGroups.Abelian.TopologicalAbelianizationLimits
import ProCGroups.Categorical.AlgebraicPullbacks
import ProCGroups.Categorical.ProfinitePullbacks
import ProCGroups.Categorical.PullbackComparison
import ProCGroups.Categorical.PushoutSquares
import ProCGroups.Categorical.QuotientPullbackEquivalences
import ProCGroups.FiniteGeneration.Basic
import ProCGroups.FiniteGeneration.CharacteristicChainsAndIndices
import ProCGroups.FiniteGroups.AllFinite
import ProCGroups.FiniteGroups.StandardClasses
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.Faithful
import ProCGroups.FiniteStepSolvableQuotients.AbelianActions.SlimnessAndTorsion
import ProCGroups.FiniteStepSolvableQuotients.Abelianization
import ProCGroups.FiniteStepSolvableQuotients.Commutators.Basic
import ProCGroups.FiniteStepSolvableQuotients.Commutators.ClosureFromFiniteQuotients
import ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients
import ProCGroups.FiniteStepSolvableQuotients.Commutators.Width
import ProCGroups.Generation.Basic
import ProCGroups.Generation.Convergence
import ProCGroups.Generation.GeneratorConvergingPairs
import ProCGroups.Generation.QuotientCriteria
import ProCGroups.Generation.QuotientGeneratorConvergingPairs
import ProCGroups.Generation.WordProductsAndClosure
import ProCGroups.GroupTheory.CentralizerNormalizerCommensurator
import ProCGroups.GroupTheory.Conjugation
import ProCGroups.GroupTheory.Subgroups
import ProCGroups.InverseSystems.CategoryBridge
import ProCGroups.InverseSystems.CountableModels
import ProCGroups.InverseSystems.Exactness
import ProCGroups.InverseSystems.FiniteStageFactorization
import ProCGroups.InverseSystems.ProfiniteLimits
import ProCGroups.InverseSystems.Quotients
import ProCGroups.InverseSystems.StagewiseIso
import ProCGroups.Order.Basic
import ProCGroups.ProC.Category.Basic
import ProCGroups.ProC.Category.Pullbacks
import ProCGroups.ProC.Category.Pushouts
import ProCGroups.ProC.GroupPredicate
import ProCGroups.ProC.GroupPredicates.Basic
import ProCGroups.ProC.GroupPredicates.Standard
import ProCGroups.ProC.GroupPredicates.Abelian
import ProCGroups.ProC.Kernels
import ProCGroups.ProC.MaximalQuotients.Definitions
import ProCGroups.ProC.MaximalQuotients.ResidualCore
import ProCGroups.ProC.MaximalQuotients.UniversalProperty
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.ProC.OpenNormalSubgroups.CountableChains
import ProCGroups.ProC.OpenNormalSubgroups.FilteredFamilies
import ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation
import ProCGroups.ProC.OpenNormalSubgroups.ClosedCommutator
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import ProCGroups.ProC.OpenNormalSubgroups.Separation
import ProCGroups.ProC.Quotients.ClosedNormal
import ProCGroups.ProC.Quotients.ClosedSubgroupNeighborhoods
import ProCGroups.ProC.Quotients.DescendingClosedSubgroupQuotients
import ProCGroups.ProC.Quotients.LeftQuotientMaps
import ProCGroups.ProC.Quotients.LeftQuotientProjectionSections
import ProCGroups.ProC.Quotients.OpenSubgroupSections
import ProCGroups.ProC.Subgroups.Products
import ProCGroups.Profinite.Basic
import ProCGroups.Profinite.MathlibBridge

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# ProCGroups

Lightweight public root for reusable profinite and pro-`C` group infrastructure.

This root keeps the default import surface small: finite-group classes, pro-`C` predicates,
profinite groups, open normal quotients, inverse systems, categorical pullbacks/pushouts,
generation, finite generation, and finite-step solvable quotients.

Advanced topics such as completions, free pro-`C` groups, free-product universal properties,
presentations, local-weight theory, normal-subgroup structure, duality, Frattini theory, and
wreath products are available from `ProCGroups.Advanced` or from their focused folder wrappers.
-/
