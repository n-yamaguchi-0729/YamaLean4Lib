import ProCGroups.FreeProC.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProC/Characterization/EmbeddingProblems.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C groups

Develops free pro-C groups on spaces and pointed spaces, their universal properties, finite quotient characterizations, and standard comparison isomorphisms.
-/

namespace ProCGroups.FreeProC.Characterization

open ProCGroups.FreeProC

universe u

section EmbeddingProblems

/-- A subgroup is minimal normal if it is nontrivial, normal, and has no proper nontrivial
normal subgroup below it. -/
def IsMinimalNormalSubgroup
    {A : Type u} [Group A] (N : Subgroup A) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧
    ∀ M : Subgroup A, M.Normal → M ≤ N → M = ⊥ ∨ M = N

/-- A topological embedding problem for a topological group.

No finiteness or pro-`C` condition is built into this structure; those are supplied by
`FiniteEmbeddingProblem` and `ProCEmbeddingProblem` below. -/
structure TopologicalEmbeddingProblem
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  A : Type u
  instGroupA : Group A
  instTopologicalSpaceA : TopologicalSpace A
  instIsTopologicalGroupA : IsTopologicalGroup A
  B : Type u
  instGroupB : Group B
  instTopologicalSpaceB : TopologicalSpace B
  instIsTopologicalGroupB : IsTopologicalGroup B
  α : A →* B
  continuous_α : Continuous α
  surjective_α : Function.Surjective α
  φ : G →* B
  continuous_φ : Continuous φ
  surjective_φ : Function.Surjective φ

attribute [instance] TopologicalEmbeddingProblem.instGroupA
attribute [instance] TopologicalEmbeddingProblem.instTopologicalSpaceA
attribute [instance] TopologicalEmbeddingProblem.instIsTopologicalGroupA
attribute [instance] TopologicalEmbeddingProblem.instGroupB
attribute [instance] TopologicalEmbeddingProblem.instTopologicalSpaceB
attribute [instance] TopologicalEmbeddingProblem.instIsTopologicalGroupB

/-- A topological embedding problem whose two finite target groups are finite. -/
structure FiniteEmbeddingProblem
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    extends TopologicalEmbeddingProblem G where
  finiteA : Finite A
  finiteB : Finite B

/-- A topological embedding problem whose two finite target groups lie in the chosen pro-`C`
predicate. -/
structure ProCEmbeddingProblem
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    extends TopologicalEmbeddingProblem G where
  isProCA : @ProCGroups.ProC.ProCGroupPredicate.holds ProC A _ _ _
  isProCB : @ProCGroups.ProC.ProCGroupPredicate.holds ProC B _ _ _

namespace TopologicalEmbeddingProblem

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The kernel of an embedding problem. -/
def kernel (P : TopologicalEmbeddingProblem G) : Subgroup P.A :=
  P.α.ker

/-- A weak solution is a continuous lift commuting with the embedding-problem square. -/
def WeakSolution (P : TopologicalEmbeddingProblem G) : Type u :=
  { φbar : G →* P.A // Continuous φbar ∧ P.α.comp φbar = P.φ }

/-- A proper solution is a surjective weak solution. -/
def ProperSolution (P : TopologicalEmbeddingProblem G) : Type u :=
  { φbar : WeakSolution P // Function.Surjective φbar.1 }

/-- Weak solvability of an embedding problem. -/
def HasWeakSolution (P : TopologicalEmbeddingProblem G) : Prop :=
  ∃ φbar : G →* P.A, Continuous φbar ∧ P.α.comp φbar = P.φ

/-- Solvability of an embedding problem. -/
def HasSolution (P : TopologicalEmbeddingProblem G) : Prop :=
  ∃ φbar : G →* P.A,
    Continuous φbar ∧ Function.Surjective φbar ∧ P.α.comp φbar = P.φ

/-- The finite minimal normal kernel condition. -/
def HasFiniteMinimalNormalKernel (P : TopologicalEmbeddingProblem G) : Prop :=
  Finite P.kernel ∧ IsMinimalNormalSubgroup P.kernel

/-- The embedding problem is split: its epimorphism has a continuous section. -/
def IsSplit (P : TopologicalEmbeddingProblem G) : Prop :=
  ∃ σ : P.B →* P.A, Continuous σ ∧ P.α.comp σ = MonoidHom.id P.B

/-- An embedding problem has at least `κ` different solutions if there is a family of pairwise
distinct continuous surjective lifts indexed by a set of cardinality `κ`. -/
def HasAtLeastProperSolutions
    (P : TopologicalEmbeddingProblem G) (κ : Cardinal) : Prop :=
  ∃ I : Type u, Cardinal.mk I = κ ∧
    ∃ ψ : I → P.ProperSolution, Function.Injective ψ

end TopologicalEmbeddingProblem

/-- A global class of embedding problems, varying with the ambient source group. -/
abbrev EmbeddingProblemPredicate :=
  {G : Type u} → [Group G] → [TopologicalSpace G] → [IsTopologicalGroup G] →
    TopologicalEmbeddingProblem G → Prop

/-- An embedding problem whose source and target both lie in the chosen pro-`C` class. -/
def IsProCEmbeddingProblem
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : TopologicalEmbeddingProblem G) : Prop :=
  @ProCGroups.ProC.ProCGroupPredicate.holds ProC P.A _ _ _ ∧
    @ProCGroups.ProC.ProCGroupPredicate.holds ProC P.B _ _ _

/-- A finite embedding problem whose two finite target groups lie in the chosen finite class. -/
def IsFiniteCEmbeddingProblem
    (C : ProCGroups.FiniteGroupClass.{u})
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : TopologicalEmbeddingProblem G) : Prop :=
  Finite P.A ∧ Finite P.B ∧
    ProCGroups.ProC.IsProCGroup C P.A ∧ ProCGroups.ProC.IsProCGroup C P.B

/-- A finite `C`-embedding problem with a continuous section. -/
def IsFiniteSplitCEmbeddingProblem
    (C : ProCGroups.FiniteGroupClass.{u})
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : TopologicalEmbeddingProblem G) : Prop :=
  IsFiniteCEmbeddingProblem C P ∧ P.IsSplit

/-- Weak lifting property over a class of embedding problems. -/
def HasWeakLiftingPropertyOver
    (E : EmbeddingProblemPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∀ P : TopologicalEmbeddingProblem G, E P → P.HasWeakSolution

/-- Strong lifting property over a class of embedding problems, with the ambient cardinal bound
exposed explicitly. -/
def HasStrongLiftingPropertyAt
    (E : EmbeddingProblemPredicate.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (κ : Cardinal) : Prop :=
  ∀ P : TopologicalEmbeddingProblem G, E P →
    Generation.topologicalRank P.B < κ →
      Generation.topologicalRank P.A ≤ κ →
        P.HasSolution

end EmbeddingProblems

end ProCGroups.FreeProC.Characterization
