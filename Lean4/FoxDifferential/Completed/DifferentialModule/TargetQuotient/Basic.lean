import FoxDifferential.Completed.DifferentialModule.Map.Surjective
import FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.Index

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/DifferentialModule/TargetQuotient/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed differential modules

The completed differential module is organized separately from coefficient algebras; its universal and quotient maps are used by completed crossed differentials.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]

/-- Definition of finiteFoxStageTargetQuotientContinuousMonoidHom. -/
def finiteFoxStageTargetQuotientContinuousMonoidHom
    [TopologicalSpace (FreeGroup X)] [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)] :
    ContinuousMonoidHom (FreeGroup X) (finiteFoxStageTargetQuotient (X := X) N) where
  toMonoidHom := QuotientGroup.mk' N
  continuous_toFun := continuous_of_discreteTopology

omit [DecidableEq X] in
/-- Evaluation formula for finiteFoxStageTargetQuotientContinuousMonoidHom_apply. -/
@[simp]
theorem finiteFoxStageTargetQuotientContinuousMonoidHom_apply
    [TopologicalSpace (FreeGroup X)] [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    (w : FreeGroup X) :
    finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N w =
      QuotientGroup.mk' N w := rfl

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- The completed free derivative source finite stage `[N,N]N^{ell^a}` refines every finite stage pulled back
from the target quotient `F/N`.  This is the order comparison that lets the completed
group-algebra projection for `π : Z_ell[[F]] -> Z_ell[[F/N]]` be read from the completed free derivative source
projection. -/
theorem finiteFoxStagePrimePowerSourceCompletedIndex_le_targetQuotientComap
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (finiteFoxStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (finiteFoxStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (j : PrimePowerCompletedGroupAlgebraIndex
      (finiteFoxStageTargetQuotient (X := X) N)) :
    completedGroupAlgebraComapIndex
        (G := FreeGroup X) (H := finiteFoxStageTargetQuotient (X := X) N)
        (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N) j.2 ≤
      finiteFoxStagePrimePowerSourceCompletedIndex
        (ℓ := ℓ) (X := X) N hfinite j.1 := by
  change finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1) ≤
    Subgroup.comap
      (finiteFoxStageTargetQuotientContinuousMonoidHom (X := X) N).toMonoidHom
      (((OrderDual.ofDual j.2).1 :
        OpenNormalSubgroup (finiteFoxStageTargetQuotient (X := X) N)) :
        Subgroup (finiteFoxStageTargetQuotient (X := X) N))
  intro g hg
  change QuotientGroup.mk' N g ∈
    (((OrderDual.ofDual j.2).1 :
      OpenNormalSubgroup (finiteFoxStageTargetQuotient (X := X) N)) :
      Subgroup (finiteFoxStageTargetQuotient (X := X) N))
  have hgN : g ∈ N :=
    finiteFoxCommutatorPowerSubgroup_le_normal (F := FreeGroup X) N (ℓ ^ j.1) hg
  have hgq : QuotientGroup.mk' N g =
      (1 : finiteFoxStageTargetQuotient (X := X) N) := by
    simpa using (QuotientGroup.eq_one_iff (N := N) g).2 hgN
  rw [hgq]
  exact Subgroup.one_mem _


end

end FoxDifferential
