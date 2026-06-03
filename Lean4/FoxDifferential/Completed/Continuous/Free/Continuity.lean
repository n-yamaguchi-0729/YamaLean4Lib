import FoxDifferential.Completed.FreeProC.Uniqueness.Derivative
import FoxDifferential.Completed.Continuous.Topology

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Continuous/Free/Continuity.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Continuous crossed differentials

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open scoped BigOperators

universe u


variable {ProC : ProCGroups.ProC.ProCGroupPredicate.{u}}
variable [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
variable (X H : Type u) [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- The completed Fox semidirect generator map is continuous when both component maps are
continuous. -/
theorem continuous_freeProCZCCompletedFoxSemidirectGenerator
    [TopologicalSpace X]
    (φ : X → H)
    (hleft : Continuous (fun x : X =>
      Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)))
    (hφ : Continuous φ) :
    Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ) := by
  rw [continuous_induced_rng]
  exact hleft.prodMk hφ

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- The completed Fox semidirect generator map is continuous for a discrete generating space. -/
theorem continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete
    [TopologicalSpace X] [DiscreteTopology X] (φ : X → H) :
    Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ) :=
  continuous_of_discreteTopology

variable {F : Type u}
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
  [DecidableEq X] [IsTopologicalGroup F] in
/-- A crossed-differential graph into the completed Fox semidirect target is continuous when both
its component maps are continuous. -/
theorem continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
    (ψ : F →* H)
    (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential
      (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ) :
    Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (ProC := ProC) (X := X) (F := F) (H := H) ψ delta hdelta) := by
  rw [continuous_induced_rng]
  exact hdelta_continuous.prodMk hψ_continuous

variable [TopologicalSpace X]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- The target-group component of the free pro-`C` completed Fox semidirect lift is continuous. -/
theorem continuous_freeProCZCCompletedFoxRightHom
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)) :
    Continuous (freeProCZCCompletedFoxRightHom
      (ProC := ProC) hι htarget φ hφ) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLift
      (ProC := ProC) hι htarget φ hφ g).right)
  exact (continuous_zcCompletedFoxSemidirect_right ProC.finiteQuotientClass X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLift
      (ProC := ProC) hι htarget φ hφ)

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
  [TopologicalSpace X] in
/-- The right component of the converging-set completed Fox semidirect lift is continuous. -/
theorem continuous_freeProCZCCompletedFoxRightHomOfConvergingSet
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) X F ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (Set.range (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))) :
    Continuous (freeProCZCCompletedFoxRightHomOfConvergingSet
      (ProC := ProC) hι htarget φ hφconv hφgen) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLiftOfConvergingSet
      (ProC := ProC) hι htarget φ hφconv hφgen g).right)
  exact (continuous_zcCompletedFoxSemidirect_right ProC.finiteQuotientClass X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLiftOfConvergingSet
      (ProC := ProC) hι htarget φ hφconv hφgen)

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
  [TopologicalSpace X] in
/-- The right component of the converging-set semidirect Fox lift is exactly the universal
free-pro-`C` lift of its generator values. -/
theorem freeProCZCCompletedFoxRightHomOfConvergingSet_eq_lift
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) X F ι)
    (hH : ProC (G := H))
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (Set.range (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)))
    (hφHconv : ProCGroups.FreeProC.FamilyConvergesToOne (G := H) φ)
    (hφHgen : ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    freeProCZCCompletedFoxRightHomOfConvergingSet
        (ProC := ProC) hι htarget φ hφconv hφgen =
      hι.lift hH φ hφHconv hφHgen := by
  apply hι.lift_unique hH φ hφHconv hφHgen
  · exact continuous_freeProCZCCompletedFoxRightHomOfConvergingSet
      (ProC := ProC) X H hι htarget φ hφconv hφgen
  · intro x
    simp only [freeProCZCCompletedFoxRightHomOfConvergingSet_generator]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
  [TopologicalSpace X] in
/-- The closed-generated completed Fox semidirect lift is continuous as a map to the full
semidirect target. -/
theorem continuous_freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) X F ι)
    (φ : X → H)
    (htarget :
      ProC (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (ProC := ProC) φ : Subgroup
            (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) φ : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator (ProC := ProC) φ)) :
    Continuous (freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
      (ProC := ProC) hι φ htarget hφconv) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLiftToClosedGenerated
      (ProC := ProC) hι φ htarget hφconv g :
        ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
  exact continuous_subtype_val.comp
    (freeProCZCCompletedFoxSemidirectLiftHomToClosedGenerated
      (ProC := ProC) hι φ htarget hφconv).continuous_toFun

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
  [TopologicalSpace X] in
/-- The right component of the closed-generated completed Fox semidirect lift is continuous. -/
theorem continuous_freeProCZCCompletedFoxRightHomViaClosedGenerated
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) X F ι)
    (φ : X → H)
    (htarget :
      ProC (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (ProC := ProC) φ : Subgroup
            (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) φ : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator (ProC := ProC) φ)) :
    Continuous (freeProCZCCompletedFoxRightHomViaClosedGenerated
      (ProC := ProC) hι φ htarget hφconv) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
      (ProC := ProC) hι φ htarget hφconv g).right)
  exact (continuous_zcCompletedFoxSemidirect_right ProC.finiteQuotientClass X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
      (ProC := ProC) X H hι φ htarget hφconv)

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
  [TopologicalSpace X] in
/-- The right component of the closed-generated semidirect Fox lift is the universal
free-pro-`C` lift of its generator values. -/
theorem freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_lift
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) X F ι)
    (hH : ProC (G := H))
    (φ : X → H)
    (htarget :
      ProC (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (ProC := ProC) φ : Subgroup
            (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) φ : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator (ProC := ProC) φ))
    (hφHconv : ProCGroups.FreeProC.FamilyConvergesToOne (G := H) φ)
    (hφHgen : ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ)) :
    freeProCZCCompletedFoxRightHomViaClosedGenerated
        (ProC := ProC) hι φ htarget hφconv =
      hι.lift hH φ hφHconv hφHgen := by
  apply hι.lift_unique hH φ hφHconv hφHgen
  · exact continuous_freeProCZCCompletedFoxRightHomViaClosedGenerated
      (ProC := ProC) X H hι φ htarget hφconv
  · intro x
    simp only [freeProCZCCompletedFoxRightHomViaClosedGenerated_generator]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
  [TopologicalSpace X] in
/-- The right component of the closed-generated semidirect Fox lift is any continuous
homomorphism with the same generator values.

This is the paper graph's target-coordinate verification: once the closed-generated lift has
right value `φ x` on every free generator `ι x`, the free pro-`C` universal property identifies
that right component with the intended continuous homomorphism. -/
theorem freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_continuousHom
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) X F ι)
    (hH : ProC (G := H))
    (φ : X → H)
    (htarget :
      ProC (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (ProC := ProC) φ : Subgroup
            (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) φ : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator (ProC := ProC) φ))
    (hφHconv : ProCGroups.FreeProC.FamilyConvergesToOne (G := H) φ)
    (hφHgen : ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ))
    (ψ : F →ₜ* H)
    (hψ_gen : ∀ x : X, ψ (ι x) = φ x) :
    freeProCZCCompletedFoxRightHomViaClosedGenerated
        (ProC := ProC) hι φ htarget hφconv =
      ψ.toMonoidHom := by
  have hright_lift :
      freeProCZCCompletedFoxRightHomViaClosedGenerated
          (ProC := ProC) hι φ htarget hφconv =
        hι.lift hH φ hφHconv hφHgen :=
    freeProCZCCompletedFoxRightHomViaClosedGenerated_eq_lift
      (ProC := ProC) X H hι hH φ htarget hφconv hφHconv hφHgen
  have hψ_lift :
      ψ.toMonoidHom = hι.lift hH φ hφHconv hφHgen := by
    apply hι.lift_unique hH φ hφHconv hφHgen
    · exact ψ.continuous_toFun
    · exact hψ_gen
  exact hright_lift.trans hψ_lift.symm

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
  [TopologicalSpace X] in
/-- The derivative-vector component of the closed-generated semidirect lift is continuous. -/
theorem continuous_freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) X F ι)
    (φ : X → H)
    (htarget :
      ProC (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (ProC := ProC) φ : Subgroup
            (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))))
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G :=
          (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
            (ProC := ProC) φ : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)))
        (freeProCZCCompletedFoxSemidirectClosedGeneratedGenerator (ProC := ProC) φ)) :
    Continuous (freeProCZCCompletedFoxDerivativeVectorViaClosedGenerated
      (ProC := ProC) hι φ htarget hφconv) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
      (ProC := ProC) hι φ htarget hφconv g).left)
  exact (continuous_zcCompletedFoxSemidirect_left ProC.finiteQuotientClass X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLiftViaClosedGenerated
      (ProC := ProC) X H hι φ htarget hφconv)

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- The completed Fox derivative-vector component of the free pro-`C` semidirect lift is
continuous. -/
theorem continuous_freeProCZCCompletedFoxDerivativeVector
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)) :
    Continuous (freeProCZCCompletedFoxDerivativeVector
      (ProC := ProC) hι htarget φ hφ) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLift
      (ProC := ProC) hι htarget φ hφ g).left)
  exact (continuous_zcCompletedFoxSemidirect_left ProC.finiteQuotientClass X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLift
      (ProC := ProC) hι htarget φ hφ)

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)]
  [TopologicalSpace X] in
/-- The derivative-vector component of the converging-set completed Fox semidirect lift is
continuous. -/
theorem continuous_freeProCZCCompletedFoxDerivativeVectorOfConvergingSet
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) X F ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφconv :
      ProCGroups.FreeProC.FamilyConvergesToOne
        (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))
    (hφgen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
        (Set.range (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))) :
    Continuous (freeProCZCCompletedFoxDerivativeVectorOfConvergingSet
      (ProC := ProC) hι htarget φ hφconv hφgen) := by
  change Continuous (fun g : F =>
    (freeProCZCCompletedFoxSemidirectLiftOfConvergingSet
      (ProC := ProC) hι htarget φ hφconv hφgen g).left)
  exact (continuous_zcCompletedFoxSemidirect_left ProC.finiteQuotientClass X H).comp
    (continuous_freeProCZCCompletedFoxSemidirectLiftOfConvergingSet
      (ProC := ProC) hι htarget φ hφconv hφgen)

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- The semidirect generator map attached to a continuous crossed differential is continuous once
the component maps are continuous. -/
theorem continuous_freeProCZCFoxSemiGenerator_of_continuousCrossedDiff
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (ψ : F →* H)
    (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential
      (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) :
    Continuous (freeProCZCCompletedFoxSemidirectGenerator
      (ProC := ProC) (fun x : X => ψ (ι x))) :=
  continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
    (ProC := ProC) hι ψ delta hdelta
    (continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (ProC := ProC) (X := X) (F := F) (H := H)
      ψ delta hdelta hdelta_continuous hψ_continuous)
    hbasis

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly ProC.finiteQuotientClass)] in
/-- Continuous completed crossed differentials with continuous coefficient homomorphism are
uniquely identified with the canonical free pro-`C` completed Fox derivative vector. -/
theorem freeProCZCCompletedFoxDerivativeVector_unique_of_continuousCrossedDiff_components
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (ψ : F →* H)
    (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential
      (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) :
    delta =
      freeProCZCCompletedFoxDerivativeVector
        (ProC := ProC) hι htarget (fun x : X => ψ (ι x))
        (continuous_freeProCZCFoxSemiGenerator_of_continuousCrossedDiff
          (ProC := ProC) X H hι ψ delta hdelta hdelta_continuous hψ_continuous hbasis) :=
  freeProCZCCompletedFoxDerivativeVector_unique_of_continuousCrossedDifferential
    (ProC := ProC) hι htarget ψ delta hdelta
    (continuous_freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (ProC := ProC) (X := X) (F := F) (H := H)
      ψ delta hdelta hdelta_continuous hψ_continuous)
    hbasis

end

end FoxDifferential
