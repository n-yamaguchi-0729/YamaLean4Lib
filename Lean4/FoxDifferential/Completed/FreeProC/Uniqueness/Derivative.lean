import FoxDifferential.Completed.FreeProC.Uniqueness.SemidirectHom

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/Uniqueness/Derivative.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C completed Fox calculus

Free pro-C sources are treated through completed Fox derivatives, stage projections, density arguments, and semidirect lift formulas.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.FreeProC

universe u


variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X F H : Type u}
variable [TopologicalSpace X]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]

/-- Any continuous semidirect lift with the prescribed generator components has the canonical
free pro-`C` completed Fox derivative vector as its left component. -/
theorem freeProCZCCompletedFoxDerivativeVector_unique_of_semidirect
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ))
    (f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (hf : Continuous f)
    (hleft :
      ∀ x : X, (f (ι x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H))
    (hright : ∀ x : X, (f (ι x)).right = φ x) :
    (fun g : F => (f g).left) =
      freeProCZCCompletedFoxDerivativeVector
        (ProC := ProC) hι htarget φ hφ := by
  have hgenerator :
      ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ x := by
    intro x
    apply ZCCompletedFoxSemidirect.ext
    · exact hleft x
    · exact hright x
  have hf_eq := hι.lift_unique htarget
    (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ) hφ hf hgenerator
  funext g
  rw [hf_eq]
  rfl

/-- Continuous completed crossed differentials on a free pro-`C` source are uniquely determined
by their standard generator values, provided their semidirect graph is continuous. -/
theorem freeProCZCCompletedFoxDerivativeVector_unique_of_continuousCrossedDifferential
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (ψ : F →* H) (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (hcontinuous :
      Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
        (X := X) ψ delta hdelta))
    (hbasis :
      ∀ x : X, delta (ι x) = Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) :
    delta =
      freeProCZCCompletedFoxDerivativeVector
        (ProC := ProC) hι htarget (fun x : X => ψ (ι x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
          (ProC := ProC) hι ψ delta hdelta hcontinuous hbasis) := by
  have hleft :
      ∀ x : X,
        (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
          (X := X) ψ delta hdelta (ι x)).left =
          Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) := by
    intro x
    exact hbasis x
  have hright :
      ∀ x : X,
        (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
          (X := X) ψ delta hdelta (ι x)).right = ψ (ι x) := by
    intro x
    rfl
  have hunique := freeProCZCCompletedFoxDerivativeVector_unique_of_semidirect
    (ProC := ProC) hι htarget (fun x : X => ψ (ι x))
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
      (ProC := ProC) hι ψ delta hdelta hcontinuous hbasis)
    (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ delta hdelta)
    hcontinuous hleft hright
  simpa using hunique

omit [DecidableEq X] in
/-- Extensionality for continuous completed crossed differentials on a free pro-`C` source.

The continuity hypotheses are put on the associated semidirect homomorphisms, which is the form
used by the completed Fox construction before the target topology is fully structural. -/
theorem freeProCZCCompletedCrossedDifferential_ext
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (ψ : F →* H)
    (delta epsilon :
      F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta :
      IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (hepsilon :
      IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) epsilon)
    (hdelta_continuous :
      Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
        (X := X) ψ delta hdelta))
    (hepsilon_continuous :
      Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
        (X := X) ψ epsilon hepsilon))
    (hbasis : ∀ x : X, delta (ι x) = epsilon (ι x)) :
    delta = epsilon := by
  let f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ delta hdelta
  let g : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H :=
    freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ epsilon hepsilon
  have hfg : ∀ x : X, f (ι x) = g (ι x) := by
    intro x
    apply ZCCompletedFoxSemidirect.ext
    · exact hbasis x
    · rfl
  have hsemidirect : f = g := hι.hom_ext htarget hdelta_continuous hepsilon_continuous hfg
  funext a
  exact congrArg
    (fun q : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H => (q a).left)
    hsemidirect

/-- The coefficient homomorphism of a continuous completed crossed differential agrees with the
right component of the canonical free pro-`C` semidirect lift. -/
theorem freeProCZCCompletedFoxRightHom_eq_of_continuousCrossedDifferential
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (ψ : F →* H) (delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (hcontinuous :
      Continuous (freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
        (X := X) ψ delta hdelta))
    (hbasis :
      ∀ x : X, delta (ι x) = Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) :
    ψ =
      freeProCZCCompletedFoxRightHom
        (ProC := ProC) hι htarget (fun x : X => ψ (ι x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
          (ProC := ProC) hι ψ delta hdelta hcontinuous hbasis) := by
  apply MonoidHom.ext
  intro g
  have hgenerator :
      ∀ x : X,
        freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
            (X := X) ψ delta hdelta (ι x) =
          freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) (fun x : X => ψ (ι x)) x := by
    intro x
    apply ZCCompletedFoxSemidirect.ext
    · exact hbasis x
    · rfl
  have hsemidirect := hι.lift_unique htarget
    (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) (fun x : X => ψ (ι x)))
    (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_crossedDifferential
      (ProC := ProC) hι ψ delta hdelta hcontinuous hbasis)
    (f := freeProCZCCompletedFoxSemidirectHomOfCrossedDifferential
      (X := X) ψ delta hdelta)
    hcontinuous hgenerator
  simpa [freeProCZCCompletedFoxRightHom] using
    congrArg (fun f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H => (f g).right) hsemidirect

/-- Existence and uniqueness of the free pro-`C` completed Fox derivative vector, formulated as
the left component of a continuous semidirect lift with prescribed generator data. -/
theorem existsUnique_freeProCZCCompletedFoxDerivativeVector_of_semidirect
    {ι : X → F} (hι : IsFreeProCGroup (ProC := ProC) ι)
    (htarget : ProC (G := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (φ : X → H)
    (hφ : Continuous (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ)) :
    ∃! delta : F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
      ∃ f : F →* ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        Continuous f ∧
          (∀ g : F, delta g = (f g).left) ∧
          (∀ x : X, (f (ι x)).left =
            Pi.single x (1 : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)) ∧
          ∀ x : X, (f (ι x)).right = φ x := by
  refine ⟨freeProCZCCompletedFoxDerivativeVector
    (ProC := ProC) hι htarget φ hφ, ?_, ?_⟩
  · refine ⟨freeProCZCCompletedFoxSemidirectLift
        (ProC := ProC) hι htarget φ hφ, ?_, ?_, ?_, ?_⟩
    · exact continuous_freeProCZCCompletedFoxSemidirectLift
        (ProC := ProC) hι htarget φ hφ
    · intro g
      rfl
    · exact freeProCZCCompletedFoxSemidirectLift_left_generator
        (ProC := ProC) hι htarget φ hφ
    · exact freeProCZCCompletedFoxSemidirectLift_right_generator
        (ProC := ProC) hι htarget φ hφ
  · intro delta hdelta
    rcases hdelta with ⟨f, hf, hdelta_left, hleft, hright⟩
    have hgenerator :
        ∀ x : X, f (ι x) = freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ x := by
      intro x
      apply ZCCompletedFoxSemidirect.ext
      · exact hleft x
      · exact hright x
    have hf_eq := hι.lift_unique htarget
      (freeProCZCCompletedFoxSemidirectGenerator (ProC := ProC) φ) hφ hf hgenerator
    funext g
    calc
      delta g = (f g).left := hdelta_left g
      _ = (freeProCZCCompletedFoxSemidirectLift
        (ProC := ProC) hι htarget φ hφ g).left := by
            rw [hf_eq]
            rfl
      _ = freeProCZCCompletedFoxDerivativeVector
          (ProC := ProC) hι htarget φ hφ g := rfl


end

end FoxDifferential
