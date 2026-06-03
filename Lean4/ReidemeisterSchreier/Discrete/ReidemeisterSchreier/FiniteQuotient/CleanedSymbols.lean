import ReidemeisterSchreier.Discrete.Presentations.KernelQuotient
import ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.Tau

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/ReidemeisterSchreier/FiniteQuotient/CleanedSymbols.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite quotient Reidemeister-Schreier presentations

Specializes Reidemeister-Schreier rewriting to finite quotient targets, cleaned symbols, cleaned relators, target presentations, word certificates, and Tietze equivalences.
-/

namespace ReidemeisterSchreier.Discrete.ReidemeisterSchreier

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

namespace FiniteQuotientSchreierData

variable (D : FiniteQuotientSchreierData X Q)
variable [DecidableEq X]

omit [DecidableEq X] in
def IsDegenerateSchreierSymbol (z : FiniteSchreierSymbol X Q) : Prop :=
  D.quotientSection (D.transition z.1 z.2) =
    D.quotientSection z.1 * FreeGroup.of z.2

omit [DecidableEq X] in
def degenerateSchreierRelators :
    Set (FreeGroup (FiniteSchreierSymbol X Q)) :=
  { q | ∃ s : Q, ∃ x : X,
      D.quotientSection (D.transition s x) = D.quotientSection s * FreeGroup.of x ∧
        q = FreeGroup.of (s, x) }

def presentationRelators (R : Set (FreeGroup X)) :
    Set (FreeGroup (FiniteSchreierSymbol X Q)) :=
  D.schreierRelators R ∪ D.degenerateSchreierRelators

omit [DecidableEq X] in
abbrev NondegenerateSchreierSymbol :=
  Presented.GeneratorPartition.Kept D.IsDegenerateSchreierSymbol

omit [DecidableEq X] in
abbrev DegenerateSchreierSymbol :=
  Presented.GeneratorPartition.Deleted D.IsDegenerateSchreierSymbol

omit [DecidableEq X] in
theorem trivialGeneratorRelatorsOfPredicate_isDegenerateSchreierSymbol
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    Presented.trivialGeneratorRelatorsOfPredicate D.IsDegenerateSchreierSymbol =
      D.degenerateSchreierRelators := by
  ext q
  constructor
  · intro hq
    rcases hq with ⟨p, hp, hpq⟩
    rcases hp with ⟨y, rfl⟩
    rcases y with ⟨⟨s, x⟩, hy⟩
    refine ⟨s, x, hy, ?_⟩
    rw [← hpq]
    simp only [FreeGroup.freeGroupCongr, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
  FreeGroup.map.of, Presented.GeneratorPartition.equiv_symm_inr]
  · rintro ⟨s, x, hdeg, rfl⟩
    refine ⟨FreeGroup.of (Sum.inr
      (⟨(s, x), hdeg⟩ : D.DegenerateSchreierSymbol)), ?_, ?_⟩
    · exact ⟨⟨(s, x), hdeg⟩, rfl⟩
    · simp only [FreeGroup.freeGroupCongr, MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk,
  FreeGroup.map.of, Presented.GeneratorPartition.equiv_symm_inr]

theorem relatorsWithTrivialGeneratorsOfPredicate_isDegenerateSchreierSymbol
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    Presented.relatorsWithTrivialGeneratorsOfPredicate
        (D.schreierRelators R) D.IsDegenerateSchreierSymbol =
      D.presentationRelators R := by
  change D.schreierRelators R ∪
      Presented.trivialGeneratorRelatorsOfPredicate D.IsDegenerateSchreierSymbol =
    D.schreierRelators R ∪ D.degenerateSchreierRelators
  rw [D.trivialGeneratorRelatorsOfPredicate_isDegenerateSchreierSymbol]

/-- The raw finite Reidemeister-Schreier relators after deleting the
degenerate Schreier generators with relators `s(q,x)=1`. -/
def presentationRelatorsAfterDeletingDegenerateSchreierGenerators
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    Set (FreeGroup D.NondegenerateSchreierSymbol) :=
  Presented.relatorsAfterDeletingTrivialGeneratorsOfPredicate
    (D.schreierRelators R) D.IsDegenerateSchreierSymbol

def deleteDegenerateSchreierGeneratorsTietzeEquiv
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    TietzeEquiv (D.presentationRelators R)
      (D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R) :=
  (TietzeEquiv.ofNormalClosureEq
    (R := D.presentationRelators R)
    (S := Presented.relatorsWithTrivialGeneratorsOfPredicate
      (D.schreierRelators R) D.IsDegenerateSchreierSymbol)
    (by
      rw [D.relatorsWithTrivialGeneratorsOfPredicate_isDegenerateSchreierSymbol R])).trans
    (Presented.deleteTrivialGeneratorsOfPredicateTietzeEquiv
      (D.schreierRelators R) D.IsDegenerateSchreierSymbol)

noncomputable def deleteDegenerateSchreierGenerators
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    PresentedGroup (D.presentationRelators R) ≃*
      PresentedGroup
        (D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R) :=
  (D.deleteDegenerateSchreierGeneratorsTietzeEquiv R).presentedEquiv

/-- The homomorphism that deletes degenerate finite Schreier generators.  A
nondegenerate generator is kept, and a degenerate generator is sent to `1`. -/
def deleteDegenerateSchreierGeneratorHom
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    FreeGroup (FiniteSchreierSymbol X Q) →*
      FreeGroup D.NondegenerateSchreierSymbol :=
  (Presented.trivializeGeneratorsHom
      D.NondegenerateSchreierSymbol D.DegenerateSchreierSymbol).comp
    (FreeGroup.freeGroupCongr
      (Presented.GeneratorPartition.equiv D.IsDegenerateSchreierSymbol))

omit [DecidableEq X] in
@[simp]
theorem deleteDegenerateSchreierGeneratorHom_of_not_degenerate
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {z : FiniteSchreierSymbol X Q} (hz : ¬ D.IsDegenerateSchreierSymbol z) :
    D.deleteDegenerateSchreierGeneratorHom (FreeGroup.of z) =
      FreeGroup.of (⟨z, hz⟩ : D.NondegenerateSchreierSymbol) := by
  simp only [deleteDegenerateSchreierGeneratorHom, MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
  FreeGroup.freeGroupCongr_apply, FreeGroup.map.of,
  Presented.GeneratorPartition.equiv_apply_of_not_delete D.IsDegenerateSchreierSymbol hz,
  Presented.trivializeGeneratorsHom_inl]

omit [DecidableEq X] in
@[simp]
theorem deleteDegenerateSchreierGeneratorHom_of_degenerate
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {z : FiniteSchreierSymbol X Q} (hz : D.IsDegenerateSchreierSymbol z) :
    D.deleteDegenerateSchreierGeneratorHom (FreeGroup.of z) = 1 := by
  simp only [deleteDegenerateSchreierGeneratorHom, MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
  FreeGroup.freeGroupCongr_apply, FreeGroup.map.of,
  Presented.GeneratorPartition.equiv_apply_of_delete D.IsDegenerateSchreierSymbol hz,
  Presented.trivializeGeneratorsHom_inr]

omit [DecidableEq X] in
theorem symbolEval_eq_one_of_isDegenerateSchreierSymbol
    {z : FiniteSchreierSymbol X Q} (hz : D.IsDegenerateSchreierSymbol z) :
    D.symbolEval z = 1 := by
  rcases z with ⟨q, x⟩
  simp only [IsDegenerateSchreierSymbol, transition_eq, symbolEval, schreierGenerator] at hz ⊢
  rw [hz]
  group

/-- The evaluation map on the nondegenerate finite Schreier generators. -/
def nondegenerateSymbolEval
    (z : D.NondegenerateSchreierSymbol) : FreeGroup X :=
  D.symbolEval z.1

def nondegenerateSymbolEvalHom :
    FreeGroup D.NondegenerateSchreierSymbol →* FreeGroup X :=
  FreeGroup.lift D.nondegenerateSymbolEval

omit [DecidableEq X] in
theorem nondegenerateSymbolEvalHom_deleteDegenerateSchreierGeneratorHom
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (w : FreeGroup (FiniteSchreierSymbol X Q)) :
    D.nondegenerateSymbolEvalHom
        (D.deleteDegenerateSchreierGeneratorHom w) =
      D.symbolEvalHom w := by
  let F : FreeGroup (FiniteSchreierSymbol X Q) →* FreeGroup X :=
    D.nondegenerateSymbolEvalHom.comp D.deleteDegenerateSchreierGeneratorHom
  have hF : F = D.symbolEvalHom := by
    ext z
    by_cases hz : D.IsDegenerateSchreierSymbol z
    · simp only [MonoidHom.coe_comp, Function.comp_apply, D.deleteDegenerateSchreierGeneratorHom_of_degenerate hz,
  map_one, symbolEvalHom_of, D.symbolEval_eq_one_of_isDegenerateSchreierSymbol hz, F]
    · simp only [nondegenerateSymbolEvalHom, MonoidHom.coe_comp, Function.comp_apply,
  D.deleteDegenerateSchreierGeneratorHom_of_not_degenerate hz, FreeGroup.lift_apply_of, nondegenerateSymbolEval,
  symbolEvalHom, F]
  exact congrArg (fun f : FreeGroup (FiniteSchreierSymbol X Q) →* FreeGroup X => f w) hF

/-- A single finite Schreier generator after deleting degenerate generators. -/
def cleanedSchreierSymbolWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (z : FiniteSchreierSymbol X Q) :
    FreeGroup D.NondegenerateSchreierSymbol :=
  if hz : D.IsDegenerateSchreierSymbol z then
    1
  else
    FreeGroup.of (⟨z, hz⟩ : D.NondegenerateSchreierSymbol)

omit [DecidableEq X] in
@[simp]
theorem cleanedSchreierSymbolWord_of_degenerate
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {z : FiniteSchreierSymbol X Q} (hz : D.IsDegenerateSchreierSymbol z) :
    D.cleanedSchreierSymbolWord z = 1 := by
  simp only [cleanedSchreierSymbolWord, hz, ↓reduceDIte]

omit [DecidableEq X] in
@[simp]
theorem cleanedSchreierSymbolWord_of_not_degenerate
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {z : FiniteSchreierSymbol X Q} (hz : ¬ D.IsDegenerateSchreierSymbol z) :
    D.cleanedSchreierSymbolWord z =
      FreeGroup.of (⟨z, hz⟩ : D.NondegenerateSchreierSymbol) := by
  simp only [cleanedSchreierSymbolWord, hz, ↓reduceDIte]

omit [DecidableEq X] in
@[simp]
theorem deleteDegenerateSchreierGeneratorHom_of
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (z : FiniteSchreierSymbol X Q) :
    D.deleteDegenerateSchreierGeneratorHom (FreeGroup.of z) =
      D.cleanedSchreierSymbolWord z := by
  by_cases hz : D.IsDegenerateSchreierSymbol z
  · simp only [hz, deleteDegenerateSchreierGeneratorHom_of_degenerate, cleanedSchreierSymbolWord_of_degenerate]
  · simp only [hz, not_false_eq_true, deleteDegenerateSchreierGeneratorHom_of_not_degenerate,
  cleanedSchreierSymbolWord_of_not_degenerate]


end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete.ReidemeisterSchreier
