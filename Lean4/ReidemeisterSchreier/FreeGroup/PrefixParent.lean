import Mathlib.GroupTheory.FreeGroup.Reduce

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/FreeGroup/PrefixParent.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free-group support

Automorphisms, signed-letter words, prefix-parent operations, and generator equivalences for free groups.
-/

namespace ReidemeisterSchreier

/-- A signed generator letter in the word model of a free group. -/
abbrev SignedLetter (X : Type u) := X × Bool

namespace SignedLetter

/-- The inverse signed letter. -/
def inv {X : Type u} (y : SignedLetter X) : SignedLetter X :=
  (y.1, !y.2)

@[simp] theorem inv_fst {X : Type u} (y : SignedLetter X) : y.inv.1 = y.1 := rfl
@[simp] theorem inv_snd {X : Type u} (y : SignedLetter X) : y.inv.2 = !y.2 := rfl
@[simp] theorem inv_inv {X : Type u} (y : SignedLetter X) : y.inv.inv = y := by
  cases y
  simp only [inv, Bool.not_not]

end SignedLetter

namespace Internal.FreeGroupWord

theorem FreeGroup.invRev_eq_getLast_append_dropLast {X : Type u}
    (w : List (X × Bool)) (hw : w ≠ []) :
    FreeGroup.invRev w =
      [((w.getLast hw).1, ! (w.getLast hw).2)] ++ FreeGroup.invRev w.dropLast := by
  refine (congrArg FreeGroup.invRev (List.dropLast_append_getLast hw)).symm.trans ?_
  simp only [FreeGroup.invRev, List.map_append, List.map_dropLast, List.map_cons, List.map_nil,
  List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]

end Internal.FreeGroupWord

/-- The last signed letter of the reduced word representing `g`, if it is nonempty. -/
def FreeGroup.lastLetter? {X : Type u} [DecidableEq X] (g : FreeGroup X) :
    Option (SignedLetter X) :=
  (FreeGroup.toWord g).getLast?

namespace Internal.FreeGroupWord

theorem FreeGroup.lastLetter?_eq_some_iff {X : Type u} [DecidableEq X]
    {g : FreeGroup X} {y : SignedLetter X} :
    FreeGroup.lastLetter? g = some y ↔
      ∃ hw : FreeGroup.toWord g ≠ [], (FreeGroup.toWord g).getLast hw = y := by
  constructor
  · intro h
    have hy : y ∈ (FreeGroup.toWord g).getLast? := by
      simpa [FreeGroup.lastLetter?, h]
    rcases List.mem_getLast?_eq_getLast hy with ⟨hw, hyw⟩
    exact ⟨hw, hyw.symm⟩
  · rintro ⟨hw, hlast⟩
    rw [FreeGroup.lastLetter?, List.getLast?_eq_getLast_of_ne_nil hw, hlast]

theorem FreeGroup.toWord_mul_of_of_not_cancels {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (x : X)
    (hcancel : ¬ ∃ hw : FreeGroup.toWord t ≠ [], (FreeGroup.toWord t).getLast hw = (x, false)) :
    FreeGroup.toWord (t * FreeGroup.of x) = FreeGroup.toWord t ++ [(x, true)] := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_of]
  have hred : FreeGroup.IsReduced (FreeGroup.toWord t ++ [(x, true)]) := by
    refine List.IsChain.append (FreeGroup.isReduced_toWord (x := t)) ?_ ?_
    · simp only [List.IsChain.singleton]
    · intro a ha b hb hab
      have hb' : (x, true) = b := by simpa using hb
      cases hb'
      rcases List.mem_getLast?_eq_getLast ha with ⟨hw, rfl⟩
      have hne : (FreeGroup.toWord t).getLast hw ≠ (x, false) := by
        intro hlast
        exact hcancel ⟨hw, hlast⟩
      dsimp at hab hne ⊢
      cases h2 : ((FreeGroup.toWord t).getLast hw).2 with
      | false =>
          exfalso
          apply hne
          apply Prod.ext
          · exact hab
          · simpa using h2
      | true => rfl
  exact hred.reduce_eq

theorem FreeGroup.mul_of_of_eq_mk_dropLast_of_cancels {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (x : X) (hw : FreeGroup.toWord t ≠ [])
    (hlast : (FreeGroup.toWord t).getLast hw = (x, false)) :
    t * FreeGroup.of x = FreeGroup.mk ((FreeGroup.toWord t).dropLast) := by
  rw [← FreeGroup.mk_toWord (x := t)]
  simp only [FreeGroup.toWord_mk, FreeGroup.reduce_toWord]
  rw [FreeGroup.of, FreeGroup.mul_mk]
  have ht :
      FreeGroup.toWord t =
        (FreeGroup.toWord t).dropLast ++ [(FreeGroup.toWord t).getLast hw] := by
    simpa using (List.dropLast_append_getLast hw).symm
  rw [ht, hlast]
  simp only [List.append_assoc, List.cons_append, List.nil_append, ne_eq, List.cons_ne_self,
    not_false_eq_true, List.dropLast_append_of_ne_nil, List.dropLast_singleton, List.append_nil]
  exact Quot.sound (show FreeGroup.Red.Step
      ((FreeGroup.toWord t).dropLast ++ (x, false) :: (x, true) :: [])
      ((FreeGroup.toWord t).dropLast) from by
        simpa using (show FreeGroup.Red.Step
          ((FreeGroup.toWord t).dropLast ++ (x, false) :: (x, true) :: [])
          ((FreeGroup.toWord t).dropLast ++ []) from by constructor))

theorem FreeGroup.toWord_mul_of_of_cancels {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (x : X) (hw : FreeGroup.toWord t ≠ [])
    (hlast : (FreeGroup.toWord t).getLast hw = (x, false)) :
    FreeGroup.toWord (t * FreeGroup.of x) = (FreeGroup.toWord t).dropLast := by
  rw [FreeGroup.mul_of_of_eq_mk_dropLast_of_cancels t x hw hlast, FreeGroup.toWord_mk]
  have hred : FreeGroup.IsReduced ((FreeGroup.toWord t).dropLast) := by
    exact (FreeGroup.isReduced_toWord (x := t)).dropLast
  simpa using hred.reduce_eq

/-- Appending a reduced signed letter to a reduced word stays reduced unless the last letter is
its inverse. -/
theorem FreeGroup.toWord_mul_mk_singleton_of_not_cancels {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (y : X × Bool)
    (hcancel :
      ¬ ∃ hw : FreeGroup.toWord t ≠ [],
          (FreeGroup.toWord t).getLast hw = (y.1, !y.2)) :
    FreeGroup.toWord (t * FreeGroup.mk [y]) = FreeGroup.toWord t ++ [y] := by
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_mk]
  have hred : FreeGroup.IsReduced (FreeGroup.toWord t ++ [y]) := by
    refine List.IsChain.append (FreeGroup.isReduced_toWord (x := t)) ?_ ?_
    · simp only [List.IsChain.singleton]
    · intro a ha b hb hab
      have hb' : y = b := by simpa using hb
      cases hb'
      rcases List.mem_getLast?_eq_getLast ha with ⟨hw, rfl⟩
      have hne : (FreeGroup.toWord t).getLast hw ≠ (y.1, !y.2) := by
        intro hlast
        exact hcancel ⟨hw, hlast⟩
      dsimp at hab hne ⊢
      cases h2 : ((FreeGroup.toWord t).getLast hw).2 with
      | false =>
          cases y with
          | mk x b =>
              cases b with
              | false => rfl
              | true =>
                  exfalso
                  apply hne
                  apply Prod.ext
                  · exact hab
                  · simpa using h2
      | true =>
          cases y with
          | mk x b =>
              cases b with
              | false =>
                  exfalso
                  apply hne
                  apply Prod.ext
                  · exact hab
                  · simp only [h2, Bool.not_false]
              | true => rfl
  exact hred.reduce_eq

/-- Cancelling a reduced signed letter on the right amounts to deleting the last letter in the
word model. -/
theorem FreeGroup.mul_mk_singleton_eq_mk_dropLast_of_cancels {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (y : X × Bool) (hw : FreeGroup.toWord t ≠ [])
    (hlast : (FreeGroup.toWord t).getLast hw = (y.1, !y.2)) :
    t * FreeGroup.mk [y] = FreeGroup.mk ((FreeGroup.toWord t).dropLast) := by
  rw [← FreeGroup.mk_toWord (x := t)]
  simp only [FreeGroup.toWord_mk, FreeGroup.reduce_toWord]
  have ht :
      FreeGroup.toWord t =
        (FreeGroup.toWord t).dropLast ++ [(FreeGroup.toWord t).getLast hw] := by
    simpa using (List.dropLast_append_getLast hw).symm
  rw [ht, hlast]
  simp only [FreeGroup.mul_mk, List.append_assoc, List.cons_append, List.nil_append, ne_eq,
    List.cons_ne_self, not_false_eq_true, List.dropLast_append_of_ne_nil,
    List.dropLast_singleton, List.append_nil]
  exact Quot.sound
    (show FreeGroup.Red.Step
        ((FreeGroup.toWord t).dropLast ++ (y.1, !y.2) :: y :: [])
        ((FreeGroup.toWord t).dropLast) from by
      simpa using
        (show FreeGroup.Red.Step
            ((FreeGroup.toWord t).dropLast ++ (y.1, !y.2) :: y :: [])
            ((FreeGroup.toWord t).dropLast ++ []) from
          FreeGroup.Red.Step.not_rev))

theorem FreeGroup.toWord_mul_mk_singleton_of_cancels {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (y : X × Bool) (hw : FreeGroup.toWord t ≠ [])
    (hlast : (FreeGroup.toWord t).getLast hw = (y.1, !y.2)) :
    FreeGroup.toWord (t * FreeGroup.mk [y]) = (FreeGroup.toWord t).dropLast := by
  rw [FreeGroup.mul_mk_singleton_eq_mk_dropLast_of_cancels t y hw hlast, FreeGroup.toWord_mk]
  have hred : FreeGroup.IsReduced ((FreeGroup.toWord t).dropLast) := by
    exact (FreeGroup.isReduced_toWord (x := t)).dropLast
  simpa using hred.reduce_eq

/-- Unified signed-letter multiplication rule for reduced words. -/
theorem FreeGroup.toWord_mul_singleton {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (y : SignedLetter X) :
    FreeGroup.toWord (t * FreeGroup.mk [y]) =
      if FreeGroup.lastLetter? t = some y.inv then
        (FreeGroup.toWord t).dropLast
      else
        FreeGroup.toWord t ++ [y] := by
  by_cases hlast? : FreeGroup.lastLetter? t = some y.inv
  · rw [if_pos hlast?]
    rcases (FreeGroup.lastLetter?_eq_some_iff (g := t) (y := y.inv)).1 hlast? with
      ⟨hw, hlast⟩
    simpa [SignedLetter.inv] using
      FreeGroup.toWord_mul_mk_singleton_of_cancels t y hw hlast
  · rw [if_neg hlast?]
    have hcancel :
        ¬ ∃ hw : FreeGroup.toWord t ≠ [],
            (FreeGroup.toWord t).getLast hw = (y.1, !y.2) := by
      intro h
      exact hlast?
        ((FreeGroup.lastLetter?_eq_some_iff (g := t) (y := y.inv)).2 (by
          simpa [SignedLetter.inv] using h))
    exact FreeGroup.toWord_mul_mk_singleton_of_not_cancels t y hcancel

/-- Positive generators are the positive signed-letter specialization of
`FreeGroup.toWord_mul_singleton`. -/
theorem FreeGroup.toWord_mul_of {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (x : X) :
    FreeGroup.toWord (t * FreeGroup.of x) =
      if FreeGroup.lastLetter? t = some ((x, false) : SignedLetter X) then
        (FreeGroup.toWord t).dropLast
      else
        FreeGroup.toWord t ++ [(x, true)] := by
  simpa [FreeGroup.of, SignedLetter.inv] using
    (FreeGroup.toWord_mul_singleton t ((x, true) : SignedLetter X))

end Internal.FreeGroupWord

/-- The predecessor of a reduced word, obtained by deleting its last letter. -/
def FreeGroup.prefixParent {X : Type u} [DecidableEq X] (t : FreeGroup X) : FreeGroup X :=
  FreeGroup.mk ((FreeGroup.toWord t).dropLast)

namespace Internal.FreeGroupWord

/-- Multiplication by a signed singleton either deletes the inverse last letter or appends the
singleton to the reduced word. -/
theorem FreeGroup.mul_mk_singleton_eq_ite_prefixParent {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (y : X × Bool) :
    t * FreeGroup.mk [y] =
      if _ : ∃ hw : FreeGroup.toWord t ≠ [],
          (FreeGroup.toWord t).getLast hw = (y.1, !y.2)
      then FreeGroup.prefixParent t
      else FreeGroup.mk (FreeGroup.toWord t ++ [y]) := by
  by_cases h : ∃ hw : FreeGroup.toWord t ≠ [],
      (FreeGroup.toWord t).getLast hw = (y.1, !y.2)
  · rcases h with ⟨hw, hlast⟩
    rw [dif_pos ⟨hw, hlast⟩]
    exact FreeGroup.mul_mk_singleton_eq_mk_dropLast_of_cancels t y hw hlast
  · rw [dif_neg h]
    calc
      t * FreeGroup.mk [y] =
          FreeGroup.mk (FreeGroup.toWord (t * FreeGroup.mk [y])) := by
            exact (FreeGroup.mk_toWord (x := t * FreeGroup.mk [y])).symm
      _ = FreeGroup.mk (FreeGroup.toWord t ++ [y]) := by
            rw [FreeGroup.toWord_mul_mk_singleton_of_not_cancels t y h]

@[simp] theorem FreeGroup.toWord_prefixParent {X : Type u} [DecidableEq X] (t : FreeGroup X) :
    FreeGroup.toWord (FreeGroup.prefixParent t) = (FreeGroup.toWord t).dropLast := by
  rw [FreeGroup.prefixParent, FreeGroup.toWord_mk]
  have hred : FreeGroup.IsReduced ((FreeGroup.toWord t).dropLast) := by
    exact (FreeGroup.isReduced_toWord (x := t)).dropLast
  exact hred.reduce_eq

theorem FreeGroup.toWord_length_prefixParent_lt {X : Type u} [DecidableEq X]
    {t : FreeGroup X} (ht : t ≠ 1) :
    (FreeGroup.toWord (FreeGroup.prefixParent t)).length < (FreeGroup.toWord t).length := by
  rw [FreeGroup.toWord_prefixParent, List.length_dropLast]
  have hnonempty : FreeGroup.toWord t ≠ [] := by
    exact mt (FreeGroup.toWord_eq_nil_iff.mp) ht
  have hlen : 0 < (FreeGroup.toWord t).length := List.length_pos_iff_ne_nil.mpr hnonempty
  simpa using Nat.pred_lt (Nat.ne_of_gt hlen)

theorem FreeGroup.length_prefixParent_eq_pred {X : Type u} [DecidableEq X]
    (t : FreeGroup X) :
    (FreeGroup.toWord (FreeGroup.prefixParent t)).length =
      (FreeGroup.toWord t).length - 1 := by
  rw [FreeGroup.toWord_prefixParent, List.length_dropLast]

theorem FreeGroup.prefixParent_mul_of_of_last_pos {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (x : X) (hw : FreeGroup.toWord t ≠ [])
    (hlast : (FreeGroup.toWord t).getLast hw = (x, true)) :
    FreeGroup.prefixParent t * FreeGroup.of x = t := by
  apply FreeGroup.toWord_injective
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_of]
  have ht : FreeGroup.toWord t =
      (FreeGroup.toWord t).dropLast ++ [(FreeGroup.toWord t).getLast hw] := by
    simpa using (List.dropLast_append_getLast hw).symm
  have hword : FreeGroup.toWord (FreeGroup.prefixParent t) ++ [(x, true)] = FreeGroup.toWord t := by
    calc
      FreeGroup.toWord (FreeGroup.prefixParent t) ++ [(x, true)]
          = (FreeGroup.toWord t).dropLast ++ [(x, true)] := by rw [FreeGroup.toWord_prefixParent]
      _ = FreeGroup.toWord t := by
        have ht' := ht.symm
        rw [hlast] at ht'
        exact ht'
  have hred : FreeGroup.IsReduced (FreeGroup.toWord (FreeGroup.prefixParent t) ++ [(x, true)]) := by
    rw [hword]
    exact FreeGroup.isReduced_toWord (x := t)
  exact hred.reduce_eq.trans hword

theorem FreeGroup.prefixParent_mul_mk_singleton_of_last {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (y : X × Bool) (hw : FreeGroup.toWord t ≠ [])
    (hlast : (FreeGroup.toWord t).getLast hw = y) :
    FreeGroup.prefixParent t * FreeGroup.mk [y] = t := by
  apply FreeGroup.toWord_injective
  rw [FreeGroup.toWord_mul, FreeGroup.toWord_prefixParent, FreeGroup.toWord_mk]
  have ht :
      FreeGroup.toWord t =
        (FreeGroup.toWord t).dropLast ++ [(FreeGroup.toWord t).getLast hw] := by
    simpa using (List.dropLast_append_getLast hw).symm
  have hword : (FreeGroup.toWord t).dropLast ++ [y] = FreeGroup.toWord t := by
    have ht' := ht.symm
    rw [hlast] at ht'
    exact ht'
  have hred : FreeGroup.IsReduced ((FreeGroup.toWord t).dropLast ++ [y]) := by
    rw [hword]
    exact FreeGroup.isReduced_toWord (x := t)
  exact hred.reduce_eq.trans hword

theorem FreeGroup.prefixParent_mul_lastLetter {X : Type u} [DecidableEq X]
    {t : FreeGroup X} {y : SignedLetter X}
    (h : FreeGroup.lastLetter? t = some y) :
    FreeGroup.prefixParent t * FreeGroup.mk [y] = t := by
  rcases (FreeGroup.lastLetter?_eq_some_iff (g := t) (y := y)).1 h with
    ⟨hw, hlast⟩
  exact FreeGroup.prefixParent_mul_mk_singleton_of_last t y hw hlast

end Internal.FreeGroupWord

/-- The parent edge data obtained by deleting the last signed letter of a nontrivial word. -/
structure FreeGroup.PrefixParentEdge {X : Type u} [DecidableEq X] (t : FreeGroup X) where
  parent : FreeGroup X
  letter : SignedLetter X
  parent_eq : parent = FreeGroup.prefixParent t
  rebuild : parent * FreeGroup.mk [letter] = t

/-- A nontrivial reduced word has a canonical parent edge. -/
def FreeGroup.prefixParentEdgeOfNeOne {X : Type u} [DecidableEq X]
    {t : FreeGroup X} (ht : t ≠ 1) : FreeGroup.PrefixParentEdge t := by
  have hw : FreeGroup.toWord t ≠ [] := by
    exact mt (FreeGroup.toWord_eq_nil_iff.mp) ht
  refine
    { parent := FreeGroup.prefixParent t
      letter := (FreeGroup.toWord t).getLast hw
      parent_eq := rfl
      rebuild := ?_ }
  exact Internal.FreeGroupWord.FreeGroup.prefixParent_mul_mk_singleton_of_last t
    ((FreeGroup.toWord t).getLast hw) hw rfl

@[simp] theorem FreeGroup.prefixParentEdgeOfNeOne_parent {X : Type u} [DecidableEq X]
    {t : FreeGroup X} (ht : t ≠ 1) :
    (FreeGroup.prefixParentEdgeOfNeOne (X := X) ht).parent =
      FreeGroup.prefixParent t :=
  rfl

theorem FreeGroup.prefixParentEdgeOfNeOne_lastLetter? {X : Type u} [DecidableEq X]
    {t : FreeGroup X} (ht : t ≠ 1) :
    FreeGroup.lastLetter? t =
      some (FreeGroup.prefixParentEdgeOfNeOne (X := X) ht).letter := by
  have hw : FreeGroup.toWord t ≠ [] := by
    exact mt (FreeGroup.toWord_eq_nil_iff.mp) ht
  simp only [lastLetter?, List.getLast?_eq_getLast_of_ne_nil hw, prefixParentEdgeOfNeOne]

/-- Nontrivial words decompose as parent times their last signed letter. -/
theorem FreeGroup.exists_prefixParent_mul_lastLetter_of_ne_one
    {X : Type u} [DecidableEq X] {t : FreeGroup X} (ht : t ≠ 1) :
    ∃ y : SignedLetter X,
      FreeGroup.lastLetter? t = some y ∧
        FreeGroup.prefixParent t * FreeGroup.mk [y] = t := by
  have hw : FreeGroup.toWord t ≠ [] := by
    exact mt (FreeGroup.toWord_eq_nil_iff.mp) ht
  refine ⟨(FreeGroup.toWord t).getLast hw, ?_, ?_⟩
  · rw [FreeGroup.lastLetter?, List.getLast?_eq_getLast_of_ne_nil hw]
  · exact Internal.FreeGroupWord.FreeGroup.prefixParent_mul_mk_singleton_of_last t
      ((FreeGroup.toWord t).getLast hw) hw rfl

theorem FreeGroup.lastLetter_cases_of_ne_one {X : Type u} [DecidableEq X]
    {t : FreeGroup X} (ht : t ≠ 1) :
    ∃ x : X,
      (∃ hw : FreeGroup.toWord t ≠ [],
          (FreeGroup.toWord t).getLast hw = (x, true) ∧
            FreeGroup.prefixParent t * FreeGroup.of x = t) ∨
      (∃ hw : FreeGroup.toWord t ≠ [],
          (FreeGroup.toWord t).getLast hw = (x, false) ∧
            t * FreeGroup.of x = FreeGroup.prefixParent t) := by
  have hw : FreeGroup.toWord t ≠ [] := by
    exact mt (FreeGroup.toWord_eq_nil_iff.mp) ht
  rcases hlast : (FreeGroup.toWord t).getLast hw with ⟨x, b⟩
  cases b with
  | false =>
      refine ⟨x, Or.inr ⟨hw, hlast, ?_⟩⟩
      simpa [FreeGroup.prefixParent] using
        Internal.FreeGroupWord.FreeGroup.mul_of_of_eq_mk_dropLast_of_cancels t x hw hlast
  | true =>
      refine ⟨x, Or.inl ⟨hw, hlast, ?_⟩⟩
      exact Internal.FreeGroupWord.FreeGroup.prefixParent_mul_of_of_last_pos t x hw hlast

namespace Internal.FreeGroupWord

theorem FreeGroup.mul_of_eq_prefixParent_of_cancels {X : Type u} [DecidableEq X]
    (t : FreeGroup X) (x : X) (hw : FreeGroup.toWord t ≠ [])
    (hlast : (FreeGroup.toWord t).getLast hw = (x, false)) :
    t * FreeGroup.of x = FreeGroup.prefixParent t := by
  simpa [FreeGroup.prefixParent] using
    FreeGroup.mul_of_of_eq_mk_dropLast_of_cancels t x hw hlast

end Internal.FreeGroupWord

end ReidemeisterSchreier
