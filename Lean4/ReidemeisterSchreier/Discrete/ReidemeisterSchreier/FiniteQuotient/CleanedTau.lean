import ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.CleanedSymbols

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/ReidemeisterSchreier/FiniteQuotient/CleanedTau.lean
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

/-- List-word form of Schreier rewriting after deleting degenerate finite
Schreier generators.  This is the computational API for concrete finite
examples. -/
def cleanedTauList
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    FreeGroup D.NondegenerateSchreierSymbol :=
  D.deleteDegenerateSchreierGeneratorHom (D.tauList q xs)

omit [DecidableEq X] in
@[simp]
theorem cleanedTauList_nil
    [DecidablePred D.IsDegenerateSchreierSymbol] (q : Q) :
    D.cleanedTauList q [] = 1 := by
  simp only [cleanedTauList, tauList, map_one]

omit [DecidableEq X] in
@[simp]
theorem cleanedTauList_cons_true
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (x : X) (xs : List (X × Bool)) :
    D.cleanedTauList q ((x, true) :: xs) =
      D.cleanedSchreierSymbolWord (q, x) *
        D.cleanedTauList (D.transition q x) xs := by
  simp only [cleanedTauList, tauList, transition_eq, map_mul, deleteDegenerateSchreierGeneratorHom_of]

omit [DecidableEq X] in
@[simp]
theorem cleanedTauList_cons_false
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (x : X) (xs : List (X × Bool)) :
    D.cleanedTauList q ((x, false) :: xs) =
      (D.cleanedSchreierSymbolWord (D.inverseTransition q x, x))⁻¹ *
        D.cleanedTauList (D.inverseTransition q x) xs := by
  simp only [cleanedTauList, tauList, inverseTransition_eq, map_mul, map_inv,
  deleteDegenerateSchreierGeneratorHom_of]

omit [DecidableEq X] in
theorem cleanedTauList_append
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (xs ys : List (X × Bool)) :
    D.cleanedTauList q (xs ++ ys) =
      D.cleanedTauList q xs *
        D.cleanedTauList
          (D.quotientMap (D.quotientSection q * FreeGroup.mk xs)) ys := by
  simp only [cleanedTauList, D.tauList_append, map_mul, quotientMap_quotientSection_apply]

omit [DecidableEq X] in
theorem cleanedTauList_red
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) {xs ys : List (X × Bool)}
    (h : FreeGroup.Red xs ys) :
    D.cleanedTauList q xs = D.cleanedTauList q ys := by
  simp only [cleanedTauList, D.tauList_red q h]

omit [DecidableEq X] in
theorem cleanedTauList_eq_of_mk_eq
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) {xs ys : List (X × Bool)}
    (h : FreeGroup.mk xs = FreeGroup.mk ys) :
    D.cleanedTauList q xs = D.cleanedTauList q ys := by
  simp only [cleanedTauList, D.tauList_eq_of_mk_eq q h]

/-- Schreier rewriting after deleting degenerate finite Schreier generators. -/
def cleanedTau
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    FreeGroup D.NondegenerateSchreierSymbol :=
  D.deleteDegenerateSchreierGeneratorHom (D.tau q w)

theorem cleanedTau_eq_cleanedTauList_toWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    D.cleanedTau q w = D.cleanedTauList q w.toWord :=
  rfl

theorem cleanedTau_mk
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    D.cleanedTau q (FreeGroup.mk xs) = D.cleanedTauList q xs := by
  simp only [cleanedTau, D.tau_mk, cleanedTauList]

/-- Reduced list-word normal form of `cleanedTau q w`.  This is the
computation-facing output of the cleaned finite Reidemeister-Schreier rewriting
map. -/
noncomputable def cleanedTauNormalWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    List (D.NondegenerateSchreierSymbol × Bool) :=
  (D.cleanedTau q w).toWord

/-- Reduced list-word normal form of `cleanedTauList q xs`. -/
noncomputable def cleanedTauListNormalWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    List (D.NondegenerateSchreierSymbol × Bool) :=
  (D.cleanedTauList q xs).toWord

theorem mk_cleanedTauNormalWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    FreeGroup.mk (D.cleanedTauNormalWord q w) = D.cleanedTau q w := by
  simpa [cleanedTauNormalWord] using
    (FreeGroup.mk_toWord (x := D.cleanedTau q w))

omit [DecidableEq X] in
theorem mk_cleanedTauListNormalWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    FreeGroup.mk (D.cleanedTauListNormalWord q xs) =
      D.cleanedTauList q xs := by
  simpa [cleanedTauListNormalWord] using
    (FreeGroup.mk_toWord (x := D.cleanedTauList q xs))

theorem cleanedTauNormalWord_mk
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool)) :
    D.cleanedTauNormalWord q (FreeGroup.mk xs) =
      D.cleanedTauListNormalWord q xs := by
  simp only [cleanedTauNormalWord, D.cleanedTau_mk, cleanedTauListNormalWord]

theorem cleanedTau_eq_mk_iff_cleanedTauNormalWord_eq_reduce
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X)
    (ys : List (D.NondegenerateSchreierSymbol × Bool)) :
    D.cleanedTau q w = FreeGroup.mk ys ↔
      D.cleanedTauNormalWord q w = FreeGroup.reduce ys := by
  unfold cleanedTauNormalWord
  rw [← FreeGroup.toWord_inj]
  constructor
  · intro h
    exact h
  · intro h
    exact h

omit [DecidableEq X] in
theorem cleanedTauList_eq_mk_iff_cleanedTauListNormalWord_eq_reduce
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    (q : Q) (xs : List (X × Bool))
    (ys : List (D.NondegenerateSchreierSymbol × Bool)) :
    D.cleanedTauList q xs = FreeGroup.mk ys ↔
      D.cleanedTauListNormalWord q xs = FreeGroup.reduce ys := by
  unfold cleanedTauListNormalWord
  rw [← FreeGroup.toWord_inj]
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem targetLift_cleanedTau_eq_mk_of_substitutionWord_reduce_eq
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {toTargetGenerator : D.NondegenerateSchreierSymbol → FreeGroup Y}
    (q : Q) (w : FreeGroup X) {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce
          (freeGroupSubstitutionWord toTargetGenerator
            (D.cleanedTauNormalWord q w)) =
        FreeGroup.reduce ys) :
    FreeGroup.lift toTargetGenerator (D.cleanedTau q w) =
      FreeGroup.mk ys := by
  rw [← D.mk_cleanedTauNormalWord q w]
  exact freeGroup_lift_mk_eq_mk_of_substitutionWord_reduce_eq h

theorem targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_eq
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.NondegenerateSchreierSymbol → FreeGroup Y}
    (q : Q) (w : FreeGroup X) {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce
          (freeGroupSubstitutionWord toTargetGenerator
            (D.cleanedTauNormalWord q w)) =
        FreeGroup.reduce ys)
    (hy : RelatorEquivalent S (FreeGroup.mk ys) 1) :
    RelatorEquivalent S
      (FreeGroup.lift toTargetGenerator (D.cleanedTau q w)) 1 :=
  (RelatorEquivalent.of_eq
    (D.targetLift_cleanedTau_eq_mk_of_substitutionWord_reduce_eq
      (toTargetGenerator := toTargetGenerator) q w h)).trans hy

theorem targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_mem
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.NondegenerateSchreierSymbol → FreeGroup Y}
    (q : Q) (w : FreeGroup X) {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce
          (freeGroupSubstitutionWord toTargetGenerator
            (D.cleanedTauNormalWord q w)) =
        FreeGroup.reduce ys)
    (hy : FreeGroup.mk ys ∈ S) :
    RelatorEquivalent S
      (FreeGroup.lift toTargetGenerator (D.cleanedTau q w)) 1 :=
  D.targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_eq
    (toTargetGenerator := toTargetGenerator) q w h
    (RelatorEquivalent.of_mem hy)

theorem mapsCleanedRelators_of_cleanedTauNormalWord_reduce
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.NondegenerateSchreierSymbol → FreeGroup Y}
    (targetWord : Q → FreeGroup X → List (Y × Bool))
    (hword :
      ∀ q : Q, ∀ r ∈ R,
        FreeGroup.reduce
            (freeGroupSubstitutionWord toTargetGenerator
              (D.cleanedTauNormalWord q r)) =
          FreeGroup.reduce (targetWord q r))
    (hrel :
      ∀ q : Q, ∀ r ∈ R,
        RelatorEquivalent S (FreeGroup.mk (targetWord q r)) 1) :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent S
        (FreeGroup.lift toTargetGenerator (D.cleanedTau q r)) 1 := by
  intro q r hr
  exact
    D.targetLift_cleanedTau_relatorEquivalent_one_of_substitutionWord_reduce_eq
      (toTargetGenerator := toTargetGenerator) q r (hword q r hr)
      (hrel q r hr)

theorem mapsCleanedRelators_of_cleanedTauNormalWord_reduce_mem
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq D.NondegenerateSchreierSymbol]
    {Y : Type*} [DecidableEq Y]
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    {toTargetGenerator : D.NondegenerateSchreierSymbol → FreeGroup Y}
    (targetWord : Q → FreeGroup X → List (Y × Bool))
    (hword :
      ∀ q : Q, ∀ r ∈ R,
        FreeGroup.reduce
            (freeGroupSubstitutionWord toTargetGenerator
              (D.cleanedTauNormalWord q r)) =
          FreeGroup.reduce (targetWord q r))
    (hmem :
      ∀ q : Q, ∀ r ∈ R, FreeGroup.mk (targetWord q r) ∈ S) :
    ∀ q : Q, ∀ r ∈ R,
      RelatorEquivalent S
        (FreeGroup.lift toTargetGenerator (D.cleanedTau q r)) 1 :=
  D.mapsCleanedRelators_of_cleanedTauNormalWord_reduce targetWord hword
    (fun q r hr => RelatorEquivalent.of_mem (hmem q r hr))

@[simp]
theorem cleanedTau_one
    [DecidablePred D.IsDegenerateSchreierSymbol] (q : Q) :
    D.cleanedTau q 1 = 1 := by
  simp only [cleanedTau, tau_one, map_one]

theorem cleanedTau_mul
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (u v : FreeGroup X) :
    D.cleanedTau q (u * v) =
      D.cleanedTau q u *
        D.cleanedTau (D.quotientMap (D.quotientSection q * u)) v := by
  simp only [cleanedTau, D.tau_mul, map_mul, quotientMap_quotientSection_apply]

theorem cleanedTau_mul_of_mem_kernel
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {u : FreeGroup X} (hu : u ∈ D.kernel) (v : FreeGroup X) :
    D.cleanedTau 1 (u * v) = D.cleanedTau 1 u * D.cleanedTau 1 v := by
  have h := D.tau_mul_of_mem_kernel (u := u) (v := v) hu
  simp only [cleanedTau, h, map_mul]

theorem cleanedTau_inv
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (u : FreeGroup X) :
    D.cleanedTau (D.quotientMap (D.quotientSection q * u)) u⁻¹ =
      (D.cleanedTau q u)⁻¹ := by
  unfold cleanedTau
  rw [D.tau_inv]
  simp only [map_inv]

theorem cleanedTau_inv_of_mem_kernel
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {u : FreeGroup X} (hu : u ∈ D.kernel) :
    D.cleanedTau 1 u⁻¹ = (D.cleanedTau 1 u)⁻¹ := by
  have h := D.tau_inv_of_mem_kernel (u := u) hu
  simp only [cleanedTau, h, map_inv]

theorem nondegenerateSymbolEvalHom_cleanedTau
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) (w : FreeGroup X) :
    D.nondegenerateSymbolEvalHom (D.cleanedTau q w) =
      D.quotientSection q * w *
        (D.quotientSection
          (D.quotientMap (D.quotientSection q * w)))⁻¹ := by
  rw [cleanedTau, D.nondegenerateSymbolEvalHom_deleteDegenerateSchreierGeneratorHom]
  exact D.symbolEvalHom_tau q w

theorem cleanedTau_pow_of_mem_kernel
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {u : FreeGroup X} (hu : u ∈ D.kernel) (n : ℕ) :
    D.cleanedTau 1 (u ^ n) = (D.cleanedTau 1 u) ^ n := by
  induction n with
  | zero =>
      simp only [pow_zero, cleanedTau_one]
  | succ n ih =>
      rw [pow_succ, pow_succ]
      rw [D.cleanedTau_mul_of_mem_kernel (D.kernel.pow_mem hu n)]
      rw [ih]

theorem cleanedTau_zpow_of_mem_kernel
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {u : FreeGroup X} (hu : u ∈ D.kernel) (n : ℤ) :
    D.cleanedTau 1 (u ^ n) = (D.cleanedTau 1 u) ^ n := by
  cases n with
  | ofNat n =>
      simpa using D.cleanedTau_pow_of_mem_kernel hu n
  | negSucc n =>
      have hpow := D.cleanedTau_pow_of_mem_kernel hu (n + 1)
      have hinv := D.cleanedTau_inv_of_mem_kernel (D.kernel.pow_mem hu (n + 1))
      calc
        D.cleanedTau 1 (u ^ Int.negSucc n) =
            D.cleanedTau 1 ((u ^ (n + 1))⁻¹) := by
              simp only [zpow_negSucc]
        _ = (D.cleanedTau 1 (u ^ (n + 1)))⁻¹ := hinv
        _ = ((D.cleanedTau 1 u) ^ (n + 1))⁻¹ := by rw [hpow]
        _ = (D.cleanedTau 1 u) ^ Int.negSucc n := by
              simp only [zpow_negSucc]

theorem cleanedTau_conj_of_mem_kernel
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {a u : FreeGroup X} (ha : a ∈ D.kernel) (hu : u ∈ D.kernel) :
    D.cleanedTau 1 (a * u * a⁻¹) =
      D.cleanedTau 1 a * D.cleanedTau 1 u * (D.cleanedTau 1 a)⁻¹ := by
  rw [mul_assoc]
  rw [D.cleanedTau_mul_of_mem_kernel ha (u * a⁻¹)]
  rw [D.cleanedTau_mul_of_mem_kernel hu a⁻¹]
  rw [D.cleanedTau_inv_of_mem_kernel ha]
  rw [mul_assoc]


end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete.ReidemeisterSchreier
