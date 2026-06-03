import ReidemeisterSchreier.Discrete.Presentations.Relators

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Singerman/FreeGroupWords.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Singerman/Reidemeister-Schreier bridge

Cyclic quotient actions, cyclic product identities, Schreier kernel computations, free-group word identities, and kernel transport for the compact Fuchsian proof.
-/

namespace FenchelNielsen

theorem list_ofFn_one_add {α : Type*} {n : ℕ} (f : Fin (1 + n) → α) :
    List.ofFn f =
      f ⟨0, by omega⟩ ::
        List.ofFn (fun j : Fin n => f ⟨1 + j.val, by omega⟩) := by
  rw [List.ofFn_congr (show 1 + n = n + 1 by omega)]
  rw [List.ofFn_succ]
  simp only [Fin.cast_zero, Fin.mk_zero', List.cons.injEq, List.ofFn_inj, true_and]
  funext j
  apply congrArg f
  ext
  simp only [Fin.val_cast, Fin.val_succ]
  omega

theorem list_ofFn_two_add {α : Type*} {n : ℕ} (f : Fin (2 + n) → α) :
    List.ofFn f =
      f ⟨0, by omega⟩ :: f ⟨1, by omega⟩ ::
        List.ofFn (fun j : Fin n => f ⟨2 + j.val, by omega⟩) := by
  rw [List.ofFn_congr (show 2 + n = (1 + n) + 1 by omega)]
  rw [List.ofFn_succ]
  rw [List.ofFn_congr (show 1 + n = n + 1 by omega)]
  rw [List.ofFn_succ]
  simp only [Fin.cast_zero, Fin.succ_zero_eq_one', Fin.mk_zero', List.cons.injEq,
    List.ofFn_inj, true_and]
  constructor
  · apply congrArg f
    ext
    simp only [Fin.val_cast, Fin.coe_ofNat_eq_mod, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one,
  lt_add_iff_pos_left, add_pos_iff, zero_lt_one, true_or]
  · funext j
    apply congrArg f
    ext
    simp only [Fin.val_cast, Fin.val_succ]
    omega

theorem freeGroup_of_pow_ne_one {X : Type*}
    (x : X) {n : ℕ} (hn : n ≠ 0) :
    (FreeGroup.of x : FreeGroup X) ^ n ≠ 1 := by
  classical
  intro h
  let χ : X → Multiplicative ℤ :=
    fun y => if y = x then Multiplicative.ofAdd (1 : ℤ) else 1
  have hmap := congrArg (FreeGroup.lift χ) h
  have hn0 : n = 0 := by
    simpa [χ, map_pow] using hmap
  exact hn hn0

private theorem freeGroup_isReduced_pow_mul_of_mul_pow_inv_word {X : Type*}
    {x y : X} (hxy : x ≠ y) (a b : ℕ) :
    FreeGroup.IsReduced
      (List.replicate a (x, true) ++ [(y, true)] ++ List.replicate b (x, false)) := by
  apply List.IsChain.append
  · apply List.IsChain.append
    · exact List.isChain_replicate_of_rel a (by intro _; rfl)
    · simp only [List.IsChain.singleton]
    · intro u hu v hv huv
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv
      subst v
      by_cases ha : a = 0
      · simp only [ha, List.replicate_zero, List.getLast?_nil, Option.mem_def, reduceCtorEq] at hu
      · have hlast : u = (x, true) := by
          simpa [List.getLast?_replicate, ha] using hu.symm
        subst u
        exact False.elim (hxy huv)
  · exact List.isChain_replicate_of_rel b (by intro _; rfl)
  · intro u hu v hv huv
    by_cases hb : b = 0
    · simp only [hb, List.replicate_zero, List.head?_nil, Option.mem_def, reduceCtorEq] at hv
    · have hvx : v = (x, false) := by
        simpa [List.head?_replicate, hb] using hv.symm
      subst v
      have huy : u = (y, true) := by
        simpa using hu.symm
      subst u
      exact False.elim (hxy huv.symm)

theorem freeGroup_toWord_pow_mul_of_mul_pow_inv {X : Type*} [DecidableEq X]
    {x y : X} (hxy : x ≠ y) (a b : ℕ) :
    FreeGroup.toWord
        ((FreeGroup.of x : FreeGroup X) ^ a * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup X) ^ b)⁻¹) =
      List.replicate a (x, true) ++ [(y, true)] ++ List.replicate b (x, false) := by
  let L := List.replicate a (x, true) ++ [(y, true)] ++ List.replicate b (x, false)
  have hmk :
      (FreeGroup.of x : FreeGroup X) ^ a * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup X) ^ b)⁻¹ =
        FreeGroup.mk L := by
    simp only [FreeGroup.of, FreeGroup.pow_mk, List.flatten_replicate_singleton, FreeGroup.mul_mk,
  FreeGroup.inv_mk, FreeGroup.invRev, List.map_replicate, Bool.not_true, List.reverse_replicate, List.append_assoc,
  List.cons_append, List.nil_append, L]
  rw [hmk, FreeGroup.toWord_mk]
  exact (freeGroup_isReduced_pow_mul_of_mul_pow_inv_word hxy a b).reduce_eq

private theorem freeGroup_pow_mul_of_mul_pow_inv_word_initialLength {X : Type*} [DecidableEq X]
    {x y : X} (hxy : x ≠ y) (a b : ℕ) :
    (List.takeWhile (fun q : X × Bool => q = (x, true))
      (List.replicate a (x, true) ++ [(y, true)] ++ List.replicate b (x, false))).length =
        a := by
  have hyx : (y, true) ≠ (x, true) := by
    intro h
    exact hxy (by cases h; rfl)
  induction a with
  | zero => simp [hyx]
  | succ a _ih => simp [List.replicate_succ, hyx]

theorem freeGroup_pow_mul_of_mul_pow_inv_left_exponent_eq_of_eq {X : Type*}
    {x y : X} (hxy : x ≠ y) {a b c d : ℕ}
    (h :
      (FreeGroup.of x : FreeGroup X) ^ a * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup X) ^ b)⁻¹ =
        (FreeGroup.of x : FreeGroup X) ^ c * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup X) ^ d)⁻¹) :
    a = c := by
  classical
  have hwords := congrArg (fun w : FreeGroup X => FreeGroup.toWord w) h
  change
    FreeGroup.toWord
        ((FreeGroup.of x : FreeGroup X) ^ a * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup X) ^ b)⁻¹) =
      FreeGroup.toWord
        ((FreeGroup.of x : FreeGroup X) ^ c * FreeGroup.of y *
          ((FreeGroup.of x : FreeGroup X) ^ d)⁻¹) at hwords
  rw [freeGroup_toWord_pow_mul_of_mul_pow_inv hxy a b,
    freeGroup_toWord_pow_mul_of_mul_pow_inv hxy c d] at hwords
  have htake := congrArg
    (fun L : List (X × Bool) =>
      (List.takeWhile (fun q : X × Bool => q = (x, true)) L).length) hwords
  change
    (List.takeWhile (fun q : X × Bool => q = (x, true))
      (List.replicate a (x, true) ++ [(y, true)] ++ List.replicate b (x, false))).length =
    (List.takeWhile (fun q : X × Bool => q = (x, true))
      (List.replicate c (x, true) ++ [(y, true)] ++ List.replicate d (x, false))).length at htake
  rw [freeGroup_pow_mul_of_mul_pow_inv_word_initialLength hxy a b,
    freeGroup_pow_mul_of_mul_pow_inv_word_initialLength hxy c d] at htake
  exact htake

end FenchelNielsen
