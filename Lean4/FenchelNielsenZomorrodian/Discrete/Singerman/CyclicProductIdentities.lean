import FenchelNielsenZomorrodian.Discrete.Singerman.FreeGroupWords

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Singerman/CyclicProductIdentities.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Singerman/Reidemeister-Schreier bridge

Cyclic quotient actions, cyclic product identities, Schreier kernel computations, free-group word identities, and kernel transport for the compact Fuchsian proof.
-/

namespace FenchelNielsen
def conjugateRangeProduct {G : Type*} [Group G] (x t : G) (n : ℕ) : G :=
  ((List.finRange n).map fun k : Fin n => x ^ (k : ℕ) * t * (x ^ (k : ℕ))⁻¹).prod
theorem MonoidHom.map_list_prod_ofFn₂
    {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) {p n : ℕ}
    (g : Fin p → Fin n → M) :
    f ((List.ofFn (fun k : Fin p => (List.ofFn (fun j : Fin n => g k j)).prod)).prod) =
      (List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin n => f (g k j))).prod)).prod := by
  rw [map_list_prod]
  rw [List.map_ofFn]
  congr
  funext k
  change f ((List.ofFn (fun j : Fin n => g k j)).prod) =
    (List.ofFn (fun j : Fin n => f (g k j))).prod
  rw [map_list_prod]
  rw [List.map_ofFn]
  rfl
theorem list_ofFn_reverse_last_desc {α : Type*} {p : ℕ} (hp : 0 < p)
    (B : Fin p → α) :
    (List.ofFn B).reverse =
      B ⟨p - 1, by omega⟩ ::
        List.ofFn (fun i : Fin (p - 1) => B ⟨p - 2 - i.val, by omega⟩) := by
  apply List.ext_get
  · simp only [List.length_reverse, List.length_ofFn, List.length_cons]
    omega
  · intro i h₁ h₂
    rw [List.get_reverse' (List.ofFn B) ⟨i, h₁⟩ (by simp only [List.length_ofFn]; omega)]
    cases i with
    | zero =>
        simp only [List.length_ofFn, tsub_zero, List.get_eq_getElem, List.getElem_ofFn, List.length_cons,
  Fin.zero_eta, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.getElem_cons_zero]
    | succ i =>
        have hleft : p - 1 - (i + 1) = p - 2 - i := by omega
        simp only [List.length_ofFn, hleft, List.get_eq_getElem, List.getElem_ofFn, List.length_cons,
  List.getElem_cons_succ]
theorem descending_block_inv_product_eq {G : Type*} [Group G] {p : ℕ} (hp : 0 < p)
    (A : G) (B : Fin p → G) :
    (B ⟨p - 1, by omega⟩ * A)⁻¹ *
        (List.ofFn (fun i : Fin (p - 1) => (B ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod =
      A⁻¹ * (List.ofFn B).prod⁻¹ := by
  have hrev := list_ofFn_reverse_last_desc hp B
  have hprod :
      (B ⟨p - 1, by omega⟩)⁻¹ *
          (List.ofFn (fun i : Fin (p - 1) => (B ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod =
        (List.ofFn B).prod⁻¹ := by
    rw [List.prod_inv_reverse]
    rw [← List.map_reverse]
    rw [hrev]
    rw [List.map_cons, List.prod_cons, List.map_ofFn]
    rfl
  calc
    (B ⟨p - 1, by omega⟩ * A)⁻¹ *
        (List.ofFn (fun i : Fin (p - 1) => (B ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod
        = A⁻¹ *
          ((B ⟨p - 1, by omega⟩)⁻¹ *
            (List.ofFn (fun i : Fin (p - 1) => (B ⟨p - 2 - i.val, by omega⟩)⁻¹)).prod) := by
          group
    _ = A⁻¹ * (List.ofFn B).prod⁻¹ := by rw [hprod]
/-- Expanding a conjugate range product over a finite list gives the corresponding block product. -/
theorem conjugateRangeProduct_list_prod_eq_blocks
    {G : Type*} [Group G] (x : G) {n : ℕ} (t : Fin n → G) (p : ℕ) :
    conjugateRangeProduct x (List.ofFn t).prod p =
      (List.ofFn (fun k : Fin p =>
        (List.ofFn (fun j : Fin n =>
          x ^ (k : ℕ) * t j * (x ^ (k : ℕ))⁻¹)).prod)).prod := by
  unfold conjugateRangeProduct
  rw [← List.ofFn_eq_map]
  congr
  funext k
  calc
    x ^ (k : ℕ) * (List.ofFn t).prod * (x ^ (k : ℕ))⁻¹ =
        (List.map (fun u => x ^ (k : ℕ) * u * (x ^ (k : ℕ))⁻¹) (List.ofFn t)).prod := by
          exact ReidemeisterSchreier.Discrete.Presentations.conjugate_list_prod (x ^ (k : ℕ)) (List.ofFn t)
    _ = (List.ofFn (fun j : Fin n => x ^ (k : ℕ) * t j * (x ^ (k : ℕ))⁻¹)).prod := by
          rw [List.map_ofFn]
          rfl
/-- Successor recursion for `conjugateRangeProduct`. -/
theorem conjugateRangeProduct_succ {G : Type*} [Group G] (x t : G) (n : ℕ) :
    conjugateRangeProduct x t (n + 1) =
      conjugateRangeProduct x t n * (x ^ n * t * (x ^ n)⁻¹) := by
  unfold conjugateRangeProduct
  rw [List.finRange_succ_last, List.map_append, List.prod_append, List.map_map]
  have hmap :
      List.map ((fun k : Fin (n + 1) => x ^ (k : ℕ) * t * (x ^ (k : ℕ))⁻¹) ∘
          Fin.castSucc) (List.finRange n) =
        List.map (fun k : Fin n => x ^ (k : ℕ) * t * (x ^ (k : ℕ))⁻¹)
          (List.finRange n) := by
    apply List.map_congr_left
    intro k _hk
    simp only [Function.comp_apply, Fin.val_castSucc]
  rw [hmap]
  simp only [List.map_cons, Fin.val_last, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
theorem pow_mul_pow_mul_conjugateRangeProduct_eq_one_of_mul_eq_one
    {G : Type*} [Group G] (x y t : G) (n : ℕ) (h : x * y * t = 1) :
    x ^ n * y ^ n * conjugateRangeProduct x t n = 1 := by
  induction n with
  | zero =>
      simp only [pow_zero, mul_one, conjugateRangeProduct, List.finRange_zero, List.map_nil, List.prod_nil]
  | succ n ih =>
      rw [conjugateRangeProduct_succ]
      have hP : conjugateRangeProduct x t n = (x ^ n * y ^ n)⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        simpa [mul_assoc] using ih
      rw [hP, pow_succ x n, pow_succ y n]
      calc
        (x ^ n * x) * (y ^ n * y) *
            ((x ^ n * y ^ n)⁻¹ * (x ^ n * t * (x ^ n)⁻¹))
            = x ^ n * (x * y * t) * (x ^ n)⁻¹ := by group
        _ = 1 := by simp only [h, mul_one, mul_inv_cancel]
/-- Block-product form of `pow_mul_pow_mul_conjugateRangeProduct_eq_one_of_mul_eq_one`. -/
theorem pow_mul_pow_mul_conjugateBlockProduct_eq_one_of_mul_eq_one
    {G : Type*} [Group G] (x y : G) {n : ℕ} (t : Fin n → G) (p : ℕ)
    (h : x * y * (List.ofFn t).prod = 1) :
    x ^ p * y ^ p *
        (List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin n =>
            x ^ (k : ℕ) * t j * (x ^ (k : ℕ))⁻¹)).prod)).prod = 1 := by
  rw [← conjugateRangeProduct_list_prod_eq_blocks]
  exact pow_mul_pow_mul_conjugateRangeProduct_eq_one_of_mul_eq_one x y (List.ofFn t).prod p h
theorem pow_mul_pow_mul_conjugateBlockProduct_mem_normalClosure_of_mul_mem_normalClosure
    {G : Type*} [Group G] {R : Set G} (x y : G) {n : ℕ} (t : Fin n → G) (p : ℕ)
    (h : x * y * (List.ofFn t).prod ∈ Subgroup.normalClosure R) :
    x ^ p * y ^ p *
        (List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin n =>
            x ^ (k : ℕ) * t j * (x ^ (k : ℕ))⁻¹)).prod)).prod ∈
      Subgroup.normalClosure R := by
  let N : Subgroup G := Subgroup.normalClosure R
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hRel :
      q x * q y * (List.ofFn (fun j : Fin n => q (t j))).prod = 1 := by
    have hq : q (x * y * (List.ofFn t).prod) = 1 := by
      exact (QuotientGroup.eq_one_iff (N := N) (x * y * (List.ofFn t).prod)).2 h
    simpa [q, map_mul, map_list_prod] using hq
  have hBlock :
      q x ^ p * q y ^ p *
          (List.ofFn (fun k : Fin p =>
            (List.ofFn (fun j : Fin n =>
              q x ^ (k : ℕ) * q (t j) * (q x ^ (k : ℕ))⁻¹)).prod)).prod = 1 :=
    pow_mul_pow_mul_conjugateBlockProduct_eq_one_of_mul_eq_one
      (q x) (q y) (fun j : Fin n => q (t j)) p hRel
  have hqTarget :
      q
        (x ^ p * y ^ p *
          (List.ofFn (fun k : Fin p =>
            (List.ofFn (fun j : Fin n =>
              x ^ (k : ℕ) * t j * (x ^ (k : ℕ))⁻¹)).prod)).prod) = 1 := by
    calc
      q
          (x ^ p * y ^ p *
            (List.ofFn (fun k : Fin p =>
              (List.ofFn (fun j : Fin n =>
                x ^ (k : ℕ) * t j * (x ^ (k : ℕ))⁻¹)).prod)).prod)
        =
          q x ^ p * q y ^ p *
            (List.ofFn (fun k : Fin p =>
              q ((List.ofFn (fun j : Fin n =>
                x ^ (k : ℕ) * t j * (x ^ (k : ℕ))⁻¹)).prod))).prod := by
            rw [map_mul, map_mul, map_pow, map_pow, map_list_prod]
            rw [List.map_ofFn]
            rfl
      _ =
          q x ^ p * q y ^ p *
            (List.ofFn (fun k : Fin p =>
              (List.ofFn (fun j : Fin n =>
                q x ^ (k : ℕ) * q (t j) * (q x ^ (k : ℕ))⁻¹)).prod)).prod := by
            congr
            funext k
            rw [map_list_prod]
            rw [List.map_ofFn]
            apply congrArg List.prod
            rw [List.ofFn_inj]
            funext j
            simp only [QuotientGroup.coe_mk', Function.comp_apply, QuotientGroup.mk_mul, QuotientGroup.mk_pow,
  QuotientGroup.mk_inv, QuotientGroup.mk'_apply, q]
      _ = 1 := hBlock
  exact
    (QuotientGroup.eq_one_iff (N := N)
      (x ^ p * y ^ p *
        (List.ofFn (fun k : Fin p =>
          (List.ofFn (fun j : Fin n =>
            x ^ (k : ℕ) * t j * (x ^ (k : ℕ))⁻¹)).prod)).prod)).1 hqTarget
def negOneCycleTailProduct {G : Type*} [Group G] (x y : G) (n : ℕ) : G :=
  (List.ofFn (fun i : Fin n =>
    x ^ (n - i.val) * y * (x ^ (n - 1 - i.val))⁻¹)).prod
/-- Successor recursion for `negOneCycleTailProduct`. -/
theorem negOneCycleTailProduct_succ {G : Type*} [Group G] (x y : G) (n : ℕ) :
    negOneCycleTailProduct x y (n + 1) =
      x ^ (n + 1) * y * (x ^ n)⁻¹ * negOneCycleTailProduct x y n := by
  unfold negOneCycleTailProduct
  rw [List.ofFn_succ, List.prod_cons]
  simp only [Fin.val_zero, tsub_zero, Nat.add_sub_cancel_right]
  congr 1
  apply congrArg List.prod
  rw [List.ofFn_inj]
  funext i
  have hi : i.val < n := i.isLt
  have hsub : n - (i.val + 1) = n - 1 - i.val := by omega
  simp only [Fin.val_succ, Nat.reduceSubDiff, hsub]
/-- Closed form for `negOneCycleTailProduct`. -/
theorem negOneCycleTailProduct_eq {G : Type*} [Group G] (x y : G) (n : ℕ) :
    negOneCycleTailProduct x y n = x ^ n * y ^ n := by
  induction n with
  | zero =>
      simp only [negOneCycleTailProduct, zero_tsub, pow_zero, one_mul, inv_one, mul_one, List.ofFn_zero,
  List.prod_nil]
  | succ n ih =>
      rw [negOneCycleTailProduct_succ, ih]
      rw [pow_succ]
      group
theorem negOneCycleProduct_eq_pow {G : Type*} [Group G] (x y : G) (n : ℕ) :
    y * (x ^ n)⁻¹ * negOneCycleTailProduct x y n = y ^ (n + 1) := by
  rw [negOneCycleTailProduct_eq]
  rw [pow_succ']
  group
end FenchelNielsen
