import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.ZeroGenus.CleanupData
import FenchelNielsenZomorrodian.Discrete.Singerman.CyclicSchreierKernel

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/ZeroGenus/Reindexing.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Compact zero-genus three-step proof data

Organizes first and second reduction data, perfectness numerics, reindexing, cleanup data, and the final zero-genus three-step finite-index theorem.
-/

namespace FenchelNielsen
private theorem fin_eq_zero_elim {n : ℕ} (h : n = 0) (i : Fin n) : False := by
  exact Nat.not_lt_zero i (by simpa [h] using i.2)
private theorem fin_eq_zero_or_one_or_succ_succ_of_eq_add_two
    {m n : ℕ} (h : m = n + 2) (i : Fin m) :
    i = Fin.cast h.symm (0 : Fin (n + 2)) ∨
      i = Fin.cast h.symm (1 : Fin (n + 2)) ∨
        ∃ k : Fin n, i = Fin.cast h.symm k.succ.succ := by
  generalize hj : Fin.cast h i = j
  have hij : i = Fin.cast h.symm j := by
    rw [← hj]
    simp only [Fin.cast_cast, Fin.cast_eq_self]
  cases j using Fin.cases with
  | zero =>
      left
      exact hij
  | succ j =>
      cases j using Fin.cases with
      | zero =>
          right
          left
          exact hij
      | succ k =>
          right
          right
          exact ⟨k, hij⟩
private theorem fin_eq_prefix_or_zero_or_one_or_tail_of_eq_add_two
    {m k n : ℕ} (h : m = k + (n + 2)) (i : Fin m) :
    (∃ j : Fin k, i = Fin.cast h.symm (Fin.castAdd (n + 2) j)) ∨
      i = Fin.cast h.symm (Fin.natAdd k (0 : Fin (n + 2))) ∨
        i = Fin.cast h.symm (Fin.natAdd k (1 : Fin (n + 2))) ∨
          ∃ t : Fin n, i = Fin.cast h.symm (Fin.natAdd k t.succ.succ) := by
  generalize hj : Fin.cast h i = j
  have hij : i = Fin.cast h.symm j := by
    rw [← hj]
    simp only [Fin.cast_cast, Fin.cast_eq_self]
  cases j using Fin.addCases with
  | left j =>
      left
      exact ⟨j, hij⟩
  | right j =>
      rcases fin_eq_zero_or_one_or_succ_succ_of_eq_add_two rfl j with rfl | rfl | ⟨t, rfl⟩
      · right
        left
        exact hij
      · right
        right
        left
        exact hij
      · right
        right
        right
        exact ⟨t, hij⟩
private theorem List.map_finRange_fin_cast {α : Type*} {m n : ℕ} (h : m = n)
    (f : Fin n → α) :
    (List.finRange m).map (fun i => f (Fin.cast h i)) = (List.finRange n).map f := by
  cases h
  rfl
private noncomputable def zeroGenusOrderedGeneratorEquiv
    (σ τ : FuchsianSignature)
    (hσZero : σ.orbitGenus = 0) (hτZero : τ.orbitGenus = 0)
    (hNum : σ.numPeriods = τ.numPeriods) :
    FuchsianGenerator σ ≃ FuchsianGenerator τ where
  toFun
    | .elliptic i => .elliptic (Fin.cast hNum i)
    | .surfaceA j => False.elim (fin_eq_zero_elim hσZero j)
    | .surfaceB j => False.elim (fin_eq_zero_elim hσZero j)
  invFun
    | .elliptic i => .elliptic (Fin.cast hNum.symm i)
    | .surfaceA j => False.elim (fin_eq_zero_elim hτZero j)
    | .surfaceB j => False.elim (fin_eq_zero_elim hτZero j)
  left_inv := by
    intro x
    cases x with
    | elliptic i => simp
    | surfaceA j => exact False.elim (fin_eq_zero_elim hσZero j)
    | surfaceB j => exact False.elim (fin_eq_zero_elim hσZero j)
  right_inv := by
    intro x
    cases x with
    | elliptic i => simp
    | surfaceA j => exact False.elim (fin_eq_zero_elim hτZero j)
    | surfaceB j => exact False.elim (fin_eq_zero_elim hτZero j)
private theorem zeroGenusOrderedGeneratorEquiv_totalRelation
    (σ τ : FuchsianSignature)
    (hσZero : σ.orbitGenus = 0) (hτZero : τ.orbitGenus = 0)
    (hNum : σ.numPeriods = τ.numPeriods) :
    FreeGroup.freeGroupCongr
        (zeroGenusOrderedGeneratorEquiv σ τ hσZero hτZero hNum)
        (totalRelation σ) =
      totalRelation τ := by
  let eGen := zeroGenusOrderedGeneratorEquiv σ τ hσZero hτZero hNum
  have hEll :
      (List.map
          (fun i : Fin σ.numPeriods =>
            xWord τ (Fin.cast hNum i))
          (List.finRange σ.numPeriods)).prod =
        (List.map (fun i : Fin τ.numPeriods => xWord τ i)
          (List.finRange τ.numPeriods)).prod := by
    rw [List.map_finRange_fin_cast hNum (fun i : Fin τ.numPeriods => xWord τ i)]
  rw [totalRelation, map_mul, map_list_prod, map_list_prod, List.map_map, List.map_map]
  have hEllMap :
      ((fun x : FreeGroup (FuchsianGenerator σ) => FreeGroup.freeGroupCongr eGen x) ∘
          (fun i : Fin σ.numPeriods => xWord σ i)) =
        fun i : Fin σ.numPeriods => xWord τ (Fin.cast hNum i) := by
    funext i
    simp only [zeroGenusOrderedGeneratorEquiv, FreeGroup.freeGroupCongr_apply, Equiv.coe_fn_mk, xWord,
  Function.comp_apply, FreeGroup.map.of, eGen]
  rw [hEllMap, hEll]
  have hSurfaceRangeSource :
      (List.finRange σ.orbitGenus : List (Fin σ.orbitGenus)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro j _hj
    exact fin_eq_zero_elim hσZero j
  have hSurfaceRangeTarget :
      (List.finRange τ.orbitGenus : List (Fin τ.orbitGenus)) = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro j _hj
    exact fin_eq_zero_elim hτZero j
  have hSurfaceSource :
      (List.map
          ((fun x : FreeGroup (FuchsianGenerator σ) => FreeGroup.freeGroupCongr eGen x) ∘
            fun j : Fin σ.orbitGenus => ⁅aWord σ j, bWord σ j⁆)
          (List.finRange σ.orbitGenus)).prod = 1 := by
    rw [hSurfaceRangeSource]
    simp only [FreeGroup.freeGroupCongr_apply, List.map_nil, List.prod_nil]
  have hSurfaceTarget :
      (List.map (fun j : Fin τ.orbitGenus => ⁅aWord τ j, bWord τ j⁆)
          (List.finRange τ.orbitGenus)).prod = 1 := by
    rw [hSurfaceRangeTarget]
    simp only [List.map_nil, List.prod_nil]
  rw [totalRelation, hSurfaceSource, hSurfaceTarget]
private theorem zeroGenusFuchsianPresentedGroupEquivOfOrderedPeriods
    (σ τ : FuchsianSignature)
    (hσZero : σ.orbitGenus = 0) (hτZero : τ.orbitGenus = 0)
    (hNum : σ.numPeriods = τ.numPeriods)
    (hPeriods : ∀ i, σ.periods i = τ.periods (Fin.cast hNum i)) :
    Nonempty (FuchsianPresentedGroup σ ≃* FuchsianPresentedGroup τ) := by
  classical
  let eGen := zeroGenusOrderedGeneratorEquiv σ τ hσZero hτZero hNum
  have hRelators :
      FreeGroup.freeGroupCongr eGen '' relators σ = relators τ := by
    ext w
    constructor
    · rintro ⟨r, hr, rfl⟩
      rcases hr with ⟨i, rfl⟩ | rfl
      · left
        refine ⟨Fin.cast hNum i, ?_⟩
        simp only [zeroGenusOrderedGeneratorEquiv, xWord, hPeriods i, FreeGroup.freeGroupCongr_apply, Equiv.coe_fn_mk,
  map_pow, FreeGroup.map.of, eGen]
      · right
        simpa [eGen] using
          zeroGenusOrderedGeneratorEquiv_totalRelation σ τ hσZero hτZero hNum
    · intro hw
      rcases hw with ⟨i, rfl⟩ | rfl
      · refine ⟨(xWord σ (Fin.cast hNum.symm i)) ^ σ.periods (Fin.cast hNum.symm i),
          Or.inl ⟨Fin.cast hNum.symm i, rfl⟩, ?_⟩
        have hperiod := hPeriods (Fin.cast hNum.symm i)
        simp only [zeroGenusOrderedGeneratorEquiv, xWord, hperiod, Fin.cast_cast, Fin.cast_eq_self,
  FreeGroup.freeGroupCongr_apply, Equiv.coe_fn_mk, map_pow, FreeGroup.map.of, eGen]
      · refine ⟨totalRelation σ, Or.inr rfl, ?_⟩
        simpa [eGen] using
          zeroGenusOrderedGeneratorEquiv_totalRelation σ τ hσZero hτZero hNum
  exact
    ⟨(PresentedGroup.equivPresentedGroup (relators σ) eGen).trans
      (QuotientGroup.quotientMulEquivOfEq (by rw [hRelators]))⟩
theorem conjugate_mem_normalClosure_of_mem
    {G : Type*} [Group G] {R : Set G} {r g : G}
    (h : r ∈ R) :
    g * r * g⁻¹ ∈ Subgroup.normalClosure R := by
  let N : Subgroup G := Subgroup.normalClosure R
  have hr : r ∈ N := Subgroup.subset_normalClosure h
  simpa [N, MulAut.conj_apply] using
    (Subgroup.normalClosure_normal.conj_mem r hr g)
theorem conjugate_pow_mem_normalClosure_of_pow_mem
    {G : Type*} [Group G] {R : Set G} {x g : G} {n : ℕ}
    (h : x ^ n ∈ R) :
    (g * x * g⁻¹) ^ n ∈ Subgroup.normalClosure R := by
  rw [conj_pow]
  exact conjugate_mem_normalClosure_of_mem h
private theorem image_powerRelator_mem_normalClosure_of_conjugate_xWord
    (σ τ : FuchsianSignature)
    (η : FreeGroup (FuchsianGenerator σ) →* FreeGroup (FuchsianGenerator τ))
    (i : Fin σ.numPeriods) (j : Fin τ.numPeriods)
    (g : FreeGroup (FuchsianGenerator τ))
    (hImage : η (xWord σ i) = g * xWord τ j * g⁻¹)
    (hPeriod : σ.periods i = τ.periods j) :
    η ((xWord σ i) ^ σ.periods i) ∈ Subgroup.normalClosure (relators τ) := by
  rw [map_pow, hImage, hPeriod]
  exact conjugate_pow_mem_normalClosure_of_pow_mem
    (G := FreeGroup (FuchsianGenerator τ)) (R := relators τ)
    (x := xWord τ j) (g := g) (n := τ.periods j)
    (Or.inl ⟨j, rfl⟩)
private theorem image_totalRelation_mem_normalClosure_of_eq
    (σ τ : FuchsianSignature)
    (η : FreeGroup (FuchsianGenerator σ) →* FreeGroup (FuchsianGenerator τ))
    (hImage : η (totalRelation σ) = totalRelation τ) :
    η (totalRelation σ) ∈ Subgroup.normalClosure (relators τ) := by
  rw [hImage]
  exact Subgroup.subset_normalClosure (Or.inr rfl)
private theorem freeGroup_hom_mul_inv_mem_of_generator_mul_inv
    {X G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (f g : FreeGroup X →* G)
    (hgen : ∀ x : X, f (FreeGroup.of x) * (g (FreeGroup.of x))⁻¹ ∈ N) :
    ∀ x : FreeGroup X, f x * (g x)⁻¹ ∈ N := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hq : q.comp f = q.comp g := by
    apply FreeGroup.ext_hom
    intro x
    have hx : (f (FreeGroup.of x) * (g (FreeGroup.of x))⁻¹ : G ⧸ N) = 1 :=
      (QuotientGroup.eq_one_iff _).2 (hgen x)
    have hx' : q (f (FreeGroup.of x)) * (q (g (FreeGroup.of x)))⁻¹ = 1 := by
      simpa [q] using hx
    exact mul_inv_eq_one.mp hx'
  intro x
  have hx : q (f x) = q (g x) :=
    DFunLike.congr_fun hq x
  apply (QuotientGroup.eq_one_iff (f x * (g x)⁻¹)).1
  have hxone : q (f x * (g x)⁻¹) = 1 := by
    rw [map_mul, map_inv, hx, mul_inv_cancel]
  simpa [q] using hxone
private theorem freeGroup_hom_mul_inv_mem_normalClosure_of_generator_mul_inv
    {X G : Type*} [Group G] {R : Set G}
    (f g : FreeGroup X →* G)
    (hgen :
      ∀ x : X, f (FreeGroup.of x) * (g (FreeGroup.of x))⁻¹ ∈
        Subgroup.normalClosure R) :
    ∀ x : FreeGroup X, f x * (g x)⁻¹ ∈ Subgroup.normalClosure R :=
  freeGroup_hom_mul_inv_mem_of_generator_mul_inv f g hgen
private theorem zeroGenusFuchsianPresentedGroupEquivOfConjugateEllipticMutualMaps_memTotal
    (σ τ : FuchsianSignature)
    (hσZero : σ.orbitGenus = 0) (hτZero : τ.orbitGenus = 0)
    (η : FreeGroup (FuchsianGenerator σ) →* FreeGroup (FuchsianGenerator τ))
    (θ : FreeGroup (FuchsianGenerator τ) →* FreeGroup (FuchsianGenerator σ))
    (ηIndex : Fin σ.numPeriods → Fin τ.numPeriods)
    (ηConj : Fin σ.numPeriods → FreeGroup (FuchsianGenerator τ))
    (hηX :
      ∀ i, η (xWord σ i) = ηConj i * xWord τ (ηIndex i) * (ηConj i)⁻¹)
    (hηPeriod : ∀ i, σ.periods i = τ.periods (ηIndex i))
    (hηTotal : η (totalRelation σ) ∈ Subgroup.normalClosure (relators τ))
    (θIndex : Fin τ.numPeriods → Fin σ.numPeriods)
    (θConj : Fin τ.numPeriods → FreeGroup (FuchsianGenerator σ))
    (hθX :
      ∀ i, θ (xWord τ i) = θConj i * xWord σ (θIndex i) * (θConj i)⁻¹)
    (hθPeriod : ∀ i, τ.periods i = σ.periods (θIndex i))
    (hθTotal : θ (totalRelation τ) ∈ Subgroup.normalClosure (relators σ))
    (hθηEll :
      ∀ i : Fin σ.numPeriods,
        θ (η (xWord σ i)) * (xWord σ i)⁻¹ ∈ Subgroup.normalClosure (relators σ))
    (hηθEll :
      ∀ i : Fin τ.numPeriods,
        η (θ (xWord τ i)) * (xWord τ i)⁻¹ ∈ Subgroup.normalClosure (relators τ)) :
    Nonempty (FuchsianPresentedGroup σ ≃* FuchsianPresentedGroup τ) := by
  refine ⟨ReidemeisterSchreier.Discrete.Presentations.quotientEquivOfRelatorsByMutualMaps
    (relators σ) (relators τ) η θ ?_ ?_ ?_ ?_⟩
  · rintro r (⟨i, rfl⟩ | rfl)
    · exact image_powerRelator_mem_normalClosure_of_conjugate_xWord
        σ τ η i (ηIndex i) (ηConj i) (hηX i) (hηPeriod i)
    · exact hηTotal
  · rintro s (⟨i, rfl⟩ | rfl)
    exact image_powerRelator_mem_normalClosure_of_conjugate_xWord
      τ σ θ i (θIndex i) (θConj i) (hθX i) (hθPeriod i)
    · exact hθTotal
  · exact freeGroup_hom_mul_inv_mem_normalClosure_of_generator_mul_inv
      (θ.comp η) (MonoidHom.id (FreeGroup (FuchsianGenerator σ))) (by
        intro x
        cases x with
        | elliptic i => simpa [xWord] using hθηEll i
        | surfaceA j => exact False.elim (fin_eq_zero_elim hσZero j)
        | surfaceB j => exact False.elim (fin_eq_zero_elim hσZero j))
  · exact freeGroup_hom_mul_inv_mem_normalClosure_of_generator_mul_inv
      (η.comp θ) (MonoidHom.id (FreeGroup (FuchsianGenerator τ))) (by
        intro y
        cases y with
        | elliptic i => simpa [xWord] using hηθEll i
        | surfaceA j => exact False.elim (fin_eq_zero_elim hτZero j)
        | surfaceB j => exact False.elim (fin_eq_zero_elim hτZero j))
private theorem zeroGenusAdjacentSwapFuchsianPresentedGroupEquiv
    {k n : ℕ} (σ τ : FuchsianSignature)
    (hσZero : σ.orbitGenus = 0) (hτZero : τ.orbitGenus = 0)
    (hσNum : σ.numPeriods = k + (n + 2)) (hτNum : τ.numPeriods = k + (n + 2))
    (hPeriodPrefix :
      ∀ j : Fin k,
        σ.periods (Fin.cast hσNum.symm (Fin.castAdd (n + 2) j)) =
          τ.periods (Fin.cast hτNum.symm (Fin.castAdd (n + 2) j)))
    (hPeriod0 :
      σ.periods (Fin.cast hσNum.symm (Fin.natAdd k (0 : Fin (n + 2)))) =
        τ.periods (Fin.cast hτNum.symm (Fin.natAdd k (1 : Fin (n + 2)))))
    (hPeriod1 :
      σ.periods (Fin.cast hσNum.symm (Fin.natAdd k (1 : Fin (n + 2)))) =
        τ.periods (Fin.cast hτNum.symm (Fin.natAdd k (0 : Fin (n + 2)))))
    (hPeriodTail :
      ∀ t : Fin n,
        σ.periods (Fin.cast hσNum.symm (Fin.natAdd k t.succ.succ)) =
          τ.periods (Fin.cast hτNum.symm (Fin.natAdd k t.succ.succ))) :
    Nonempty (FuchsianPresentedGroup σ ≃* FuchsianPresentedGroup τ) := by
  let σ0 : Fin σ.numPeriods := Fin.cast hσNum.symm (Fin.natAdd k (0 : Fin (n + 2)))
  let σ1 : Fin σ.numPeriods := Fin.cast hσNum.symm (Fin.natAdd k (1 : Fin (n + 2)))
  let τ0 : Fin τ.numPeriods := Fin.cast hτNum.symm (Fin.natAdd k (0 : Fin (n + 2)))
  let τ1 : Fin τ.numPeriods := Fin.cast hτNum.symm (Fin.natAdd k (1 : Fin (n + 2)))
  let sameτ : Fin σ.numPeriods → Fin τ.numPeriods := fun i =>
    Fin.cast hτNum.symm (Fin.cast hσNum i)
  let sameσ : Fin τ.numPeriods → Fin σ.numPeriods := fun i =>
    Fin.cast hσNum.symm (Fin.cast hτNum i)
  have hσ10 : σ1 ≠ σ0 := by
    intro h
    have := congrArg (fun i : Fin σ.numPeriods => (Fin.cast hσNum i).val) h
    simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.val_natAdd, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.zero_mod,
  add_zero, Nat.add_eq_left, one_ne_zero, σ1, σ0] at this
  have hτ10 : τ1 ≠ τ0 := by
    intro h
    have := congrArg (fun i : Fin τ.numPeriods => (Fin.cast hτNum i).val) h
    simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.val_natAdd, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.zero_mod,
  add_zero, Nat.add_eq_left, one_ne_zero, τ1, τ0] at this
  have hprefix_ne_zero :
      ∀ j : Fin k, (Fin.castAdd (n + 2) j : Fin (k + (n + 2))) ≠
        Fin.natAdd k (0 : Fin (n + 2)) := by
    intro j h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero] at this
    omega
  have hprefix_ne_one :
      ∀ j : Fin k, (Fin.castAdd (n + 2) j : Fin (k + (n + 2))) ≠
        Fin.natAdd k (1 : Fin (n + 2)) := by
    intro j h
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.coe_ofNat_eq_mod, Nat.one_mod] at this
    omega
  have htail_ne_zero : ∀ t : Fin n, (t.succ.succ : Fin (n + 2)) ≠ 0 := by
    intro t h
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.add_eq_zero_iff, one_ne_zero, and_false,
  and_self] at this
  have htail_ne_one : ∀ t : Fin n, (t.succ.succ : Fin (n + 2)) ≠ 1 := by
    intro t h
    have := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.add_eq_right, Nat.add_eq_zero_iff,
  one_ne_zero, and_false] at this
  let η : FreeGroup (FuchsianGenerator σ) →* FreeGroup (FuchsianGenerator τ) :=
    FreeGroup.lift fun
      | .elliptic i =>
          if i = σ0 then xWord τ τ1
          else if i = σ1 then (xWord τ τ1)⁻¹ * xWord τ τ0 * xWord τ τ1
          else xWord τ (sameτ i)
      | .surfaceA j => False.elim (fin_eq_zero_elim hσZero j)
      | .surfaceB j => False.elim (fin_eq_zero_elim hσZero j)
  let θ : FreeGroup (FuchsianGenerator τ) →* FreeGroup (FuchsianGenerator σ) :=
    FreeGroup.lift fun
      | .elliptic i =>
          if i = τ0 then xWord σ σ0 * xWord σ σ1 * (xWord σ σ0)⁻¹
          else if i = τ1 then xWord σ σ0
          else xWord σ (sameσ i)
      | .surfaceA j => False.elim (fin_eq_zero_elim hτZero j)
      | .surfaceB j => False.elim (fin_eq_zero_elim hτZero j)
  let ηIndex : Fin σ.numPeriods → Fin τ.numPeriods := fun i =>
    if i = σ0 then τ1 else if i = σ1 then τ0 else sameτ i
  let ηConj : Fin σ.numPeriods → FreeGroup (FuchsianGenerator τ) := fun i =>
    if i = σ1 then (xWord τ τ1)⁻¹ else 1
  let θIndex : Fin τ.numPeriods → Fin σ.numPeriods := fun i =>
    if i = τ0 then σ1 else if i = τ1 then σ0 else sameσ i
  let θConj : Fin τ.numPeriods → FreeGroup (FuchsianGenerator σ) := fun i =>
    if i = τ0 then xWord σ σ0 else 1
  refine zeroGenusFuchsianPresentedGroupEquivOfConjugateEllipticMutualMaps_memTotal
    σ τ hσZero hτZero η θ ηIndex ηConj ?_ ?_ ?_ θIndex θConj ?_ ?_ ?_ ?_ ?_
  · intro i
    rcases fin_eq_prefix_or_zero_or_one_or_tail_of_eq_add_two hσNum i with
      ⟨j, rfl⟩ | rfl | rfl | ⟨t, rfl⟩
    · simp only [xWord, Fin.cast_cast, FreeGroup.lift_apply_of, Fin.cast_inj, hprefix_ne_zero j, ↓reduceIte,
  hprefix_ne_one j, one_mul, inv_one, mul_one, η, σ0, σ1, sameτ, ηConj, ηIndex]
    · simp only [xWord, FreeGroup.lift_apply_of, ↓reduceIte, Fin.cast_inj, Fin.natAdd_inj, zero_ne_one, one_mul,
  inv_one, mul_one, η, σ0, σ1, ηConj, ηIndex]
    · simp only [xWord, FreeGroup.lift_apply_of, hσ10, ↓reduceIte, inv_inv, η, σ0, σ1, ηConj, ηIndex]
    · simp only [xWord, Fin.cast_cast, FreeGroup.lift_apply_of, Fin.cast_inj, Fin.natAdd_inj, htail_ne_zero t,
  ↓reduceIte, htail_ne_one t, one_mul, inv_one, mul_one, η, σ0, σ1, sameτ, ηConj, ηIndex]
  · intro i
    rcases fin_eq_prefix_or_zero_or_one_or_tail_of_eq_add_two hσNum i with
      ⟨j, rfl⟩ | rfl | rfl | ⟨t, rfl⟩
    · simpa [ηIndex, σ0, σ1, sameτ, hprefix_ne_zero j, hprefix_ne_one j] using
        hPeriodPrefix j
    · simpa [ηIndex, σ0, σ1] using hPeriod0
    · simpa [ηIndex, σ0, σ1, hσ10] using hPeriod1
    · simpa [ηIndex, σ0, σ1, sameτ, htail_ne_zero t, htail_ne_one t] using
        hPeriodTail t
  · apply image_totalRelation_mem_normalClosure_of_eq
    rw [totalRelation, map_mul, map_list_prod]
    have hSourceSurfaceRange : (List.finRange σ.orbitGenus : List (Fin σ.orbitGenus)) = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro j _hj
      exact fin_eq_zero_elim hσZero j
    have hTargetSurfaceRange : (List.finRange τ.orbitGenus : List (Fin τ.orbitGenus)) = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro j _hj
      exact fin_eq_zero_elim hτZero j
    rw [hSourceSurfaceRange]
    rw [totalRelation, hTargetSurfaceRange]
    rw [List.map_map, ← List.ofFn_eq_map]
    rw [List.ofFn_congr hσNum]
    rw [← List.ofFn_eq_map]
    rw [List.ofFn_congr hτNum]
    have hSourceList :
        List.ofFn
            (fun i : Fin (k + (n + 2)) =>
              η (xWord σ (Fin.cast hσNum.symm i))) =
          List.ofFn
              (fun j : Fin k =>
                η (xWord σ (Fin.cast hσNum.symm (Fin.castAdd (n + 2) j)))) ++
            List.ofFn
              (fun j : Fin (n + 2) =>
                η (xWord σ (Fin.cast hσNum.symm (Fin.natAdd k j)))) := by
      rw [← List.ofFn_fin_append]
      congr
      funext i
      cases i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]
    have hTargetList :
        List.ofFn
            (fun i : Fin (k + (n + 2)) =>
              xWord τ (Fin.cast hτNum.symm i)) =
          List.ofFn
              (fun j : Fin k =>
                xWord τ (Fin.cast hτNum.symm (Fin.castAdd (n + 2) j))) ++
            List.ofFn
              (fun j : Fin (n + 2) =>
                xWord τ (Fin.cast hτNum.symm (Fin.natAdd k j))) := by
      rw [← List.ofFn_fin_append]
      congr
      funext i
      cases i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]
    simp only [Function.comp_apply]
    rw [hSourceList, hTargetList]
    rw [List.ofFn_succ]
    rw [List.ofFn_succ]
    simp only [xWord, Fin.cast_cast, FreeGroup.lift_apply_of, Fin.cast_inj, hprefix_ne_zero, ↓reduceIte,
  hprefix_ne_one, Fin.succ_zero_eq_one, Fin.natAdd_inj, one_ne_zero, Fin.succ_ne_zero, htail_ne_one, List.prod_append,
  List.prod_cons, List.map_nil, List.prod_nil, map_one, mul_one, List.ofFn_succ, mul_right_inj, η, σ0, τ1, σ1, τ0,
  sameτ]
    group
  · intro i
    rcases fin_eq_prefix_or_zero_or_one_or_tail_of_eq_add_two hτNum i with
      ⟨j, rfl⟩ | rfl | rfl | ⟨t, rfl⟩
    · simp only [xWord, Fin.cast_cast, FreeGroup.lift_apply_of, Fin.cast_inj, hprefix_ne_zero j, ↓reduceIte,
  hprefix_ne_one j, one_mul, inv_one, mul_one, θ, τ0, τ1, sameσ, θConj, θIndex]
    · simp only [xWord, FreeGroup.lift_apply_of, ↓reduceIte, θ, τ0, τ1, θConj, θIndex]
    · simp only [xWord, FreeGroup.lift_apply_of, hτ10, ↓reduceIte, one_mul, inv_one, mul_one, θ, τ0, τ1, θConj,
  θIndex]
    · simp only [xWord, Fin.cast_cast, FreeGroup.lift_apply_of, Fin.cast_inj, Fin.natAdd_inj, htail_ne_zero t,
  ↓reduceIte, htail_ne_one t, one_mul, inv_one, mul_one, θ, τ0, τ1, sameσ, θConj, θIndex]
  · intro i
    rcases fin_eq_prefix_or_zero_or_one_or_tail_of_eq_add_two hτNum i with
      ⟨j, rfl⟩ | rfl | rfl | ⟨t, rfl⟩
    · simpa [θIndex, τ0, τ1, sameσ, hprefix_ne_zero j, hprefix_ne_one j] using
        (hPeriodPrefix j).symm
    · simpa [θIndex, τ0, τ1] using hPeriod1.symm
    · simpa [θIndex, τ0, τ1, hτ10] using hPeriod0.symm
    · simpa [θIndex, τ0, τ1, sameσ, htail_ne_zero t, htail_ne_one t] using
        (hPeriodTail t).symm
  · apply image_totalRelation_mem_normalClosure_of_eq
    rw [totalRelation, map_mul, map_list_prod]
    have hSourceSurfaceRange : (List.finRange τ.orbitGenus : List (Fin τ.orbitGenus)) = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro j _hj
      exact fin_eq_zero_elim hτZero j
    have hTargetSurfaceRange : (List.finRange σ.orbitGenus : List (Fin σ.orbitGenus)) = [] := by
      apply List.eq_nil_iff_forall_not_mem.2
      intro j _hj
      exact fin_eq_zero_elim hσZero j
    rw [hSourceSurfaceRange]
    rw [totalRelation, hTargetSurfaceRange]
    rw [List.map_map, ← List.ofFn_eq_map]
    rw [List.ofFn_congr hτNum]
    rw [← List.ofFn_eq_map]
    rw [List.ofFn_congr hσNum]
    have hSourceList :
        List.ofFn
            (fun i : Fin (k + (n + 2)) =>
              θ (xWord τ (Fin.cast hτNum.symm i))) =
          List.ofFn
              (fun j : Fin k =>
                θ (xWord τ (Fin.cast hτNum.symm (Fin.castAdd (n + 2) j)))) ++
            List.ofFn
              (fun j : Fin (n + 2) =>
                θ (xWord τ (Fin.cast hτNum.symm (Fin.natAdd k j)))) := by
      rw [← List.ofFn_fin_append]
      congr
      funext i
      cases i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]
    have hTargetList :
        List.ofFn
            (fun i : Fin (k + (n + 2)) =>
              xWord σ (Fin.cast hσNum.symm i)) =
          List.ofFn
              (fun j : Fin k =>
                xWord σ (Fin.cast hσNum.symm (Fin.castAdd (n + 2) j))) ++
            List.ofFn
              (fun j : Fin (n + 2) =>
                xWord σ (Fin.cast hσNum.symm (Fin.natAdd k j))) := by
      rw [← List.ofFn_fin_append]
      congr
      funext i
      cases i using Fin.addCases <;> simp only [Fin.append_left, Fin.append_right]
    simp only [Function.comp_apply]
    rw [hSourceList, hTargetList]
    rw [List.ofFn_succ]
    rw [List.ofFn_succ]
    simp only [xWord, Fin.cast_cast, FreeGroup.lift_apply_of, Fin.cast_inj, hprefix_ne_zero, ↓reduceIte,
  hprefix_ne_one, Fin.succ_zero_eq_one, Fin.natAdd_inj, one_ne_zero, Fin.succ_ne_zero, htail_ne_one, List.prod_append,
  List.prod_cons, List.map_nil, List.prod_nil, map_one, mul_one, List.ofFn_succ, mul_right_inj, θ, τ0, σ0, σ1, τ1,
  sameσ]
    group
  · intro i
    have hEq : θ (η (xWord σ i)) = xWord σ i := by
      rcases fin_eq_prefix_or_zero_or_one_or_tail_of_eq_add_two hσNum i with
        ⟨j, rfl⟩ | rfl | rfl | ⟨t, rfl⟩
      · simp only [xWord, Fin.cast_cast, FreeGroup.lift_apply_of, Fin.cast_inj, hprefix_ne_zero j, ↓reduceIte,
  hprefix_ne_one j, θ, τ0, σ0, σ1, τ1, sameσ, η, sameτ]
      · simp only [xWord, FreeGroup.lift_apply_of, ↓reduceIte, hτ10, θ, σ0, σ1, η]
      · simp only [xWord, FreeGroup.lift_apply_of, hσ10, ↓reduceIte, map_mul, map_inv, hτ10, θ, σ0, σ1, η]
        group
      · simp only [xWord, Fin.cast_cast, FreeGroup.lift_apply_of, Fin.cast_inj, Fin.natAdd_inj, htail_ne_zero t,
  ↓reduceIte, htail_ne_one t, θ, τ0, σ0, σ1, τ1, sameσ, η, sameτ]
    rw [hEq]
    simp only [mul_inv_cancel, one_mem]
  · intro i
    have hEq : η (θ (xWord τ i)) = xWord τ i := by
      rcases fin_eq_prefix_or_zero_or_one_or_tail_of_eq_add_two hτNum i with
        ⟨j, rfl⟩ | rfl | rfl | ⟨t, rfl⟩
      · simp only [xWord, Fin.cast_cast, FreeGroup.lift_apply_of, Fin.cast_inj, hprefix_ne_zero j, ↓reduceIte,
  hprefix_ne_one j, η, σ0, τ1, σ1, τ0, sameτ, θ, sameσ]
      · simp only [xWord, FreeGroup.lift_apply_of, ↓reduceIte, map_mul, hσ10, map_inv, η, τ1, τ0, θ]
        group
      · simp only [xWord, FreeGroup.lift_apply_of, hτ10, ↓reduceIte, η, τ1, τ0, θ]
      · simp only [xWord, Fin.cast_cast, FreeGroup.lift_apply_of, Fin.cast_inj, Fin.natAdd_inj, htail_ne_zero t,
  ↓reduceIte, htail_ne_one t, η, σ0, τ1, σ1, τ0, sameτ, θ, sameσ]
    rw [hEq]
    simp only [mul_inv_cancel, one_mem]
private theorem zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods_of_adjacentSwap
    (σ τ : FuchsianSignature)
    (hσZero : σ.orbitGenus = 0) (hτZero : τ.orbitGenus = 0)
    {ι : Type*}
    (eσ : ι ≃ Fin σ.numPeriods) (eτ : ι ≃ Fin τ.numPeriods)
    {k n : ℕ}
    (hσNum : σ.numPeriods = k + (n + 2)) (hτNum : τ.numPeriods = k + (n + 2))
    (hAdjacent :
      let σ0 : Fin σ.numPeriods := Fin.cast hσNum.symm (Fin.natAdd k (0 : Fin (n + 2)))
      let σ1 : Fin σ.numPeriods := Fin.cast hσNum.symm (Fin.natAdd k (1 : Fin (n + 2)))
      let τ0 : Fin τ.numPeriods := Fin.cast hτNum.symm (Fin.natAdd k (0 : Fin (n + 2)))
      let τ1 : Fin τ.numPeriods := Fin.cast hτNum.symm (Fin.natAdd k (1 : Fin (n + 2)))
      let sameτ : Fin σ.numPeriods → Fin τ.numPeriods := fun i =>
        Fin.cast hτNum.symm (Fin.cast hσNum i)
      ∀ x, eτ x = if eσ x = σ0 then τ1 else if eσ x = σ1 then τ0 else sameτ (eσ x))
    (hPeriods : ∀ x, σ.periods (eσ x) = τ.periods (eτ x)) :
    Nonempty (FuchsianPresentedGroup σ ≃* FuchsianPresentedGroup τ) := by
  let σ0 : Fin σ.numPeriods := Fin.cast hσNum.symm (Fin.natAdd k (0 : Fin (n + 2)))
  let σ1 : Fin σ.numPeriods := Fin.cast hσNum.symm (Fin.natAdd k (1 : Fin (n + 2)))
  let τ0 : Fin τ.numPeriods := Fin.cast hτNum.symm (Fin.natAdd k (0 : Fin (n + 2)))
  let τ1 : Fin τ.numPeriods := Fin.cast hτNum.symm (Fin.natAdd k (1 : Fin (n + 2)))
  let sameτ : Fin σ.numPeriods → Fin τ.numPeriods := fun i =>
    Fin.cast hτNum.symm (Fin.cast hσNum i)
  refine zeroGenusAdjacentSwapFuchsianPresentedGroupEquiv
    (k := k) (n := n) σ τ hσZero hτZero hσNum hτNum ?_ ?_ ?_ ?_
  · intro j
    let σj : Fin σ.numPeriods := Fin.cast hσNum.symm (Fin.castAdd (n + 2) j)
    let τj : Fin τ.numPeriods := Fin.cast hτNum.symm (Fin.castAdd (n + 2) j)
    let x : ι := eσ.symm σj
    have hxσ : eσ x = σj := by simp only [Equiv.apply_symm_apply, x]
    have hprefix_ne_zero :
        (Fin.castAdd (n + 2) j : Fin (k + (n + 2))) ≠
          Fin.natAdd k (0 : Fin (n + 2)) := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero] at this
      omega
    have hprefix_ne_one :
        (Fin.castAdd (n + 2) j : Fin (k + (n + 2))) ≠
          Fin.natAdd k (1 : Fin (n + 2)) := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.coe_ofNat_eq_mod, Nat.one_mod] at this
      omega
    have hxτ : eτ x = τj := by
      simpa [σ0, σ1, τ0, τ1, sameτ, σj, τj, hxσ, hprefix_ne_zero,
        hprefix_ne_one] using hAdjacent x
    calc
      σ.periods (Fin.cast hσNum.symm (Fin.castAdd (n + 2) j)) =
          σ.periods (eσ x) := by
        rw [hxσ]
      _ = τ.periods (eτ x) := hPeriods x
      _ = τ.periods (Fin.cast hτNum.symm (Fin.castAdd (n + 2) j)) := by
        rw [hxτ]
  · let x : ι := eσ.symm σ0
    have hxσ : eσ x = σ0 := by simp only [Equiv.apply_symm_apply, x]
    have hxτ : eτ x = τ1 := by
      simpa [σ0, σ1, τ0, τ1, sameτ, hxσ] using hAdjacent x
    calc
      σ.periods (Fin.cast hσNum.symm (Fin.natAdd k (0 : Fin (n + 2)))) =
          σ.periods (eσ x) := by
        rw [hxσ]
      _ = τ.periods (eτ x) := hPeriods x
      _ = τ.periods (Fin.cast hτNum.symm (Fin.natAdd k (1 : Fin (n + 2)))) := by
        rw [hxτ]
  · let x : ι := eσ.symm σ1
    have hxσ : eσ x = σ1 := by simp only [Equiv.apply_symm_apply, x]
    have hσ10 : σ1 ≠ σ0 := by
      intro h
      have := congrArg (fun i : Fin σ.numPeriods => (Fin.cast hσNum i).val) h
      simp only [Fin.cast_cast, Fin.cast_eq_self, Fin.val_natAdd, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.zero_mod,
  add_zero, Nat.add_eq_left, one_ne_zero, σ1, σ0] at this
    have hxτ : eτ x = τ0 := by
      simpa [σ0, σ1, τ0, τ1, sameτ, hxσ, hσ10] using hAdjacent x
    calc
      σ.periods (Fin.cast hσNum.symm (Fin.natAdd k (1 : Fin (n + 2)))) =
          σ.periods (eσ x) := by
        rw [hxσ]
      _ = τ.periods (eτ x) := hPeriods x
      _ = τ.periods (Fin.cast hτNum.symm (Fin.natAdd k (0 : Fin (n + 2)))) := by
        rw [hxτ]
  · intro t
    let σt : Fin σ.numPeriods := Fin.cast hσNum.symm (Fin.natAdd k t.succ.succ)
    let x : ι := eσ.symm σt
    have hxσ : eσ x = σt := by simp only [Equiv.apply_symm_apply, x]
    have htail_ne_zero : (t.succ.succ : Fin (n + 2)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.add_eq_zero_iff, one_ne_zero, and_false,
  and_self] at this
    have htail_ne_one : (t.succ.succ : Fin (n + 2)) ≠ 1 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.add_eq_right, Nat.add_eq_zero_iff,
  one_ne_zero, and_false] at this
    have hxτ : eτ x = Fin.cast hτNum.symm (Fin.natAdd k t.succ.succ) := by
      simpa [σ0, σ1, τ0, τ1, sameτ, σt, hxσ, htail_ne_zero, htail_ne_one] using
        hAdjacent x
    calc
      σ.periods (Fin.cast hσNum.symm (Fin.natAdd k t.succ.succ)) =
          σ.periods (eσ x) := by
        rw [hxσ]
      _ = τ.periods (eτ x) := hPeriods x
      _ = τ.periods (Fin.cast hτNum.symm (Fin.natAdd k t.succ.succ)) := by
        rw [hxτ]
noncomputable def zeroGenusPermutedSignature
    (σ : FuchsianSignature) {m : ℕ} (hNum : σ.numPeriods = m)
    (p : Equiv.Perm (Fin m)) : FuchsianSignature where
  orbitGenus := 0
  numCusps := 0
  numPeriods := m
  periods := fun i => σ.periods (Fin.cast hNum.symm (p i))
  period_ge_two := by
    intro i
    exact σ.period_ge_two _
  numCusps_eq_zero := rfl
  numPeriods_ge_three := by
    have hge := σ.numPeriods_ge_three
    omega
@[local simp]
theorem zeroGenusPermutedSignature_orbitGenus
    (σ : FuchsianSignature) {m : ℕ} (hNum : σ.numPeriods = m)
    (p : Equiv.Perm (Fin m)) :
    (zeroGenusPermutedSignature σ hNum p).orbitGenus = 0 := rfl
@[local simp]
theorem zeroGenusPermutedSignature_numPeriods
    (σ : FuchsianSignature) {m : ℕ} (hNum : σ.numPeriods = m)
    (p : Equiv.Perm (Fin m)) :
    (zeroGenusPermutedSignature σ hNum p).numPeriods = m := rfl
@[local simp]
theorem zeroGenusPermutedSignature_periods
    (σ : FuchsianSignature) {m : ℕ} (hNum : σ.numPeriods = m)
    (p : Equiv.Perm (Fin m)) (i : Fin m) :
    (zeroGenusPermutedSignature σ hNum p).periods i =
      σ.periods (Fin.cast hNum.symm (p i)) := rfl
private theorem zeroGenusFuchsianPresentedGroupEquivOfPermutedSignature
    (σ : FuchsianSignature) (hσZero : σ.orbitGenus = 0)
    {r : ℕ} (hNum : σ.numPeriods = r + 1)
    (p : Equiv.Perm (Fin (r + 1))) :
    Nonempty
      (FuchsianPresentedGroup σ ≃*
        FuchsianPresentedGroup (zeroGenusPermutedSignature σ hNum p)) := by
  classical
  let S : Equiv.Perm (Fin (r + 1)) → FuchsianSignature :=
    fun p => zeroGenusPermutedSignature σ hNum p
  let adjacentSet : Set (Equiv.Perm (Fin (r + 1))) :=
    Set.range fun i : Fin r => Equiv.swap i.castSucc i.succ
  have htop : Submonoid.closure adjacentSet = ⊤ := by
    simpa [adjacentSet] using Equiv.Perm.mclosure_swap_castSucc_succ r
  refine Submonoid.induction_of_closure_eq_top_right
    (s := adjacentSet) htop p ?_ ?_
  · refine zeroGenusFuchsianPresentedGroupEquivOfOrderedPeriods
      σ (S 1) hσZero rfl hNum ?_
    intro i
    simp only [zeroGenusPermutedSignature_numPeriods, zeroGenusPermutedSignature_periods, Equiv.Perm.coe_one,
  id_eq, Fin.cast_cast, Fin.cast_eq_self, S]
  · intro p s hs ih
    rcases hs with ⟨i, rfl⟩
    let sw : Equiv.Perm (Fin (r + 1)) := Equiv.swap i.castSucc i.succ
    let k : ℕ := i.val
    let nTail : ℕ := r - i.val - 1
    have hAdjNum : r + 1 = k + (nTail + 2) := by
      dsimp [k, nTail]
      omega
    have hpos0 :
        Fin.cast hAdjNum.symm (Fin.natAdd k (0 : Fin (nTail + 2))) =
          i.castSucc := by
      ext
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Fin.val_castSucc, k,
  nTail]
    have hpos1 :
        Fin.cast hAdjNum.symm (Fin.natAdd k (1 : Fin (nTail + 2))) =
          i.succ := by
      ext
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.coe_ofNat_eq_mod, Nat.one_mod, Fin.val_succ,
  k, nTail]
    have hswap_apply :
        ∀ x : Fin (r + 1),
          sw x = if x = i.castSucc then i.succ else if x = i.succ then i.castSucc else x := by
      intro x
      by_cases hx0 : x = i.castSucc
      · subst x
        simp only [Equiv.swap_apply_left, ↓reduceIte, sw]
      · by_cases hx1 : x = i.succ
        · subst x
          simp only [Equiv.swap_apply_right, hx0, ↓reduceIte, sw]
        · simpa [sw, hx0, hx1] using Equiv.swap_apply_of_ne_of_ne hx0 hx1
    have hstep :
        Nonempty (FuchsianPresentedGroup (S p) ≃* FuchsianPresentedGroup (S (p * sw))) := by
      refine zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods_of_adjacentSwap
        (S p) (S (p * sw)) rfl rfl
        (Equiv.refl (Fin (r + 1))) sw hAdjNum hAdjNum ?_ ?_
      · dsimp
        intro x
        rw [hpos0, hpos1]
        exact hswap_apply x
      · intro x
        simp only [zeroGenusPermutedSignature_numPeriods, Equiv.refl_apply, zeroGenusPermutedSignature_periods,
  Equiv.Perm.coe_mul, Function.comp_apply, Equiv.swap_apply_self, S, sw]
    rcases ih with ⟨e₁⟩
    rcases hstep with ⟨e₂⟩
    exact ⟨e₁.trans e₂⟩
theorem zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods
    (σ τ : FuchsianSignature)
    (hσZero : σ.orbitGenus = 0) (hτZero : τ.orbitGenus = 0)
    {ι : Type*}
    (eσ : ι ≃ Fin σ.numPeriods) (eτ : ι ≃ Fin τ.numPeriods)
    (hPeriods : ∀ x, σ.periods (eσ x) = τ.periods (eτ x)) :
    Nonempty (FuchsianPresentedGroup σ ≃* FuchsianPresentedGroup τ) := by
  classical
  letI : Fintype ι := Fintype.ofEquiv (Fin σ.numPeriods) eσ.symm
  have hσCard : Fintype.card ι = σ.numPeriods := by
    simpa using Fintype.card_congr eσ
  have hτCard : Fintype.card ι = τ.numPeriods := by
    simpa using Fintype.card_congr eτ
  have hNum : σ.numPeriods = τ.numPeriods := hσCard.symm.trans hτCard
  let r : ℕ := σ.numPeriods - 1
  have hσLen : σ.numPeriods = r + 1 := by
    dsimp [r]
    have hge := σ.numPeriods_ge_three
    omega
  have hτLen : τ.numPeriods = r + 1 := by
    omega
  let p : Equiv.Perm (Fin (r + 1)) :=
    (finCongr hτLen.symm).trans (eτ.symm.trans (eσ.trans (finCongr hσLen)))
  rcases zeroGenusFuchsianPresentedGroupEquivOfPermutedSignature σ hσZero hσLen p with ⟨e₁⟩
  have hρτ :
      Nonempty
        (FuchsianPresentedGroup (zeroGenusPermutedSignature σ hσLen p) ≃*
          FuchsianPresentedGroup τ) := by
    refine zeroGenusFuchsianPresentedGroupEquivOfOrderedPeriods
      (zeroGenusPermutedSignature σ hσLen p) τ rfl hτZero hτLen.symm ?_
    intro j
    let t : Fin τ.numPeriods := Fin.cast hτLen.symm j
    let x : ι := eτ.symm t
    have hxτ : eτ x = t := by
      simp only [Equiv.apply_symm_apply, x]
    calc
      (zeroGenusPermutedSignature σ hσLen p).periods j = σ.periods (eσ x) := by
        simp only [zeroGenusPermutedSignature, Equiv.trans_apply, finCongr_apply, Fin.cast_cast, Fin.cast_eq_self, p,
  x, t]
      _ = τ.periods (eτ x) := hPeriods x
      _ = τ.periods (Fin.cast hτLen.symm j) := by
        rw [hxτ]
  rcases hρτ with ⟨e₂⟩
  exact ⟨e₁.trans e₂⟩
theorem firstReductionSourceMulEquiv_exists
    {σ : FuchsianSignature} (D : FirstReductionPeriodData σ)
    (hZero : σ.orbitGenus = 0) :
    Nonempty (FuchsianPresentedGroup σ ≃* FuchsianPresentedGroup D.sourceSignature) := by
  refine
    zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods σ D.sourceSignature
      hZero ?_ D.reindex (originalFirstReductionOrderedIndexEquiv D.tailLen) ?_
  · simp only [FirstReductionPeriodData.sourceSignature, originalFirstReductionSignature]
  · intro x
    rw [← D.periods_eq x]
    cases x using Sum.casesOn with
    | inl i =>
        fin_cases i <;>
          simp only [originalFirstReductionPeriods, twoPeriods, Nat.reduceAdd, Fin.mk_zero, Fin.mk_one, Fin.isValue,
  fin_cases_const_one, FirstReductionPeriodData.sourceSignature, originalFirstReductionSignature,
  originalFirstReductionOrderedIndexEquiv, Fin.val_eq_zero_iff, Equiv.coe_fn_mk, Fin.coe_ofNat_eq_mod, Nat.mod_succ,
  originalFirstReductionSignaturePeriod, one_ne_zero, ↓reduceDIte, Fin.cases_zero]
    | inr j =>
        simp only [originalFirstReductionPeriods, FirstReductionPeriodData.sourceSignature,
  originalFirstReductionSignature, originalFirstReductionOrderedIndexEquiv, Fin.val_eq_zero_iff, Fin.isValue,
  Equiv.coe_fn_mk, originalFirstReductionSignaturePeriod, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, false_and,
  ↓reduceDIte, add_tsub_cancel_left, Fin.eta, dite_eq_ite, right_eq_ite_iff]
        omega

end FenchelNielsen
