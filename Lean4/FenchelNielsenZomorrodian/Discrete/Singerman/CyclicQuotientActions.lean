import ReidemeisterSchreier.Discrete.Presentations.KernelQuotient
import FenchelNielsenZomorrodian.Discrete.Singerman.ReidemeisterSchreier

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Singerman/CyclicQuotientActions.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Singerman/Reidemeister-Schreier bridge

Cyclic quotient actions, cyclic product identities, Schreier kernel computations, free-group word identities, and kernel transport for the compact Fuchsian proof.
-/

open scoped Pointwise
namespace FenchelNielsen
universe u
noncomputable def cyclicQuotientRightRep
    {G : Type*} [Group G] {N : ℕ}
    (φ : G →* Multiplicative (ZMod N)) (t : G) :
    Quotient (QuotientGroup.rightRel φ.ker) → G :=
  Quotient.lift
    (fun g => t ^ (Multiplicative.toAdd (φ g)).val)
    (by
      intro a b hab
      have hab' : QuotientGroup.rightRel φ.ker a b := hab
      rw [QuotientGroup.rightRel_apply] at hab'
      have habφ : φ a = φ b := by
        have habφ' : φ b = φ a := by
          apply eq_of_mul_inv_eq_one
          simpa [map_mul, map_inv] using MonoidHom.mem_ker.mp hab'
        exact habφ'.symm
      have hval :
          (Multiplicative.toAdd (φ a)).val = (Multiplicative.toAdd (φ b)).val := by
        exact congrArg ZMod.val (congrArg Multiplicative.toAdd habφ)
      simp only [hval])
@[simp 900] theorem cyclicQuotientRightRep_spec
    {G : Type*} [Group G] {N : ℕ} [NeZero N]
    (φ : G →* Multiplicative (ZMod N)) (t : G)
    (ht : φ t = Multiplicative.ofAdd (1 : ZMod N))
    (q : Quotient (QuotientGroup.rightRel φ.ker)) :
    Quotient.mk'' (cyclicQuotientRightRep φ t q) = q := by
  refine Quotient.inductionOn' q ?_
  intro g
  apply Quotient.sound'
  rw [QuotientGroup.rightRel_apply]
  rw [MonoidHom.mem_ker]
  have hk :
      Multiplicative.ofAdd (((Multiplicative.toAdd (φ g)).val : ℕ) : ZMod N) = φ g := by
    exact congrArg Multiplicative.ofAdd
      (ZMod.natCast_zmod_val (Multiplicative.toAdd (φ g)))
  rw [show cyclicQuotientRightRep φ t (Quotient.mk'' g) =
      t ^ (Multiplicative.toAdd (φ g)).val by rfl]
  rw [map_mul, MonoidHom.map_inv, MonoidHom.map_pow, ← hk, ht]
  apply (Multiplicative.toAdd : Multiplicative (ZMod N) ≃ ZMod N).injective
  simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, ofAdd_toAdd, toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd,
  nsmul_eq_mul, mul_one, add_neg_cancel, toAdd_one]
/-- The cyclic right representative set complements the kernel. -/
theorem ker_isComplement_range_cyclicQuotientRightRep
    {G : Type*} [Group G] {N : ℕ} [NeZero N]
    (φ : G →* Multiplicative (ZMod N)) (t : G)
    (ht : φ t = Multiplicative.ofAdd (1 : ZMod N)) :
    Subgroup.IsComplement (φ.ker : Set G) (Set.range (cyclicQuotientRightRep φ t)) :=
  Subgroup.isComplement_range_right (cyclicQuotientRightRep_spec φ t ht)
/-- The representative set of `cyclicQuotientRightRep` contains the identity. -/
theorem one_mem_range_cyclicQuotientRightRep
    {G : Type*} [Group G] {N : ℕ}
    (φ : G →* Multiplicative (ZMod N)) (t : G) :
    (1 : G) ∈ Set.range (cyclicQuotientRightRep φ t) := by
  refine ⟨Quotient.mk'' (1 : G), ?_⟩
  simp only [cyclicQuotientRightRep, Quotient.lift_mk, map_one, toAdd_one, ZMod.val_zero, pow_zero]
/-- Powers below the modulus of the distinguished free generator lie in the representative set. -/
theorem generatorPower_mem_range_cyclicQuotientRightRep
    {X : Type*} {N : ℕ} [NeZero N]
    (φ : FreeGroup X →* Multiplicative (ZMod N)) (x : X)
    (hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N))
    {m : ℕ} (hm : m < N) :
    (FreeGroup.of x) ^ m ∈ Set.range (cyclicQuotientRightRep φ (FreeGroup.of x)) := by
  classical
  refine ⟨Quotient.mk'' ((FreeGroup.of x) ^ m), ?_⟩
  have hφm : φ ((FreeGroup.of x) ^ m) = Multiplicative.ofAdd ((m : ℕ) : ZMod N) := by
    rw [map_pow, hx]
    apply (Multiplicative.toAdd : Multiplicative (ZMod N) ≃ ZMod N).injective
    simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one]
  have hval : (Multiplicative.toAdd (φ ((FreeGroup.of x) ^ m))).val = m := by
    rw [hφm]
    simpa using (ZMod.val_natCast_of_lt hm)
  change (FreeGroup.of x) ^ (Multiplicative.toAdd (φ ((FreeGroup.of x) ^ m))).val =
    (FreeGroup.of x) ^ m
  rw [hval]
theorem mem_range_cyclicQuotientRightRep_iff_generatorPower
    {X : Type*} {N : ℕ} [NeZero N]
    (φ : FreeGroup X →* Multiplicative (ZMod N)) {x : X}
    (hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N))
    {t : FreeGroup X} :
    t ∈ Set.range (cyclicQuotientRightRep φ (FreeGroup.of x)) ↔
      ∃ k : Fin N, t = (FreeGroup.of x) ^ k.val := by
  constructor
  · intro ht
    rcases ht with ⟨q, rfl⟩
    refine Quotient.inductionOn' q ?_
    intro g
    exact
      ⟨⟨(Multiplicative.toAdd (φ g)).val,
          ZMod.val_lt (Multiplicative.toAdd (φ g))⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact generatorPower_mem_range_cyclicQuotientRightRep φ x hx k.isLt
theorem cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator
    {X : Type*} [DecidableEq X] {N : ℕ} [NeZero N]
    (φ : FreeGroup X →* Multiplicative (ZMod N)) (x : X)
    (hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N)) :
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    IsRightSchreierTransversal φ.ker T := by
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  refine ⟨?_, ?_, ?_⟩
  · simpa [T] using
      ker_isComplement_range_cyclicQuotientRightRep φ (FreeGroup.of x) hx
  · simpa [T] using
      one_mem_range_cyclicQuotientRightRep φ (FreeGroup.of x)
  · intro t ht
    rcases ht with ⟨q, rfl⟩
    refine Quotient.inductionOn' q ?_
    intro g u hu
    have hrep :
        cyclicQuotientRightRep φ (FreeGroup.of x) (Quotient.mk'' g) =
          (FreeGroup.of x) ^ (Multiplicative.toAdd (φ g)).val := rfl
    rw [hrep] at hu
    rcases hu with ⟨m, hm, rfl⟩
    have hm' : m ≤ (Multiplicative.toAdd (φ g)).val := by
      simpa [FreeGroup.toWord_of_pow, List.length_replicate] using hm
    have hmlt : m < N := lt_of_le_of_lt hm' (ZMod.val_lt (Multiplicative.toAdd (φ g)))
    rw [FreeGroup.toWord_of_pow, List.take_replicate, min_eq_left hm',
      ← FreeGroup.toWord_of_pow, FreeGroup.mk_toWord]
    exact generatorPower_mem_range_cyclicQuotientRightRep φ x hx hmlt
noncomputable def freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator
    {X : Type*} [DecidableEq X] {N : ℕ} [NeZero N]
    (φ : FreeGroup X →* Multiplicative (ZMod N)) (x : X)
    (hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N)) :
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker := by
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  exact schreierGeneratorInverseBasisEquiv (X := X) hT
@[simp 900] theorem freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator_of
    {X : Type*} [DecidableEq X] {N : ℕ} [NeZero N]
    (φ : FreeGroup X →* Multiplicative (ZMod N)) (x : X)
    (hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N)) :
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    ∀ z : ↥(schreierGeneratorSet hT),
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx (FreeGroup.of z) =
        (z : φ.ker)⁻¹ := by
  classical
  dsimp
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  intro z
  exact schreierGeneratorInverseBasisEquiv_of (X := X) hT z
noncomputable def presentedFreeKernelCyclicSchreierRelatorQuotientEquivPresentedKernel
    {X : Type*} [DecidableEq X] {N : ℕ} [NeZero N] {rels : Set (FreeGroup X)}
    {f : X → Multiplicative (ZMod N)}
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1)
    (x : X)
    (hx : FreeGroup.lift f (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N)) :
    let φ := FreeGroup.lift f
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    FreeGroup ↥(schreierGeneratorSet hT) ⧸
        Subgroup.normalClosure
          (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
            (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := rels) T)) ≃*
      (PresentedGroup.toGroup (rels := rels) (f := f) hrels).ker := by
  classical
  let φ : FreeGroup X →* Multiplicative (ZMod N) := FreeGroup.lift f
  let T : Set (FreeGroup X) := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  simpa [φ, T, hT, e] using
    ReidemeisterSchreier.Discrete.Presentations.presentedFreeKernelSchreierRelatorQuotientEquivPresentedKernel hrels hT.1 e
end FenchelNielsen
