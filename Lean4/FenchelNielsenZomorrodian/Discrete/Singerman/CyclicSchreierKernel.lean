import FenchelNielsenZomorrodian.Discrete.Core.EllipticQuotientHom
import FenchelNielsenZomorrodian.Discrete.Singerman.CyclicQuotientActions

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Singerman/CyclicSchreierKernel.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Singerman/Reidemeister-Schreier bridge

Cyclic quotient actions, cyclic product identities, Schreier kernel computations, free-group word identities, and kernel transport for the compact Fuchsian proof.
-/

namespace FenchelNielsen
def CyclicSchreierRelatorData
    {X Y : Type} [DecidableEq X] {N : ℕ} [NeZero N] {rels : Set (FreeGroup X)}
    (f : X → Multiplicative (ZMod N))
    (x : X)
    (hx : FreeGroup.lift f (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N))
    (targetRelators : Set (FreeGroup Y)) : Type :=
  (let φ : FreeGroup X →* Multiplicative (ZMod N) := FreeGroup.lift f
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
      freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
    ReidemeisterSchreier.Discrete.Presentations.RelatorQuotientMutualMapData
      (ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
        (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := rels) T))
      targetRelators)
noncomputable def cyclicSchreierKernelEquivPresentedGroupOfRelatorData
    {X Y : Type} [DecidableEq X] {N : ℕ} [NeZero N] {rels : Set (FreeGroup X)}
    (f : X → Multiplicative (ZMod N))
    (hrels : ∀ r ∈ rels, FreeGroup.lift f r = 1)
    (x : X)
    (hx : FreeGroup.lift f (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N))
    (targetRelators : Set (FreeGroup Y))
    (hData : CyclicSchreierRelatorData (rels := rels) f x hx targetRelators) :
    (PresentedGroup.toGroup (rels := rels) (f := f) hrels).ker ≃*
      PresentedGroup targetRelators := by
  classical
  let φ : FreeGroup X →* Multiplicative (ZMod N) := FreeGroup.lift f
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let e : FreeGroup ↥(schreierGeneratorSet hT) ≃* φ.ker :=
    freeGroupKernelSchreierBasisEquivOfCyclicQuotientGenerator φ x hx
  let R : Set (FreeGroup ↥(schreierGeneratorSet hT)) :=
    ReidemeisterSchreier.Discrete.Presentations.freeGroupPullbackRelatorSet e
      (ReidemeisterSchreier.Discrete.Presentations.freeKernelTransversalRelatorSet (f := f) (rels := rels) T)
  let hTarget :
      FreeGroup ↥(schreierGeneratorSet hT) ⧸ Subgroup.normalClosure R ≃*
        PresentedGroup targetRelators :=
    ReidemeisterSchreier.Discrete.Presentations.quotientEquivOfRelatorQuotientMutualMapData R targetRelators
      (by simpa [CyclicSchreierRelatorData, φ, T, hT, e, R] using hData)
  let hKernel :
      FreeGroup ↥(schreierGeneratorSet hT) ⧸ Subgroup.normalClosure R ≃*
        (PresentedGroup.toGroup (rels := rels) (f := f) hrels).ker := by
    simpa [φ, T, hT, e, R] using
      (presentedFreeKernelCyclicSchreierRelatorQuotientEquivPresentedKernel
        (N := N) (rels := rels) (f := f) hrels x hx)
  exact hKernel.symm.trans hTarget

def FuchsianEllipticCyclicRelatorData
    {p : ℕ} [NeZero p] {Y : Type} (σ : FuchsianSignature)
    (ξ : Fin σ.numPeriods → Multiplicative (ZMod p))
    (i₀ : Fin σ.numPeriods)
    (hi₀ : ξ i₀ = Multiplicative.ofAdd (1 : ZMod p))
    (targetRelators : Set (FreeGroup Y)) : Type :=
  (letI := Classical.decEq (FuchsianGenerator σ)
   let f := ellipticQuotientGeneratorImage σ ξ
   let x := FuchsianGenerator.elliptic i₀
   let hx :
      FreeGroup.lift f (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage, hi₀, f, x]
   CyclicSchreierRelatorData (N := p) (rels := relators σ) f x hx targetRelators)

def FuchsianEllipticCyclicSchreierRelatorData
    {p : ℕ} [NeZero p] (σ τ : FuchsianSignature)
    (ξ : Fin σ.numPeriods → Multiplicative (ZMod p))
    (i₀ : Fin σ.numPeriods)
    (hi₀ : ξ i₀ = Multiplicative.ofAdd (1 : ZMod p)) : Type :=
  FuchsianEllipticCyclicRelatorData σ ξ i₀ hi₀ (relators τ)

noncomputable def fuchsianEllipticCyclicKernelEquivPresentedGroupOfRelatorData
    {p : ℕ} [NeZero p] {Y : Type} (σ : FuchsianSignature)
    (ξ : Fin σ.numPeriods → Multiplicative (ZMod p))
    (hpow : ∀ i, ξ i ^ σ.periods i = 1)
    (hprod : ∏ i : Fin σ.numPeriods, ξ i = 1)
    (i₀ : Fin σ.numPeriods)
    (hi₀ : ξ i₀ = Multiplicative.ofAdd (1 : ZMod p))
    (targetRelators : Set (FreeGroup Y))
    (D : FuchsianEllipticCyclicRelatorData σ ξ i₀ hi₀ targetRelators) :
    (ellipticQuotientHom σ ξ hpow hprod).ker ≃*
      PresentedGroup targetRelators := by
  classical
  letI := Classical.decEq (FuchsianGenerator σ)
  let f := ellipticQuotientGeneratorImage σ ξ
  let x := FuchsianGenerator.elliptic i₀
  let hx :
      FreeGroup.lift f (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod p) := by
    simp only [FreeGroup.lift_apply_of, ellipticQuotientGeneratorImage, hi₀, f, x]
  let hrels : ∀ r ∈ relators σ, FreeGroup.lift f r = 1 :=
    ellipticQuotientGeneratorImage_respects_relators σ ξ hpow hprod
  have hD :
      CyclicSchreierRelatorData (N := p) (rels := relators σ) f x hx targetRelators := by
    simpa [FuchsianEllipticCyclicRelatorData, f, x, hx] using D
  simpa [ellipticQuotientHom, f, x, hx, hrels] using
    cyclicSchreierKernelEquivPresentedGroupOfRelatorData
      (N := p) (rels := relators σ) f hrels x hx targetRelators hD

noncomputable def fuchsianEllipticCyclicKernelEquivOfRelatorData
    {p : ℕ} [NeZero p] (σ τ : FuchsianSignature)
    (ξ : Fin σ.numPeriods → Multiplicative (ZMod p))
    (hpow : ∀ i, ξ i ^ σ.periods i = 1)
    (hprod : ∏ i : Fin σ.numPeriods, ξ i = 1)
    (i₀ : Fin σ.numPeriods)
    (hi₀ : ξ i₀ = Multiplicative.ofAdd (1 : ZMod p))
    (D : FuchsianEllipticCyclicSchreierRelatorData σ τ ξ i₀ hi₀) :
    (ellipticQuotientHom σ ξ hpow hprod).ker ≃*
      FuchsianPresentedGroup τ :=
  fuchsianEllipticCyclicKernelEquivPresentedGroupOfRelatorData
    σ ξ hpow hprod i₀ hi₀ (relators τ) D
theorem freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
    {X : Type*} {N : ℕ}
    (φ : FreeGroup X →* Multiplicative (ZMod N)) (x : X)
    (hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N))
    {m : ℕ} (hm : m < N) :
    (FreeGroup.of x) ^ m ∈ Set.range (cyclicQuotientRightRep φ (FreeGroup.of x)) := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le m) hm)⟩
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
private theorem freeGroupGeneratorPower_mul_generator_mem_range_cyclicQuotientRightRep
    {X : Type*} {N : ℕ}
    (φ : FreeGroup X →* Multiplicative (ZMod N)) (x : X)
    (hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N))
    {k : ℕ} (hk : k + 1 < N) :
    (FreeGroup.of x) ^ k * FreeGroup.of x ∈
      Set.range (cyclicQuotientRightRep φ (FreeGroup.of x)) := by
  simpa [pow_succ] using
    freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep φ x hx (m := k + 1) hk
theorem cyclicQuotient_distinguished_schreierGenerator_eq_one_of_succ_lt
    {X : Type*} [DecidableEq X] {N : ℕ} [NeZero N]
    (φ : FreeGroup X →* Multiplicative (ZMod N)) (x : X)
    (hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N))
    {k : ℕ} (hk : k + 1 < N) :
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    schreierGenerator hT ((FreeGroup.of x) ^ k) x = 1 := by
  classical
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  exact schreierGenerator_eq_one_of_mem hT
    (freeGroupGeneratorPower_mul_generator_mem_range_cyclicQuotientRightRep φ x hx hk)
theorem cyclicQuotient_distinguished_schreierGenerator_wrap_eq
    {X : Type*} [DecidableEq X] {N : ℕ} [NeZero N]
    (φ : FreeGroup X →* Multiplicative (ZMod N)) (x : X)
    (hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N)) :
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    schreierGenerator hT ((FreeGroup.of x) ^ (N - 1)) x =
      (⟨(FreeGroup.of x) ^ N, by
        rw [MonoidHom.mem_ker]
        rw [map_pow, hx]
        apply (Multiplicative.toAdd : Multiplicative (ZMod N) ≃ ZMod N).injective
        simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]⟩ : φ.ker) := by
  classical
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  apply Subtype.ext
  have hpowKer : (FreeGroup.of x) ^ N ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    rw [map_pow, hx]
    apply (Multiplicative.toAdd : Multiplicative (ZMod N) ≃ ZMod N).injective
    simp only [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, CharP.cast_eq_zero, mul_one, toAdd_one]
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hsucc : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hNpos)
  have hprod : (FreeGroup.of x) ^ (N - 1) * FreeGroup.of x = (FreeGroup.of x) ^ N := by
    rw [← pow_succ, hsucc]
  have hprodKer : (FreeGroup.of x) ^ (N - 1) * FreeGroup.of x ∈ φ.ker := by
    simpa [hprod] using hpowKer
  simp only [schreierGenerator, hprod, schreierRepresentative_eq_one_of_mem hT hpowKer, inv_one, mul_one]
theorem cyclicQuotient_trivialImage_schreierGenerator_eq_conj
    {X : Type*} [DecidableEq X] {N : ℕ} [NeZero N]
    (φ : FreeGroup X →* Multiplicative (ZMod N)) (x y : X)
    (hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N))
    (hy : φ (FreeGroup.of y) = 1) (k : Fin N) :
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    schreierGenerator hT ((FreeGroup.of x) ^ k.val) y =
      (⟨(FreeGroup.of x) ^ k.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ k.val)⁻¹, by
        rw [MonoidHom.mem_ker]
        simp only [map_mul, map_pow, hx, hy, mul_one, map_inv, mul_inv_cancel]⟩ : φ.ker) := by
  classical
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let t : FreeGroup X := (FreeGroup.of x) ^ k.val
  have ht : t ∈ T := by
    simpa [T, t] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep φ x hx (m := k.val) k.isLt
  have hker : (t * FreeGroup.of y) * t⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_pow, hx, hy, mul_one, map_inv, mul_inv_cancel, t]
  apply Subtype.ext
  simp only [schreierGenerator, schreierRepresentative_eq_of_mem_mul_inv_mem hT ht hker, t]
theorem cyclicQuotient_negOneImage_schreierGenerator_eq
    {X : Type*} [DecidableEq X] {N : ℕ} [NeZero N]
    (φ : FreeGroup X →* Multiplicative (ZMod N)) (x y : X)
    (hx : φ (FreeGroup.of x) = Multiplicative.ofAdd (1 : ZMod N))
    (hy : φ (FreeGroup.of y) = Multiplicative.ofAdd (-1 : ZMod N)) (k : Fin N) :
    let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
    let hT : IsRightSchreierTransversal φ.ker T :=
      cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
    let r : ℕ := ((k.val : ZMod N) - 1).val
    schreierGenerator hT ((FreeGroup.of x) ^ k.val) y =
      (⟨(FreeGroup.of x) ^ k.val * FreeGroup.of y *
          ((FreeGroup.of x) ^ r)⁻¹, by
        rw [MonoidHom.mem_ker]
        rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
        apply (Multiplicative.toAdd : Multiplicative (ZMod N) ≃ ZMod N).injective
        simp only [ofAdd_neg, toAdd_mul, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, toAdd_inv, ZMod.natCast_val,
  dvd_refl, ZMod.cast_sub, ZMod.cast_natCast, ZMod.cast_one, neg_sub, toAdd_one, r]
        ring⟩ : φ.ker) := by
  classical
  let T := Set.range (cyclicQuotientRightRep φ (FreeGroup.of x))
  let hT : IsRightSchreierTransversal φ.ker T :=
    cyclicQuotientRightRep_isRightSchreierTransversal_of_freeGroupGenerator φ x hx
  let r : ℕ := ((k.val : ZMod N) - 1).val
  let t : FreeGroup X := (FreeGroup.of x) ^ k.val
  let u : FreeGroup X := (FreeGroup.of x) ^ r
  have hu : u ∈ T := by
    simpa [T, u, r] using
      freeGroupGeneratorPower_mem_range_cyclicQuotientRightRep
        φ x hx (m := r) (ZMod.val_lt ((k.val : ZMod N) - 1))
  have hker : (t * FreeGroup.of y) * u⁻¹ ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    rw [map_mul, map_inv, map_mul, map_pow, map_pow, hx, hy]
    apply (Multiplicative.toAdd : Multiplicative (ZMod N) ≃ ZMod N).injective
    simp only [ofAdd_neg, toAdd_mul, toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, mul_one, toAdd_inv, ZMod.natCast_val,
  dvd_refl, ZMod.cast_sub, ZMod.cast_natCast, ZMod.cast_one, neg_sub, toAdd_one, r]
    ring
  apply Subtype.ext
  simp only [schreierGenerator, schreierRepresentative_eq_of_mem_mul_inv_mem hT hu hker, u, r, t]
end FenchelNielsen
