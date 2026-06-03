import ReidemeisterSchreier.Discrete.OpenSubgroups.Transversals

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/OpenSubgroups/Generators.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Schreier representatives and generators

Defines Schreier representatives, nontrivial Schreier pairs, classical generator values, and pointed transversal constructions.
-/

namespace ReidemeisterSchreier.Discrete.OpenSubgroups

section SchreierGenerators

open scoped Pointwise
open FreeGroup

/-- The Schreier transversal itself carries the same right-coset action, transported along the
equivalence with right cosets. -/
noncomputable def schreierTransversalRightCosetAction {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    MulAction (FreeGroup X) T := by
  letI : MulAction (FreeGroup X) (Quotient (QuotientGroup.rightRel L)) :=
    rightCosetLeftMulActionByInverse L
  let e : T ≃ Quotient (QuotientGroup.rightRel L) := hT.1.rightQuotientEquiv.symm
  refine
    { smul := fun g t => e.symm (g • e t)
      one_smul := by
        intro t
        change e.symm (1 • e t) = t
        rw [one_smul]
        exact e.left_inv t
      mul_smul := by
        intro g h t
        change e.symm ((g * h) • e t) = e.symm (g • e (e.symm (h • e t)))
        rw [mul_smul, e.apply_symm_apply] }

/-- The chosen representative of a right coset attached to a right Schreier transversal. -/
noncomputable def schreierRepresentative {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    FreeGroup X → T :=
  hT.1.toRightFun

@[simp] theorem schreierRepresentative_eq_of_mem {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {t : FreeGroup X} (ht : t ∈ T) :
  schreierRepresentative (X := X) hT t = ⟨t, ht⟩ := by
  apply (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp hT.1 t).unique
  · exact hT.1.mul_inv_toRightFun_mem t
  · simp only [mul_inv_cancel, SetLike.mem_coe, one_mem]

@[simp] theorem schreierRepresentative_eq_one_of_mem {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {g : FreeGroup X} (hg : g ∈ L) :
    schreierRepresentative (X := X) hT g = ⟨1, hT.2.1⟩ := by
  apply (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp hT.1 g).unique
  · exact hT.1.mul_inv_toRightFun_mem g
  · simpa using hg

theorem schreierRepresentative_eq_of_mem_mul_inv_mem {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {g t : FreeGroup X} (ht : t ∈ T) (hgt : g * t⁻¹ ∈ L) :
    schreierRepresentative (X := X) hT g = ⟨t, ht⟩ := by
  apply (Subgroup.isComplement_iff_existsUnique_mul_inv_mem.mp hT.1 g).unique
  · exact hT.1.mul_inv_toRightFun_mem g
  · exact hgt

theorem prefixParent_mem_of_mem {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {t : FreeGroup X} (ht : t ∈ T) :
    FreeGroup.prefixParent t ∈ T := by
  refine hT.2.2 ht ?_
  refine ⟨(FreeGroup.toWord t).length - 1, Nat.sub_le (FreeGroup.toWord t).length 1, ?_⟩
  simp only [prefixParent, List.dropLast_eq_take]

theorem schreierTransversalRightCosetAction_smul {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (g : FreeGroup X) (t : T) :
    letI := schreierTransversalRightCosetAction (X := X) hT
    g • t = schreierRepresentative (X := X) hT ((t : FreeGroup X) * g⁻¹) := by
  let e : T ≃ Quotient (QuotientGroup.rightRel L) := hT.1.rightQuotientEquiv.symm
  have ht : e t = Quotient.mk'' (t : FreeGroup X) := by
    simpa [e] using hT.1.mk''_rightQuotientEquiv (e t)
  change
      hT.1.rightQuotientEquiv (g • hT.1.rightQuotientEquiv.symm t) =
        hT.1.rightQuotientEquiv (Quotient.mk'' ((t : FreeGroup X) * g⁻¹))
  rw [ht, rightCosetLeftMulActionByInverse_mk_smul]

/-- The Schreier expression attached to any word `t` and basis element `x`. -/
noncomputable def schreierGenerator {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) (t : FreeGroup X) (x : X) : L := by
  refine
    ⟨t * FreeGroup.of x *
        ((schreierRepresentative (X := X) hT (t * FreeGroup.of x) : T) : FreeGroup X)⁻¹, ?_⟩
  exact hT.1.mul_inv_toRightFun_mem (t * FreeGroup.of x)

/-- The canonical index type for the nontrivial Schreier generators attached to a right Schreier
transversal.  This pair-indexed type is the preferred basis index; the value-set
`schreierGeneratorSet` records the same nontrivial generators by their subgroup values. -/
abbrev NontrivialSchreierPair {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) : Type u :=
  {p : T × X // schreierGenerator (X := X) hT ((p.1 : T) : FreeGroup X) p.2 ≠ 1}

/-- The Schreier generator value represented by a nontrivial Schreier pair. -/
noncomputable def nontrivialSchreierPairGenerator {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    NontrivialSchreierPair (X := X) hT → L :=
  fun p => schreierGenerator (X := X) hT ((p.1.1 : T) : FreeGroup X) p.1.2

@[simp] theorem nontrivialSchreierPairGenerator_apply {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (p : NontrivialSchreierPair (X := X) hT) :
    nontrivialSchreierPairGenerator (X := X) hT p =
      schreierGenerator (X := X) hT ((p.1.1 : T) : FreeGroup X) p.1.2 :=
  rfl

/-- The classical Schreier generator value set attached to a right Schreier transversal.
Prefer `NontrivialSchreierPair` as the basis index; this set records only the resulting values. -/
def schreierGeneratorSet {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) : Set L :=
  {z | ∃ t ∈ T, ∃ x : X, z = schreierGenerator (X := X) hT t x ∧ z ≠ 1}

@[simp] theorem mem_schreierGeneratorSet_iff {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) {z : L} :
    z ∈ schreierGeneratorSet (X := X) hT ↔
      ∃ t ∈ T, ∃ x : X, z = schreierGenerator (X := X) hT t x ∧ z ≠ 1 :=
  Iff.rfl

theorem schreierGenerator_mem_schreierGeneratorSet_of_mem_of_ne_one
    {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {t : FreeGroup X} (ht : t ∈ T) (x : X)
    (hne : schreierGenerator (X := X) hT t x ≠ 1) :
    schreierGenerator (X := X) hT t x ∈ schreierGeneratorSet (X := X) hT :=
  ⟨t, ht, x, rfl, hne⟩

theorem schreierGenerator_mem_schreierGeneratorSet_of_ne_one
    {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    (t : T) (x : X)
    (hne : schreierGenerator (X := X) hT (t : FreeGroup X) x ≠ 1) :
    schreierGenerator (X := X) hT (t : FreeGroup X) x ∈
      schreierGeneratorSet (X := X) hT :=
  schreierGenerator_mem_schreierGeneratorSet_of_mem_of_ne_one
    (X := X) hT t.property x hne

/-- The value-set API is precisely the range of the pair-indexed generator map. -/
theorem schreierGeneratorSet_eq_range_nontrivialSchreierPairGenerator
    {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T) :
    schreierGeneratorSet (X := X) hT =
      Set.range (nontrivialSchreierPairGenerator (X := X) hT) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨t, ht, x, hz, hne⟩
    refine ⟨⟨(⟨t, ht⟩, x), ?_⟩, ?_⟩
    · simpa [hz] using hne
    · simp only [nontrivialSchreierPairGenerator, hz]
  · rintro ⟨p, rfl⟩
    exact schreierGenerator_mem_schreierGeneratorSet_of_ne_one
      (X := X) hT p.1.1 p.1.2 p.2

@[simp] theorem schreierGenerator_eq_one_of_mem {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {t : FreeGroup X} {x : X}
    (htx : t * FreeGroup.of x ∈ T) :
    schreierGenerator (X := X) hT t x = 1 := by
  apply Subtype.ext
  simp only [schreierGenerator, schreierRepresentative_eq_of_mem (X := X) hT htx, mul_inv_rev, mul_assoc,
  mul_inv_cancel_left, mul_inv_cancel, OneMemClass.coe_one]

@[simp] theorem schreierGenerator_eq_of_mul_mem {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {t : FreeGroup X} {x : X}
    (htx : t * FreeGroup.of x ∈ L) :
    schreierGenerator (X := X) hT t x = ⟨t * FreeGroup.of x, htx⟩ := by
  apply Subtype.ext
  simp only [schreierGenerator, schreierRepresentative_eq_one_of_mem (X := X) hT htx, inv_one, mul_one]

theorem schreierGenerator_eq_one_iff {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    {hT : IsRightSchreierTransversal (X := X) L T}
    {t : FreeGroup X} {x : X} :
    schreierGenerator (X := X) hT t x = 1 ↔
      ((schreierRepresentative (X := X) hT (t * FreeGroup.of x) : T) : FreeGroup X) =
        t * FreeGroup.of x := by
  constructor
  · intro h
    have hval : t * FreeGroup.of x *
        (((schreierRepresentative (X := X) hT (t * FreeGroup.of x) : T) : FreeGroup X))⁻¹ = 1 := by
      exact congrArg Subtype.val h
    have hmul := congrArg
      (fun g : FreeGroup X =>
        g * ((schreierRepresentative (X := X) hT (t * FreeGroup.of x) : T) : FreeGroup X)) hval
    simpa [mul_assoc] using hmul.symm
  · intro hrep
    apply Subtype.ext
    simp only [schreierGenerator, hrep, mul_inv_rev, mul_assoc, mul_inv_cancel_left, mul_inv_cancel,
  OneMemClass.coe_one]


/-- Pointed discrete Reidemeister-Schreier: if `x^N` is the first positive power of a free
generator landing in `L`, one may choose a right Schreier transversal whose distinguished
Schreier generator is exactly `x^N`. -/
theorem exists_rightSchreierTransversal_of_minimalGeneratorPower
    {X : Type u} [DecidableEq X] {L : Subgroup (FreeGroup X)} (x : X) {N : ℕ}
    (hN : 0 < N)
    (hpow : (FreeGroup.of x) ^ N ∈ L)
    (hmin : ∀ m : ℕ, 0 < m → m < N → (FreeGroup.of x) ^ m ∉ L) :
    ∃ T : Set (FreeGroup X), ∃ hT : IsRightSchreierTransversal (X := X) L T,
      (FreeGroup.of x) ^ (N - 1) ∈ T ∧
        schreierGenerator (X := X) hT ((FreeGroup.of x) ^ (N - 1)) x =
          ⟨(FreeGroup.of x) ^ N, hpow⟩ := by
  let T₀ : Set (FreeGroup X) := Set.range fun i : Fin N => (FreeGroup.of x) ^ (i : ℕ)
  have hT₀ : IsRightPartialSchreierTransversal (X := X) L T₀ :=
    isRightPartialSchreierTransversal_generatorPowers_of_minimalPower
      (X := X) (L := L) x hN hmin
  rcases exists_rightSchreierTransversal_of_partial (X := X) (L := L) hT₀ with
    ⟨T, hsub, hT⟩
  have hpred : (FreeGroup.of x) ^ (N - 1) ∈ T := by
    apply hsub
    exact ⟨⟨N - 1, Nat.pred_lt (Nat.ne_of_gt hN)⟩, rfl⟩
  have hmul :
      (FreeGroup.of x) ^ (N - 1) * FreeGroup.of x = (FreeGroup.of x) ^ N := by
    calc
      (FreeGroup.of x) ^ (N - 1) * FreeGroup.of x = (FreeGroup.of x) ^ ((N - 1).succ) := by
        rw [pow_succ]
      _ = (FreeGroup.of x) ^ N := by
        simpa using congrArg (fun n : ℕ => (FreeGroup.of x) ^ n) (Nat.succ_pred_eq_of_pos hN)
  have hmul_mem : (FreeGroup.of x) ^ (N - 1) * FreeGroup.of x ∈ L := by
    rw [hmul]
    exact hpow
  refine ⟨T, hT, hpred, ?_⟩
  calc
    schreierGenerator (X := X) hT ((FreeGroup.of x) ^ (N - 1)) x =
        ⟨(FreeGroup.of x) ^ (N - 1) * FreeGroup.of x, hmul_mem⟩ := by
          exact schreierGenerator_eq_of_mul_mem (X := X) hT hmul_mem
    _ = ⟨(FreeGroup.of x) ^ N, hpow⟩ := by
      apply Subtype.ext
      exact hmul

theorem schreierRepresentative_eq_prefixParent_of_cancels {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {t : FreeGroup X} {x : X}
    (ht : t ∈ T) (hw : FreeGroup.toWord t ≠ [])
    (hlast : (FreeGroup.toWord t).getLast hw = (x, false)) :
    schreierRepresentative (X := X) hT (t * FreeGroup.of x) =
      ⟨FreeGroup.prefixParent t, prefixParent_mem_of_mem (X := X) hT ht⟩ := by
  rw [Internal.FreeGroupWord.FreeGroup.mul_of_eq_prefixParent_of_cancels t x hw hlast]
  exact schreierRepresentative_eq_of_mem (X := X) hT (prefixParent_mem_of_mem (X := X) hT ht)

theorem schreierRepresentative_eq_of_prefixParent_last_pos {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {t : FreeGroup X} (ht : t ∈ T) {x : X}
    (hw : FreeGroup.toWord t ≠ [])
    (hlast : (FreeGroup.toWord t).getLast hw = (x, true)) :
    schreierRepresentative (X := X) hT (FreeGroup.prefixParent t * FreeGroup.of x) = ⟨t, ht⟩ := by
  rw [Internal.FreeGroupWord.FreeGroup.prefixParent_mul_of_of_last_pos t x hw hlast]
  exact schreierRepresentative_eq_of_mem (X := X) hT ht

@[simp] theorem schreierGenerator_eq_one_of_cancels {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {t : FreeGroup X} {x : X}
    (ht : t ∈ T) (hw : FreeGroup.toWord t ≠ [])
    (hlast : (FreeGroup.toWord t).getLast hw = (x, false)) :
    schreierGenerator (X := X) hT t x = 1 := by
  apply schreierGenerator_eq_one_of_mem (X := X) hT
  rw [Internal.FreeGroupWord.FreeGroup.mul_of_eq_prefixParent_of_cancels t x hw hlast]
  exact prefixParent_mem_of_mem (X := X) hT ht

@[simp] theorem schreierGenerator_eq_one_of_prefixParent_last_pos {X : Type u} [DecidableEq X]
    {L : Subgroup (FreeGroup X)} {T : Set (FreeGroup X)}
    (hT : IsRightSchreierTransversal (X := X) L T)
    {t : FreeGroup X} (ht : t ∈ T) {x : X}
    (hw : FreeGroup.toWord t ≠ [])
    (hlast : (FreeGroup.toWord t).getLast hw = (x, true)) :
    schreierGenerator (X := X) hT (FreeGroup.prefixParent t) x = 1 := by
  apply schreierGenerator_eq_one_of_mem (X := X) hT
  rw [Internal.FreeGroupWord.FreeGroup.prefixParent_mul_of_of_last_pos t x hw hlast]
  exact ht


end SchreierGenerators

end ReidemeisterSchreier.Discrete.OpenSubgroups
