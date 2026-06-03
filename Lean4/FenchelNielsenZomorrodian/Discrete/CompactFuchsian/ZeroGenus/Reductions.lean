import FenchelNielsenZomorrodian.Discrete.CompactFuchsian.ZeroGenus.Reindexing

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/ZeroGenus/Reductions.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Compact zero-genus three-step proof data

Organizes first and second reduction data, perfectness numerics, reindexing, cleanup data, and the final zero-genus three-step finite-index theorem.
-/

namespace FenchelNielsen
structure FirstKernelTailPrimeDivisorData {σ : FuchsianSignature}
    (D : FirstReductionPeriodData σ) where
  q : ℕ
  hqPrime : q.Prime
  k : Fin D.tailLen
  hqk : q ∣ D.tail k
  hm₃pos : 0 < D.tail k / q
noncomputable def FirstReductionPeriodData.tailPrimeDivisorData
    {σ : FuchsianSignature} (D : FirstReductionPeriodData σ) :
    FirstKernelTailPrimeDivisorData D := by
  classical
  let k : Fin D.tailLen := ⟨0, D.hTailLen⟩
  have htail_ge : 2 ≤ D.tail k := D.htail k
  have htail_pos : 0 < D.tail k := lt_of_lt_of_le (by decide : 0 < 2) htail_ge
  have htail_ne_one : D.tail k ≠ 1 := by omega
  let hqExists : ∃ q, q.Prime ∧ q ∣ D.tail k := Nat.exists_prime_and_dvd htail_ne_one
  let q := Classical.choose hqExists
  have hqPrime : q.Prime := (Classical.choose_spec hqExists).1
  have hqk : q ∣ D.tail k := (Classical.choose_spec hqExists).2
  exact
    { q := q
      hqPrime := hqPrime
      k := k
      hqk := hqk
      hm₃pos := Nat.div_pos (Nat.le_of_dvd htail_pos hqk) hqPrime.pos }
structure SecondStageCleanupPeriodData
    {σ : FuchsianSignature} (D : FirstReductionPeriodData σ)
    (secondPrime : FirstKernelTailPrimeDivisorData D) where
  tailLen : ℕ
  m₃' : ℕ
  tail : Fin tailLen → ℕ
  hm₃' : 0 < m₃'
  htail : ∀ j, 2 ≤ tail j
  reindexTail : Fin (tailLen + 1) ≃ Fin D.tailLen
  tail_eq :
    ∀ j, firstReductionTailIncludingThird (q := secondPrime.q) m₃' tail j =
      D.tail (reindexTail j)
noncomputable def secondStageCleanupPeriodDataOfTailPrime
    {σ : FuchsianSignature} (D : FirstReductionPeriodData σ)
    (secondPrime : FirstKernelTailPrimeDivisorData D) :
    SecondStageCleanupPeriodData D secondPrime := by
  classical
  let tailLen := D.tailLen - 1
  have hLen : tailLen + 1 = D.tailLen := by
    have hpos : 1 ≤ D.tailLen := Nat.succ_le_of_lt D.hTailLen
    omega
  let k' : Fin (tailLen + 1) := (finCongr hLen).symm secondPrime.k
  let reindexTail : Fin (tailLen + 1) ≃ Fin D.tailLen :=
    (finHeadInsertionEquiv k').trans (finCongr hLen)
  let tail : Fin tailLen → ℕ := fun j => D.tail (reindexTail j.succ)
  have hmul : secondPrime.q * (D.tail secondPrime.k / secondPrime.q) =
      D.tail secondPrime.k := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel secondPrime.hqk
  exact
    { tailLen := tailLen
      m₃' := D.tail secondPrime.k / secondPrime.q
      tail := tail
      hm₃' := secondPrime.hm₃pos
      htail := by
        intro j
        exact D.htail (reindexTail j.succ)
      reindexTail := reindexTail
      tail_eq := by
        intro j
        refine Fin.cases ?_ ?_ j
        · change secondPrime.q * (D.tail secondPrime.k / secondPrime.q) =
            D.tail (reindexTail 0)
          simpa [reindexTail, k'] using hmul
        · intro a
          rfl }
noncomputable def SecondStageCleanupPeriodData.reindexSource
    {σ : FuchsianSignature} {D : FirstReductionPeriodData σ}
    {secondPrime : FirstKernelTailPrimeDivisorData D}
    (E : SecondStageCleanupPeriodData D secondPrime) :
    OriginalFirstReductionIndex (E.tailLen + 1) ≃ OriginalFirstReductionIndex D.tailLen :=
  Equiv.sumCongr (Equiv.refl (Fin 2)) E.reindexTail
noncomputable def SecondStageCleanupPeriodData.sourceSignature
    {σ : FuchsianSignature} {D : FirstReductionPeriodData σ}
    {secondPrime : FirstKernelTailPrimeDivisorData D}
    (E : SecondStageCleanupPeriodData D secondPrime) :
    FuchsianSignature :=
  originalFirstReductionSignature D.m₁' D.m₂'
    (firstReductionTailIncludingThird (q := secondPrime.q) E.m₃' E.tail)
    D.hp D.hm₁' D.hm₂'
    (firstReductionTailIncludingThird_ge_two_of_pos
      secondPrime.hqPrime.two_le E.m₃' E.tail E.hm₃' E.htail)
    (Nat.succ_pos _)
theorem secondStageCleanupSourceMulEquiv_exists
    {σ : FuchsianSignature} {D : FirstReductionPeriodData σ}
    {secondPrime : FirstKernelTailPrimeDivisorData D}
    (E : SecondStageCleanupPeriodData D secondPrime) :
    Nonempty (FuchsianPresentedGroup D.sourceSignature ≃*
      FuchsianPresentedGroup E.sourceSignature) := by
  refine
    zeroGenusFuchsianPresentedGroupEquivOfIndexedPeriods D.sourceSignature E.sourceSignature
      ?_ ?_
      (E.reindexSource.trans (originalFirstReductionOrderedIndexEquiv D.tailLen))
      (originalFirstReductionOrderedIndexEquiv (E.tailLen + 1)) ?_
  · rfl
  · rfl
  · intro x
    cases x using Sum.casesOn with
    | inl i =>
        fin_cases i <;>
          rfl
    | inr j =>
        have hD : 2 + (E.reindexTail j).val ≠ 1 := by omega
        have hE : 2 + j.val ≠ 1 := by omega
        simpa [SecondStageCleanupPeriodData.sourceSignature,
          FirstReductionPeriodData.sourceSignature, originalFirstReductionSignature,
          originalFirstReductionSignaturePeriod, originalFirstReductionOrderedIndexEquiv,
          originalFirstReductionPeriods, twoPeriods, SecondStageCleanupPeriodData.reindexSource,
          hD, hE]
          using (E.tail_eq j).symm

theorem SecondStageCleanupPeriodData.source_nonOne_periods_ge_two
    {σ : FuchsianSignature} {D : FirstReductionPeriodData σ}
    {secondPrime : FirstKernelTailPrimeDivisorData D}
    (E : SecondStageCleanupPeriodData D secondPrime) :
    ∀ i : NonOneSubfamilyIndex
        (secondReductionSourcePeriods (p := D.p) (q := secondPrime.q)
          D.m₁' D.m₂' E.m₃' E.tail),
      2 ≤ nonOneSubfamilyPeriods
        (secondReductionSourcePeriods (p := D.p) (q := secondPrime.q)
          D.m₁' D.m₂' E.m₃' E.tail) i :=
  secondReductionSource_nonOne_periods_ge_two
    secondPrime.hqPrime.two_le D.m₁' D.m₂' E.m₃' E.tail
    D.hm₁' D.hm₂' E.hm₃'
    (fun j => lt_of_lt_of_le (by decide : 0 < 2) (E.htail j))

theorem SecondStageCleanupPeriodData.source_nonOne_card_ge_three_of_firstHead
    {σ : FuchsianSignature} {D : FirstReductionPeriodData σ}
    {secondPrime : FirstKernelTailPrimeDivisorData D}
    (E : SecondStageCleanupPeriodData D secondPrime)
    (hm₁ne : D.m₁' ≠ 1) :
    3 ≤ Fintype.card
      (NonOneSubfamilyIndex
        (secondReductionSourcePeriods (p := D.p) (q := secondPrime.q)
          D.m₁' D.m₂' E.m₃' E.tail)) := by
  let periods :=
    secondReductionSourcePeriods (p := D.p) (q := secondPrime.q)
      D.m₁' D.m₂' E.m₃' E.tail
  have hqm_ne : secondPrime.q * E.m₃' ≠ 1 := by
    have hqge : 2 ≤ secondPrime.q * E.m₃' :=
      le_trans secondPrime.hqPrime.two_le
        (Nat.le_mul_of_pos_right secondPrime.q E.hm₃')
    omega
  let f : Fin 3 → NonOneSubfamilyIndex periods := fun i =>
    match i with
    | ⟨0, _⟩ =>
        ⟨.inl 0, by
          simpa [periods, secondReductionSourcePeriods, twoPeriods] using hm₁ne⟩
    | ⟨1, _⟩ =>
        ⟨.inr (.inl 0), by
          simpa [periods, secondReductionSourcePeriods] using hqm_ne⟩
    | ⟨2, _⟩ =>
        ⟨.inr (.inl 1), by
          simpa [periods, secondReductionSourcePeriods] using hqm_ne⟩
    | ⟨n + 3, hn⟩ => False.elim (by omega)
  have hf : Function.Injective f := by
    intro a b h
    fin_cases a <;> fin_cases b <;> first | rfl | cases h
  simpa using Fintype.card_le_of_injective f hf

end FenchelNielsen
