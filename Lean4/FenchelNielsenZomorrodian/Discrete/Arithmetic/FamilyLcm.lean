import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Arithmetic/FamilyLcm.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Arithmetic of period families

GCD, LCM, prime-divisor, replicated-family, and abelian-period numerical lemmas used in compact zero-genus reductions.
-/

open scoped BigOperators

namespace FenchelNielsen

def otherPeriodsLcmFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (periods : ι → ℕ) (i : ι) : ℕ :=
  (Finset.univ.erase i).lcm periods

def otherPeriodsProductFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (periods : ι → ℕ) (i : ι) : ℕ :=
  (Finset.univ.erase i).prod periods

def finZeroOfTwoLe {n : ℕ} (hn : 2 ≤ n) : Fin n :=
  ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩

def finOneOfTwoLe {n : ℕ} (hn : 2 ≤ n) : Fin n :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hn⟩

def finPartner {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : Fin n :=
  if _ : i = finZeroOfTwoLe hn then
    finOneOfTwoLe hn
  else
    finZeroOfTwoLe hn

theorem finPartner_ne {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    finPartner hn i ≠ i := by
  by_cases hi : i = finZeroOfTwoLe hn
  · subst hi
    intro h
    simp only [finPartner, finZeroOfTwoLe, ↓reduceDIte, finOneOfTwoLe, Fin.mk.injEq, one_ne_zero] at h
  · intro h
    have hzero : finZeroOfTwoLe hn = i := by
      simpa [finPartner, hi] using h
    exact hi hzero.symm

def LCMConditionFamily {ι : Type*} [Fintype ι] [DecidableEq ι]
    (periods : ι → ℕ) : Prop :=
  ∀ i, periods i ∣ otherPeriodsLcmFamily periods i

theorem LCMConditionFamily.reindex_iff
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) {periods : α → ℕ} :
    LCMConditionFamily (fun b : β => periods (e.symm b)) ↔
      LCMConditionFamily periods := by
  let reindexed : β → ℕ := fun b => periods (e.symm b)
  have hOther (a : α) :
      otherPeriodsLcmFamily reindexed (e a) =
        otherPeriodsLcmFamily periods a := by
    rw [otherPeriodsLcmFamily, otherPeriodsLcmFamily]
    have himage :
        ((Finset.univ.erase (e a) : Finset β).image e.symm) =
          (Finset.univ.erase a : Finset α) := by
      ext x
      simp only [Finset.mem_image, Finset.mem_erase, ne_eq, Finset.mem_univ, and_true, Equiv.symm_apply_eq,
  exists_eq_right, EmbeddingLike.apply_eq_iff_eq]
    calc
      (Finset.univ.erase (e a) : Finset β).lcm reindexed
          = (Finset.univ.erase (e a) : Finset β).lcm (periods ∘ e.symm) := rfl
      _ = ((Finset.univ.erase (e a) : Finset β).image e.symm).lcm periods :=
          (Finset.lcm_image (f := periods) (g := e.symm)
            (s := (Finset.univ.erase (e a) : Finset β))).symm
      _ = (Finset.univ.erase a : Finset α).lcm periods := by rw [himage]
  constructor
  · intro h a
    have hdiv :
        periods a ∣
          otherPeriodsLcmFamily reindexed (e a) := by
      simpa [reindexed] using h (e a)
    simpa [reindexed, hOther a] using hdiv
  · intro h b
    have hdiv :
        reindexed b ∣ otherPeriodsLcmFamily reindexed (e (e.symm b)) := by
      have hbase := h (e.symm b)
      rw [← hOther (e.symm b)] at hbase
      simpa [reindexed] using hbase
    simpa [reindexed] using hdiv

def HasEqualPartnerFamily {ι : Type*}
    (periods : ι → ℕ) : Prop :=
  ∀ i, ∃ j, j ≠ i ∧ periods j = periods i

theorem lcmConditionFamily_of_hasEqualPartnerFamily
    {ι : Type*} [Fintype ι] [DecidableEq ι] {periods : ι → ℕ}
    (hperiods : HasEqualPartnerFamily periods) : LCMConditionFamily periods := by
  intro i
  rcases hperiods i with ⟨j, hji, hjEq⟩
  have hj : j ∈ (Finset.univ.erase i : Finset ι) := by
    exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  rw [otherPeriodsLcmFamily]
  rw [← hjEq]
  exact Finset.dvd_lcm hj

theorem otherPeriodsLcmFamily_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι] {periods : ι → ℕ}
    (hpos : ∀ i, 0 < periods i) (i : ι) :
    0 < otherPeriodsLcmFamily periods i := by
  rw [Nat.pos_iff_ne_zero, otherPeriodsLcmFamily]
  exact
    (Finset.lcm_ne_zero_iff).2
      (fun j _ => Nat.ne_of_gt (hpos j))

abbrev NonOneSubfamilyIndex {ι : Type*} (periods : ι → ℕ) :=
  {i : ι // periods i ≠ 1}

def nonOneSubfamilyPeriods {ι : Type*} (periods : ι → ℕ)
    (i : NonOneSubfamilyIndex periods) : ℕ :=
  periods i.1

theorem nonOneSubfamilyPeriods_ge_two
    {ι : Type*} (periods : ι → ℕ) (hpos : ∀ i, 0 < periods i) :
    ∀ i : NonOneSubfamilyIndex periods, 2 ≤ nonOneSubfamilyPeriods periods i := by
  intro i
  have hiPos : 0 < periods i.1 := hpos i.1
  have hiNe : periods i.1 ≠ 1 := i.2
  dsimp [nonOneSubfamilyPeriods]
  omega

end FenchelNielsen
