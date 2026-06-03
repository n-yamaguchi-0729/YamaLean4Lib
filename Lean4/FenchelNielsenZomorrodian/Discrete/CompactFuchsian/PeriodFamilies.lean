import FenchelNielsenZomorrodian.Discrete.Singerman.KernelTransport

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/CompactFuchsian/PeriodFamilies.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Compact Fuchsian proof infrastructure

Presentation-level compact Fuchsian period families and quotient constructions used in the FNZ profinite bridge.
-/

namespace FenchelNielsen

def twoPeriods {α : Type*} (a b : α) : Fin 2 → α :=
  Fin.cases a (fun _ => b)
@[simp 900] theorem twoPeriods_zero {α : Type*} (a b : α) :
    twoPeriods a b 0 = a := rfl
@[simp 900] theorem twoPeriods_one {α : Type*} (a b : α) :
    twoPeriods a b 1 = b := rfl
@[simp 900] theorem fin_cases_const_one {α : Type*} (a b : α) :
    Fin.cases a (fun _ : Fin 1 => b) 1 = b := rfl
abbrev OriginalFirstReductionIndex (tailLen : ℕ) := Sum (Fin 2) (Fin tailLen)
def originalFirstReductionPeriods {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) :
    OriginalFirstReductionIndex tailLen → ℕ
  | .inl i => twoPeriods (p * m₁') (p * m₂') i
  | .inr j => tail j
abbrev FirstReductionIndex (tailLen p : ℕ) := Sum (Fin 2) (Fin tailLen × Fin p)
def firstReductionPeriods {tailLen p : ℕ}
    (m₁' m₂' : ℕ) (tail : Fin tailLen → ℕ) :
    FirstReductionIndex tailLen p → ℕ
  | .inl i => twoPeriods m₁' m₂' i
  | .inr jk => tail jk.1
abbrev FirstSecondInputIndex (tailLen p : ℕ) := Sum (Fin 2) (Sum (Fin p) (Fin tailLen × Fin p))
abbrev SecondReductionSourceIndex (tailLen p : ℕ) :=
  Sum (Fin 2) (Sum (Fin 2) (Sum (Fin (p - 2)) (Fin tailLen × Fin p)))
def secondReductionSourcePeriods {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ) :
    SecondReductionSourceIndex tailLen p → ℕ
  | .inl i => twoPeriods m₁' m₂' i
  | .inr (.inl _) => q * m₃'
  | .inr (.inr (.inl _)) => q * m₃'
  | .inr (.inr (.inr jk)) => tail jk.1
def secondReductionSourceCycleCount {tailLen p q : ℕ} :
    SecondReductionSourceIndex tailLen p → ℕ
  | .inl _ => q
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => q
  | .inr (.inr (.inr _)) => q
def secondReductionSourceTransportPeriods {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ) :
    ∀ i : SecondReductionSourceIndex tailLen p,
      Fin (secondReductionSourceCycleCount (q := q) i) → ℕ
  | .inl i, _ => twoPeriods m₁' m₂' i
  | .inr (.inl _), _ => m₃'
  | .inr (.inr (.inl _)), _ => q * m₃'
  | .inr (.inr (.inr jk)), _ => tail jk.1
abbrev SecondReductionTransportIndex (tailLen p q : ℕ) :=
  Σ i : SecondReductionSourceIndex tailLen p,
    Fin (secondReductionSourceCycleCount (tailLen := tailLen) (p := p) (q := q) i)
abbrev secondReductionTransportPeriods {tailLen p q : ℕ}
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ) :
    SecondReductionTransportIndex tailLen p q → ℕ :=
  singermanTransportPeriodsFamily
    (secondReductionSourceTransportPeriods (p := p) (q := q) m₁' m₂' m₃' tail)
theorem secondReductionTransport_hasEqualPartnerFamily
    {tailLen p q : ℕ} (hq : 2 ≤ q)
    (m₁' m₂' m₃' : ℕ) (tail : Fin tailLen → ℕ) :
    HasEqualPartnerFamily (secondReductionTransportPeriods (p := p) (q := q) m₁' m₂' m₃' tail) := by
  intro x
  rcases x with ⟨i, k⟩
  cases i with
  | inl i =>
      refine ⟨⟨.inl i, finPartner hq k⟩, ?_, ?_⟩
      · intro h
        have hk : finPartner hq k = k := by
          simpa using eq_of_heq (Sigma.mk.inj_iff.mp h).2
        exact finPartner_ne hq k hk
      · rfl
  | inr s =>
      cases s with
      | inl j =>
          refine ⟨⟨.inr (.inl (finPartner (by decide : 2 ≤ 2) j)),
              by simpa [secondReductionSourceCycleCount] using (0 : Fin 1)⟩, ?_, ?_⟩
          · intro h
            have hj : finPartner (by decide : 2 ≤ 2) j = j := by
              simpa using (Sigma.mk.inj_iff.mp h).1
            exact finPartner_ne (by decide : 2 ≤ 2) j hj
          · rfl
      | inr s =>
          cases s with
          | inl j =>
              refine ⟨⟨.inr (.inr (.inl j)), finPartner hq k⟩, ?_, ?_⟩
              · intro h
                have hk : finPartner hq k = k := by
                  simpa using eq_of_heq (Sigma.mk.inj_iff.mp h).2
                exact finPartner_ne hq k hk
              · rfl
          | inr jk =>
              refine ⟨⟨.inr (.inr (.inr jk)), finPartner hq k⟩, ?_, ?_⟩
              · intro h
                have hk : finPartner hq k = k := by
                  simpa using eq_of_heq (Sigma.mk.inj_iff.mp h).2
                exact finPartner_ne hq k hk
              · rfl

end FenchelNielsen
