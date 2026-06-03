import Mathlib.GroupTheory.QuotientGroup.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/RightQuotient.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Right quotients of groups

This file contains the group-theoretic right-coset quotient API used by both
discrete and profinite Reidemeister-Schreier constructions. It is mathlib-only:
topology, compactness, and open-subgroup sections are added in profinite files.
-/

namespace ReidemeisterSchreier

universe u

variable {G : Type u} [Group G]

/-- The right quotient `H \ G`, encoded by mathlib's right-coset relation. -/
abbrev RightQuotient (H : Subgroup G) :=
  Quotient (QuotientGroup.rightRel H)

/-- The right coset of an element modulo a subgroup. -/
def rightCoset (H : Subgroup G) (g : G) : RightQuotient H :=
  Quotient.mk'' g

/-- A right coset is the base coset exactly when its representative lies in the subgroup. -/
theorem rightCoset_eq_basepoint_iff_mem
    {H : Subgroup G} {g : G} :
    rightCoset H g = rightCoset H (1 : G) ↔ g ∈ H := by
  constructor
  · intro hg
    have hrel : QuotientGroup.rightRel H g 1 := Quotient.exact' hg
    have hginv : g⁻¹ ∈ H := by
      simpa using (QuotientGroup.rightRel_apply.mp hrel)
    simpa using H.inv_mem hginv
  · intro hg
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simpa using H.inv_mem hg

/-- Right multiplication on right cosets, expressed as a left action by
`g • [a] = [a * g⁻¹]`. -/
def rightCosetMulAction (H : Subgroup G) :
    MulAction G (RightQuotient H) where
  smul g :=
    Quotient.map' (fun a => a * g⁻¹) fun a b hab => by
      rw [QuotientGroup.rightRel_apply] at hab ⊢
      simpa [mul_assoc] using hab
  one_smul q := by
    refine Quotient.inductionOn' q ?_
    intro a
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simp only [inv_one, mul_one, mul_inv_cancel, one_mem]
  mul_smul g h q := by
    refine Quotient.inductionOn' q ?_
    intro a
    apply Quotient.sound'
    rw [QuotientGroup.rightRel_apply]
    simp only [mul_assoc, mul_inv_rev, inv_inv, inv_mul_cancel_left, mul_inv_cancel, one_mem]

@[simp] theorem rightCosetMulAction_mk_smul
    (H : Subgroup G) (g a : G) :
    letI := rightCosetMulAction H
    g • (Quotient.mk'' a : RightQuotient H) = Quotient.mk'' (a * g⁻¹) :=
  rfl

@[simp] theorem rightCosetMulAction_inv_mk_smul
    (H : Subgroup G) (g a : G) :
    letI := rightCosetMulAction H
    g⁻¹ • (Quotient.mk'' a : RightQuotient H) = Quotient.mk'' (a * g) := by
  rw [rightCosetMulAction_mk_smul (H := H) g⁻¹ a]
  simp only [inv_inv]

@[simp] theorem rightCosetMulAction_rightCoset_smul
    (H : Subgroup G) (g a : G) :
    letI := rightCosetMulAction H
    g • rightCoset H a = rightCoset H (a * g⁻¹) :=
  rightCosetMulAction_mk_smul H g a

@[simp] theorem rightCosetMulAction_inv_rightCoset_smul
    (H : Subgroup G) (g a : G) :
    letI := rightCosetMulAction H
    g⁻¹ • rightCoset H a = rightCoset H (a * g) :=
  rightCosetMulAction_inv_mk_smul H g a

/-- Right cosets are equivalent to the usual left quotient. -/
def rightQuotientEquivLeftQuotient (H : Subgroup G) :
    RightQuotient H ≃ G ⧸ H :=
  QuotientGroup.quotientRightRelEquivQuotientLeftRel H

end ReidemeisterSchreier
