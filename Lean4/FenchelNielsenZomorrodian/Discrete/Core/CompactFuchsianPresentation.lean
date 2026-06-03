import FenchelNielsenZomorrodian.Discrete.Core.Signature
import Mathlib.Algebra.Group.Commutator
import Mathlib.Data.Fintype.Sum
import Mathlib.GroupTheory.PresentedGroup

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Discrete/Core/CompactFuchsianPresentation.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete Fenchel and compact Fuchsian core definitions

Signatures, generator indices, presentations, elliptic generators, quotient homomorphisms, and family-signature transformations.
-/

open scoped BigOperators

namespace FenchelNielsen

structure FuchsianSignature extends FenchelSignature where
  numCusps_eq_zero : numCusps = 0
  numPeriods_ge_three : 3 ≤ numPeriods

inductive FuchsianGenerator (σ : FuchsianSignature)
  | elliptic : Fin σ.numPeriods → FuchsianGenerator σ
  | surfaceA : Fin σ.orbitGenus → FuchsianGenerator σ
  | surfaceB : Fin σ.orbitGenus → FuchsianGenerator σ

def FuchsianGenerator.equivSum (σ : FuchsianSignature) :
    FuchsianGenerator σ ≃ Fin σ.numPeriods ⊕ Fin σ.orbitGenus ⊕ Fin σ.orbitGenus where
  toFun
    | .elliptic i => .inl i
    | .surfaceA j => .inr (.inl j)
    | .surfaceB j => .inr (.inr j)
  invFun
    | .inl i => FuchsianGenerator.elliptic i
    | .inr (.inl j) => FuchsianGenerator.surfaceA j
    | .inr (.inr j) => FuchsianGenerator.surfaceB j
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x with
    | inl i => rfl
    | inr y =>
        cases y <;> rfl

instance FuchsianGenerator.instFintype (σ : FuchsianSignature) :
    Fintype (FuchsianGenerator σ) :=
  Fintype.ofEquiv (Fin σ.numPeriods ⊕ Fin σ.orbitGenus ⊕ Fin σ.orbitGenus)
    (FuchsianGenerator.equivSum σ).symm

def xWord (σ : FuchsianSignature) (i : Fin σ.numPeriods) :
    FreeGroup (FuchsianGenerator σ) :=
  FreeGroup.of <| FuchsianGenerator.elliptic i

def aWord (σ : FuchsianSignature) (j : Fin σ.orbitGenus) :
    FreeGroup (FuchsianGenerator σ) :=
  FreeGroup.of <| FuchsianGenerator.surfaceA j

def bWord (σ : FuchsianSignature) (j : Fin σ.orbitGenus) :
    FreeGroup (FuchsianGenerator σ) :=
  FreeGroup.of <| FuchsianGenerator.surfaceB j

def totalRelation (σ : FuchsianSignature) :
    FreeGroup (FuchsianGenerator σ) :=
  ((List.finRange σ.numPeriods).map fun i => xWord σ i).prod *
    ((List.finRange σ.orbitGenus).map fun j => ⁅aWord σ j, bWord σ j⁆).prod

def relators (σ : FuchsianSignature) : Set (FreeGroup (FuchsianGenerator σ)) :=
  {w | (∃ i : Fin σ.numPeriods, w = (xWord σ i) ^ σ.periods i) ∨ w = totalRelation σ}

abbrev FuchsianPresentedGroup (σ : FuchsianSignature) : Type :=
  PresentedGroup (relators σ)

instance instGroupFuchsianPresentedGroup (σ : FuchsianSignature) :
    Group (FuchsianPresentedGroup σ) :=
  inferInstance

end FenchelNielsen
