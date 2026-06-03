import Mathlib.GroupTheory.PresentedGroup
import ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/Presentations/Tietze/Core.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Tietze transformations

Presentation-level Tietze moves for adding and deleting generators, replacing relators, comparing quotient presentations, and recording executable Tietze scripts.
-/

universe u v w

namespace ReidemeisterSchreier.Discrete.Presentations

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- A reusable Tietze certificate between two presentations.  This is the
scriptable layer: certificates can be reversed and composed while retaining the
underlying normal-closure data. -/
structure TietzeEquiv
    {X Y : Type*} (R : Set (FreeGroup X)) (S : Set (FreeGroup Y)) where
  toMutualMapData : RelatorQuotientMutualMapData R S

namespace TietzeEquiv

variable {X Y Z : Type*}
variable {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
variable {T : Set (FreeGroup Z)}

def refl (R : Set (FreeGroup X)) : TietzeEquiv R R where
  toMutualMapData := RelatorQuotientMutualMapData.refl R

def symm (D : TietzeEquiv R S) : TietzeEquiv S R where
  toMutualMapData := D.toMutualMapData.symm

def trans (D₁ : TietzeEquiv R S) (D₂ : TietzeEquiv S T) :
    TietzeEquiv R T where
  toMutualMapData := D₁.toMutualMapData.trans D₂.toMutualMapData

def ofMutualMapData (D : RelatorQuotientMutualMapData R S) :
    TietzeEquiv R S where
  toMutualMapData := D

def ofRelatorEquivalent
    {R S : Set (FreeGroup X)}
    (hR_to_S : ∀ r ∈ R, RelatorEquivalent S r 1)
    (hS_to_R : ∀ s ∈ S, RelatorEquivalent R s 1) :
    TietzeEquiv R S where
  toMutualMapData :=
    relatorQuotientMutualMapDataOfRelatorEquivalent hR_to_S hS_to_R

def ofNormalClosureEq
    {R S : Set (FreeGroup X)}
    (h : Subgroup.normalClosure R = Subgroup.normalClosure S) :
    TietzeEquiv R S where
  toMutualMapData := relatorQuotientMutualMapDataOfNormalClosureEq h

def ofGeneratorMaps
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ r ∈ R,
        FreeGroup.lift toGenerator r ∈ Subgroup.normalClosure S)
    (hS :
      ∀ s ∈ S,
        FreeGroup.lift invGenerator s ∈ Subgroup.normalClosure R)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent R
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent S
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    TietzeEquiv R S :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfGeneratorMaps
      toGenerator invGenerator hR hS hinv_to hto_inv)

def ofGeneratorMapsRelatorEquivalent
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ r ∈ R,
        RelatorEquivalent S (FreeGroup.lift toGenerator r) 1)
    (hS :
      ∀ s ∈ S,
        RelatorEquivalent R (FreeGroup.lift invGenerator s) 1)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent R
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent S
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    TietzeEquiv R S :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfGeneratorMapsRelatorEquivalent
      toGenerator invGenerator hR hS hinv_to hto_inv)

/-- Tietze certificate from generator maps when both relator sets are indexed
unions.  Use this when a presentation has named relator families and each
family has its own calculation. -/
def ofGeneratorMapsRelatorEquivalent_iUnion
    {ι κ : Sort*}
    {R : ι → Set (FreeGroup X)} {S : κ → Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ i : ι, ∀ r ∈ R i,
        RelatorEquivalent (Set.iUnion S) (FreeGroup.lift toGenerator r) 1)
    (hS :
      ∀ k : κ, ∀ s ∈ S k,
        RelatorEquivalent (Set.iUnion R) (FreeGroup.lift invGenerator s) 1)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent (Set.iUnion R)
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent (Set.iUnion S)
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    TietzeEquiv (Set.iUnion R) (Set.iUnion S) :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfGeneratorMapsRelatorEquivalent_iUnion
      toGenerator invGenerator hR hS hinv_to hto_inv)

/-- Two-level family variant of `ofGeneratorMapsRelatorEquivalent_iUnion`. -/
def ofGeneratorMapsRelatorEquivalent_iUnion₂
    {ι κ : Sort*} {α : ι → Sort*} {β : κ → Sort*}
    {R : ∀ i : ι, α i → Set (FreeGroup X)}
    {S : ∀ k : κ, β k → Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ i : ι, ∀ a : α i, ∀ r ∈ R i a,
        RelatorEquivalent
          (Set.iUnion fun k : κ => Set.iUnion (S k))
          (FreeGroup.lift toGenerator r) 1)
    (hS :
      ∀ k : κ, ∀ b : β k, ∀ s ∈ S k b,
        RelatorEquivalent
          (Set.iUnion fun i : ι => Set.iUnion (R i))
          (FreeGroup.lift invGenerator s) 1)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent
          (Set.iUnion fun i : ι => Set.iUnion (R i))
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent
          (Set.iUnion fun k : κ => Set.iUnion (S k))
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    TietzeEquiv
      (Set.iUnion fun i : ι => Set.iUnion (R i))
      (Set.iUnion fun k : κ => Set.iUnion (S k)) :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfGeneratorMapsRelatorEquivalent_iUnion₂
      toGenerator invGenerator hR hS hinv_to hto_inv)

noncomputable def quotientEquiv (D : TietzeEquiv R S) :
    FreeGroup X ⧸ Subgroup.normalClosure R ≃*
      FreeGroup Y ⧸ Subgroup.normalClosure S :=
  quotientEquivOfRelatorQuotientMutualMapData R S D.toMutualMapData

noncomputable def presentedEquiv (D : TietzeEquiv R S) :
    PresentedGroup R ≃* PresentedGroup S :=
  quotientEquivOfRelatorQuotientMutualMapData R S D.toMutualMapData

end TietzeEquiv

def freeGroupPullbackRelatorTietzeEquiv
    {X Y : Type*} (e : FreeGroup X ≃* FreeGroup Y)
    (S : Set (FreeGroup Y)) :
    TietzeEquiv (freeGroupPullbackRelatorSet e S) S :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfNormalClosureMapEq
      (freeGroupPullbackRelatorSet e S) S e
      (map_normalClosure_freeGroupPullbackRelatorSet e S))

/-- A presentation packaged with its generator type.  This is a light wrapper
for writing long Tietze scripts whose intermediate presentations may have
different generator types. -/
structure Presentation where
  Generator : Type u
  relators : Set (FreeGroup Generator)

namespace Presentation

def ofRelators {X : Type u} (R : Set (FreeGroup X)) : Presentation.{u} where
  Generator := X
  relators := R

end Presentation

/-- A scriptable Tietze certificate between packaged presentations.  The data is
still exactly a `TietzeEquiv`; this wrapper only remembers the intermediate
presentation objects so long chains can be composed without unpacking generator
types by hand. -/
structure TietzeScript (P : Presentation.{u}) (Q : Presentation.{v}) where
  toTietzeEquiv : TietzeEquiv P.relators Q.relators

namespace TietzeScript

def ofTietzeEquiv {P : Presentation.{u}} {Q : Presentation.{v}}
    (D : TietzeEquiv P.relators Q.relators) :
    TietzeScript P Q where
  toTietzeEquiv := D

def ofMutualMapData {P : Presentation.{u}} {Q : Presentation.{v}}
    (D : RelatorQuotientMutualMapData P.relators Q.relators) :
    TietzeScript P Q :=
  ofTietzeEquiv (TietzeEquiv.ofMutualMapData D)

def refl (P : Presentation.{u}) : TietzeScript P P :=
  ofTietzeEquiv (TietzeEquiv.refl P.relators)

def symm {P : Presentation.{u}} {Q : Presentation.{v}}
    (D : TietzeScript P Q) :
    TietzeScript Q P :=
  ofTietzeEquiv D.toTietzeEquiv.symm

def trans {P : Presentation.{u}} {Q : Presentation.{v}}
    {U : Presentation.{w}}
    (D₁ : TietzeScript P Q) (D₂ : TietzeScript Q U) :
    TietzeScript P U :=
  ofTietzeEquiv (D₁.toTietzeEquiv.trans D₂.toTietzeEquiv)

noncomputable def presentedEquiv
    {P : Presentation.{u}} {Q : Presentation.{v}}
    (D : TietzeScript P Q) :
    PresentedGroup P.relators ≃* PresentedGroup Q.relators :=
  D.toTietzeEquiv.presentedEquiv

noncomputable def quotientEquiv
    {P : Presentation.{u}} {Q : Presentation.{v}}
    (D : TietzeScript P Q) :
    FreeGroup P.Generator ⧸ Subgroup.normalClosure P.relators ≃*
      FreeGroup Q.Generator ⧸ Subgroup.normalClosure Q.relators :=
  D.toTietzeEquiv.quotientEquiv

end TietzeScript

namespace TietzeEquiv

def toScript
    {X Y : Type*} {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (D : TietzeEquiv R S) :
    TietzeScript (Presentation.ofRelators R) (Presentation.ofRelators S) :=
  TietzeScript.ofTietzeEquiv D

end TietzeEquiv

end ReidemeisterSchreier.Discrete.Presentations
