import Mathlib.Algebra.Group.PUnit
import Mathlib.GroupTheory.QuotientGroup.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FiniteGroups/Classes.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite group classes

Defines finite group classes and their standard closure properties: quotients, finite subdirect products, subgroups, extensions, formations, and standard examples.
-/

namespace ProCGroups

universe u v

/-- A class of groups, implemented as an unbundled predicate on group carriers. -/
abbrev GroupClass := ∀ (G : Type u) [Group G], Prop

/-- A class of finite groups.

The public API bundles the predicate with the proof that every member is finite.  The coercion
below keeps the usual `C G` spelling for membership. -/
structure FiniteGroupClass where
  pred : GroupClass.{u}
  finite_of_mem : ∀ {G : Type u} [Group G], pred G → Finite G

instance instCoeFunFiniteGroupClass : CoeFun FiniteGroupClass (fun _ => GroupClass.{u}) where
  coe C := C.pred

namespace FiniteGroupClass

/-- The class only contains finite groups. -/
def FiniteOnly (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {G : Type u} [Group G], C G → Finite G

/-- Members of a bundled finite-group class are finite. -/
theorem finite {C : FiniteGroupClass.{u}} {G : Type u} [Group G] (hG : C G) : Finite G :=
  C.finite_of_mem hG

/-- The finite-only predicate follows from the bundled class data. -/
theorem finiteOnly (C : FiniteGroupClass.{u}) : FiniteOnly C :=
  fun hG => C.finite hG

/-- The finite-group class contains all trivial groups.

This is the class-level form needed when a construction indexes over quotients and must include
the terminal quotient.  Formations provide this automatically via `Formation.one_mem`; users of a
formation should not add a separate hypothesis. -/
class ContainsTrivialQuotients (C : FiniteGroupClass.{u}) : Prop where
  of_subsingleton : ∀ {Q : Type u} [Group Q], Subsingleton Q → C Q

/-- 1 (closure under isomorphism). -/
def IsomClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {G H : Type u} [Group G] [Group H], Nonempty (G ≃* H) → C G → C H

/-- Closed under taking subgroups. -/
def SubgroupClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {G : Type u} [Group G] (H : Subgroup G), C G → C H

/-- Closed under taking normal subgroups. -/
def NormalSubgroupClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {G : Type u} [Group G] (N : Subgroup G) [N.Normal], C G → C N

/-- Closed under taking quotients. -/
def QuotientClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {G : Type u} [Group G] (N : Subgroup G) [N.Normal], C G → C (G ⧸ N)

/-- Closed under forming finite direct products. -/
def FiniteProductClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {ι : Type u} [Fintype ι] {G : ι → Type u} [∀ i, Group (G i)],
    (∀ i, C (G i)) → C (∀ i, G i)

/-- Closed under forming finite subdirect products.

We package a finite subdirect product as an injective homomorphism into a finite product whose
coordinate maps are all surjective.
-/
def FiniteSubdirectProductClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {ι : Type u} [Fintype ι] {G : Type u} [Group G]
    {H : ι → Type u} [∀ i, Group (H i)],
    (f : G →* ∀ i, H i) →
    Function.Injective f →
    (∀ i, Function.Surjective fun g : G => f g i) →
    (∀ i, C (H i)) →
    C G

/-- Closed under extensions. -/
def ExtensionClosed (C : FiniteGroupClass.{u}) : Prop :=
  ∀ {E : Type u} [Group E] (N : Subgroup E) [N.Normal],
    C N → C (E ⧸ N) → C E

/-- A formation of finite groups.

Standard formation terminology starts with a family of finite groups containing the trivial group and then asks for
closure under quotients and finite fiber/subdirect products. In this unbundled predicate API the
trivial group condition is a theorem, `Formation.one_mem`, because it follows from the empty finite
subdirect product. -/
structure Formation (C : FiniteGroupClass.{u}) : Prop where
  quotientClosed : QuotientClosed C
  finiteSubdirectProductClosed : FiniteSubdirectProductClosed C

/-- A variety of finite groups. -/
structure Variety (C : FiniteGroupClass.{u}) : Prop where
  subgroupClosed : SubgroupClosed C
  quotientClosed : QuotientClosed C
  finiteProductClosed : FiniteProductClosed C

/-- A Melnikov formation of finite groups.

A Melnikov formation includes the underlying formation field directly, rather than
re-proving it at every use site, so the standard formation API (including `Formation.one_mem`) is
available immediately. -/
structure MelnikovFormation (C : FiniteGroupClass.{u}) : Prop where
  formation : Formation C
  normalSubgroupClosed : NormalSubgroupClosed C
  extensionClosed : ExtensionClosed C

/-- A finite-group class is hereditary when it is closed under injective homomorphisms.

This is the form used by finite-quotient comap constructions: a pullback quotient embeds into the
target finite quotient, so membership descends along injections. -/
structure Hereditary (C : FiniteGroupClass.{u}) : Prop where
  of_injective :
    ∀ {G H : Type u} [Group G] [Group H],
      C H → (f : G →* H) → Function.Injective f → C G

/-- A full formation of finite groups.

Equivalently, this is a Melnikov formation whose finite groups are closed under subgroups. The
`Hereditary` injective-hom formulation is derived as `FullFormation.hereditary`. -/
structure FullFormation (C : FiniteGroupClass.{u}) : Prop where
  melnikovFormation : MelnikovFormation C
  subgroupClosed : SubgroupClosed C

/-- Typeclass wrapper for a finite-group formation.

Use this when a theorem only needs the closure package for a fixed finite class and should not
carry a separate `hForm : Formation C` argument everywhere. -/
class IsFormation (C : FiniteGroupClass.{u}) : Prop where
  formation : Formation C

/-- Typeclass wrapper for a Melnikov formation. -/
class IsMelnikovFormation (C : FiniteGroupClass.{u}) : Prop where
  melnikovFormation : MelnikovFormation C

/-- Typeclass wrapper for a full formation. -/
class IsFullFormation (C : FiniteGroupClass.{u}) : Prop where
  fullFormation : FullFormation C

/-- Bundled finite-group formation data, useful when the class itself should travel as data. -/
structure FiniteFormation where
  C : FiniteGroupClass.{u}
  formation : Formation C

/-- Bundled full finite-group formation data. -/
structure FullFiniteFormation where
  C : FiniteGroupClass.{u}
  fullFormation : FullFormation C

/-- A Melnikov formation typeclass supplies the underlying formation typeclass. -/
@[instance 100]
def isFormation_of_isMelnikovFormation
    (C : FiniteGroupClass.{u}) [hC : IsMelnikovFormation C] :
    IsFormation C where
  formation := hC.melnikovFormation.formation

/-- A full formation typeclass supplies the underlying Melnikov formation typeclass. -/
@[instance 100]
def isMelnikovFormation_of_isFullFormation
    (C : FiniteGroupClass.{u}) [hC : IsFullFormation C] :
    IsMelnikovFormation C where
  melnikovFormation := hC.fullFormation.melnikovFormation

/-- Formation members are finite because the underlying class is bundled as finite-only. -/
theorem Formation.finiteOnly {C : FiniteGroupClass.{u}} (_hForm : Formation C) :
    FiniteOnly C :=
  C.finiteOnly

/-- Variety members are finite because the underlying class is bundled as finite-only. -/
theorem Variety.finiteOnly {C : FiniteGroupClass.{u}} (_hVar : Variety C) :
    FiniteOnly C :=
  C.finiteOnly

/-- Every formation is closed under isomorphisms. -/
theorem Formation.isomClosed {C : FiniteGroupClass.{u}} (hForm : Formation C) :
    IsomClosed C := by
  intro G H _ _ hGH hCG
  rcases hGH with ⟨e⟩
  let f : H →* (PUnit → G) :=
    { toFun := fun h _ => e.symm h
      map_one' := by
        ext i
        cases i
        simp only [map_one, Pi.one_apply]
      map_mul' := by
        intro x y
        ext i
        cases i
        simp only [map_mul, Pi.mul_apply]}
  have hf : Function.Injective f := by
    intro x y hxy
    exact e.symm.injective (by simpa [f] using congrFun hxy PUnit.unit)
  have hsurj : ∀ i : PUnit, Function.Surjective fun h : H => f h i := by
    intro i g
    refine ⟨e g, ?_⟩
    cases i
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.symm_apply_apply, f]
  exact hForm.finiteSubdirectProductClosed f hf hsurj (fun _ => hCG)

/-- Every formation is closed under finite direct products. -/
theorem Formation.finiteProductClosed {C : FiniteGroupClass.{u}}
    (hForm : Formation C) : FiniteProductClosed C := by
  classical
  intro ι _ G _ hG
  let f : (∀ i, G i) →* ∀ i, G i := MonoidHom.id _
  refine hForm.finiteSubdirectProductClosed f ?_ ?_ hG
  · intro x y hxy
    simpa [f] using hxy
  · intro i y
    refine ⟨Function.update 1 i y, ?_⟩
    simp only [MonoidHom.id_apply, Function.update_self, f]

/-- Every formation contains the trivial group.

This is the standard `containing the trivial group` clause. In this API it is derived from the empty
finite subdirect product, so users should pass only `Formation C`, not a separate `C PUnit`
hypothesis. -/
theorem Formation.one_mem {C : FiniteGroupClass.{u}} (hForm : Formation C) :
    C PUnit := by
  let G : PEmpty → Type u := fun _ => PUnit
  letI : ∀ i : PEmpty, Group (G i) := by
    intro i
    cases i
  let e : ((i : PEmpty) → G i) ≃* PUnit := by
    refine
      { toFun := fun _ => PUnit.unit
        invFun := fun _ i => nomatch i
        left_inv := ?_
        right_inv := ?_
        map_mul' := ?_ }
    · intro x
      ext i
    · intro x
      cases x
      rfl
    · intro x y
      rfl
  have hProd : C ((i : PEmpty) → G i) :=
    hForm.finiteProductClosed (ι := PEmpty) (G := G) (fun i => by cases i)
  exact hForm.isomClosed ⟨e⟩ hProd

/-- Use a specified multiplicative equivalence to transport membership in an isomorphism-closed
finite-group class. -/
theorem IsomClosed.of_mulEquiv {C : FiniteGroupClass.{u}}
    (hIso : IsomClosed C) {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : C G) :
    C H :=
  hIso ⟨e⟩ hG

/-- Membership in an isomorphism-closed finite-group class is invariant under a specified
multiplicative equivalence. -/
theorem IsomClosed.iff_of_mulEquiv {C : FiniteGroupClass.{u}}
    (hIso : IsomClosed C) {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) :
    C G ↔ C H :=
  ⟨hIso.of_mulEquiv e, hIso.of_mulEquiv e.symm⟩

/-- An isomorphism-closed class containing the trivial group contains every trivial group. -/
theorem containsTrivialQuotients_of_isomClosed_one_mem {C : FiniteGroupClass.{u}}
    (hIso : IsomClosed C) (hOne : C PUnit) :
    ContainsTrivialQuotients C := by
  refine ⟨?_⟩
  intro Q _ hQ
  letI : Subsingleton Q := hQ
  let e : PUnit ≃* Q :=
    { toFun := fun _ => 1
      invFun := fun _ => PUnit.unit
      left_inv := by
        intro x
        cases x
        rfl
      right_inv := by
        intro q
        exact Subsingleton.elim _ _
      map_mul' := by
        intro x y
        exact Subsingleton.elim _ _ }
  exact hIso ⟨e⟩ hOne

/-- Every formation contains the trivial quotients. -/
theorem Formation.containsTrivialQuotients {C : FiniteGroupClass.{u}}
    (hForm : Formation C) :
    ContainsTrivialQuotients C :=
  containsTrivialQuotients_of_isomClosed_one_mem hForm.isomClosed hForm.one_mem

/-- Any isomorphism-closed subgroup-closed class that is closed under finite direct products is
also closed under finite subdirect products. -/
theorem finiteSubdirectProductClosed_of_isomClosed_subgroupClosed_finiteProductClosed
    {C : FiniteGroupClass.{u}}
    (hIso : IsomClosed C)
    (hSub : SubgroupClosed C)
    (hProd : FiniteProductClosed C) :
    FiniteSubdirectProductClosed C := by
  intro ι _ G _ H _ f hf _hsurj hH
  have hPi : C (∀ i, H i) := hProd hH
  have hRange : C f.range := hSub f.range hPi
  have hRangeRestrictInj : Function.Injective f.rangeRestrict := by
    intro x y hxy
    exact hf (by simpa using congrArg Subtype.val hxy)
  let e : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨hRangeRestrictInj, f.rangeRestrict_surjective⟩
  exact hIso ⟨e.symm⟩ hRange

/-- An isomorphism-closed variety contains the trivial group. -/
theorem variety_one_mem_of_isomClosed {C : FiniteGroupClass.{u}}
    (hVar : Variety C) (hIso : IsomClosed C) :
    C PUnit := by
  let G : PEmpty → Type u := fun _ => PUnit
  letI : ∀ i : PEmpty, Group (G i) := by
    intro i
    cases i
  let e : ((i : PEmpty) → G i) ≃* PUnit := by
    classical
    refine
      { toFun := fun _ => PUnit.unit
        invFun := fun _ i => nomatch i
        left_inv := ?_
        right_inv := ?_
        map_mul' := ?_ }
    · intro x
      ext i
    · intro x
      cases x
      rfl
    · intro x y
      rfl
  have hProd : C ((i : PEmpty) → G i) :=
    hVar.finiteProductClosed (ι := PEmpty) (G := G) (fun i => by cases i)
  exact hIso ⟨e⟩ hProd

/-- Any subgroup-closed isomorphism-closed class that contains one group also contains the trivial
group. -/
theorem one_mem_of_subgroupClosed_isomClosed {C : FiniteGroupClass.{u}}
    (hSub : SubgroupClosed C) (hIso : IsomClosed C)
    {G : Type u} [Group G] (hG : C G) :
    C PUnit := by
  let eBot : (⊥ : Subgroup G) ≃* PUnit :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => 1
      left_inv := by
        intro x
        exact Subsingleton.elim _ _
      right_inv := by
        intro x
        cases x
        rfl
      map_mul' := by
        intro x y
        rfl }
  exact hIso ⟨eBot⟩ (hSub (⊥ : Subgroup G) hG)

/-- Subgroup- and isomorphism-closure imply the injective-hom hereditary form. -/
theorem Hereditary.of_subgroupClosed_isomClosed {C : FiniteGroupClass.{u}}
    (hSub : SubgroupClosed C) (hIso : IsomClosed C) :
    Hereditary C := by
  refine ⟨?_⟩
  intro G H _ _ hH f hf
  have hRange : C f.range := hSub f.range hH
  let e : G ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨by
      intro x y hxy
      exact hf (by simpa using congrArg Subtype.val hxy),
    f.rangeRestrict_surjective⟩
  exact hIso ⟨e.symm⟩ hRange

/-- Hereditary classes are subgroup-closed. -/
theorem Hereditary.subgroupClosed {C : FiniteGroupClass.{u}}
    (hHer : Hereditary C) :
    SubgroupClosed C := by
  intro G _ H hG
  exact hHer.of_injective hG H.subtype Subtype.val_injective

/-- Hereditary finite-group classes are invariant under multiplicative equivalence. -/
theorem Hereditary.of_mulEquiv {C : FiniteGroupClass.{u}}
    (hHer : Hereditary C) {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hH : C H) :
    C G :=
  hHer.of_injective hH e.toMonoidHom e.injective

/-- Membership in a hereditary finite-group class is invariant under a specified multiplicative
equivalence. -/
theorem Hereditary.iff_of_mulEquiv {C : FiniteGroupClass.{u}}
    (hHer : Hereditary C) {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) :
    C G ↔ C H :=
  ⟨fun hG => hHer.of_mulEquiv e.symm hG, fun hH => hHer.of_mulEquiv e hH⟩

/-- Members of a Melnikov formation are finite. -/
theorem MelnikovFormation.finiteOnly {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C) : FiniteOnly C :=
  hC.formation.finiteOnly

/-- A Melnikov formation is quotient-closed. -/
theorem MelnikovFormation.quotientClosed {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C) : QuotientClosed C :=
  hC.formation.quotientClosed

/-- A Melnikov formation contains the trivial group. -/
theorem MelnikovFormation.one_mem {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C) : C PUnit :=
  hC.formation.one_mem

/-- A Melnikov formation contains the trivial quotients. -/
theorem MelnikovFormation.containsTrivialQuotients {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C) :
    ContainsTrivialQuotients C :=
  hC.formation.containsTrivialQuotients

/-- A Melnikov formation is isomorphism-closed. -/
theorem MelnikovFormation.isomClosed {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C) : IsomClosed C :=
  hC.formation.isomClosed

/-- Members of a full formation are finite. -/
theorem FullFormation.finiteOnly {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : FiniteOnly C :=
  hC.melnikovFormation.finiteOnly

/-- A full formation is quotient-closed. -/
theorem FullFormation.quotientClosed {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : QuotientClosed C :=
  hC.melnikovFormation.quotientClosed

/-- A full formation contains the trivial group. -/
theorem FullFormation.one_mem {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : C PUnit :=
  hC.melnikovFormation.one_mem

/-- A full formation contains the trivial quotients. -/
theorem FullFormation.containsTrivialQuotients {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) :
    ContainsTrivialQuotients C :=
  hC.melnikovFormation.containsTrivialQuotients

/-- A full formation is isomorphism-closed. -/
theorem FullFormation.isomClosed {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : IsomClosed C :=
  hC.melnikovFormation.isomClosed

/-- A full formation is closed under normal subgroups. -/
theorem FullFormation.normalSubgroupClosed {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : NormalSubgroupClosed C :=
  hC.melnikovFormation.normalSubgroupClosed

/-- A full formation is extension-closed. -/
theorem FullFormation.extensionClosed {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : ExtensionClosed C :=
  hC.melnikovFormation.extensionClosed

/-- The subgroup-closed part of a full formation, in the injective-hom form used by finite
quotient pullbacks. -/
theorem FullFormation.hereditary {C : FiniteGroupClass.{u}}
    (hC : FullFormation C) : Hereditary C :=
  Hereditary.of_subgroupClosed_isomClosed hC.subgroupClosed hC.isomClosed

/-- An isomorphism-closed variety is a formation in the unbundled `FiniteGroupClass` API. -/
theorem variety_formation {C : FiniteGroupClass.{u}}
    (hVar : Variety C) (hIso : IsomClosed C) :
    Formation C := by
  refine ⟨hVar.quotientClosed, ?_⟩
  exact finiteSubdirectProductClosed_of_isomClosed_subgroupClosed_finiteProductClosed
    hIso hVar.subgroupClosed hVar.finiteProductClosed

/-- A variety together with extension-closure packages the standard finite-class closure
hypotheses used by the pro-`C` API. -/
theorem Variety.closureBundle_of_isomClosed_extensionClosed {C : FiniteGroupClass.{u}}
    (hVar : Variety C)
    (hIso : IsomClosed C)
    (hExt : ExtensionClosed C) :
    Formation C ∧ SubgroupClosed C ∧ IsomClosed C ∧ QuotientClosed C ∧ ExtensionClosed C := by
  exact ⟨variety_formation hVar hIso, hVar.subgroupClosed, hIso, hVar.quotientClosed, hExt⟩

/-- For a Melnikov formation, the quotients by two normal subgroups lying in the
class force the quotient by their intersection to lie in the class as well. -/
theorem MelnikovFormation.quotient_inf_mem {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C)
    {G : Type u} [Group G]
    (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal]
    (h₁ : C (G ⧸ N₁)) (h₂ : C (G ⧸ N₂)) :
    C (G ⧸ (N₁ ⊓ N₂)) := by
  let E : Type u := G ⧸ (N₁ ⊓ N₂)
  let L : Subgroup E := Subgroup.map (QuotientGroup.mk' (N₁ ⊓ N₂)) N₁
  letI : L.Normal := by
    dsimp [L]
    exact Subgroup.Normal.map (show N₁.Normal by infer_instance)
      (QuotientGroup.mk' (N₁ ⊓ N₂))
      (QuotientGroup.mk'_surjective (N₁ ⊓ N₂))
  have hQuotL : C (E ⧸ L) := by
    let e : E ⧸ L ≃* G ⧸ N₁ :=
      QuotientGroup.quotientQuotientEquivQuotient (N₁ ⊓ N₂) N₁ inf_le_left
    exact hC.isomClosed ⟨e.symm⟩ h₁
  let K₂ : Subgroup (G ⧸ N₂) := Subgroup.map (QuotientGroup.mk' N₂) N₁
  letI : K₂.Normal := by
    dsimp [K₂]
    exact Subgroup.Normal.map (show N₁.Normal by infer_instance)
      (QuotientGroup.mk' N₂)
      (QuotientGroup.mk'_surjective N₂)
  have hK₂ : C K₂ := hC.normalSubgroupClosed K₂ h₂
  let ψ₂ : N₁ →* G ⧸ N₂ := (QuotientGroup.mk' N₂).comp N₁.subtype
  have hψ₂range : ψ₂.range = K₂ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hψ₂ker : ψ₂.ker = N₂.subgroupOf N₁ := by
    ext x
    change QuotientGroup.mk' N₂ x.1 = 1 ↔ x.1 ∈ N₂
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff (N := N₂) x.1]
  have hQuotN₁ : C (N₁ ⧸ N₂.subgroupOf N₁) := by
    let e₀ : N₁ ⧸ N₂.subgroupOf N₁ ≃* N₁ ⧸ ψ₂.ker :=
      QuotientGroup.quotientMulEquivOfEq hψ₂ker.symm
    let e₁ : N₁ ⧸ ψ₂.ker ≃* ψ₂.range := QuotientGroup.quotientKerEquivRange ψ₂
    let e₂ : ψ₂.range ≃* K₂ := MulEquiv.subgroupCongr hψ₂range
    exact hC.isomClosed ⟨((e₀.trans e₁).trans e₂).symm⟩ hK₂
  let ψ₁ : N₁ →* E := (QuotientGroup.mk' (N₁ ⊓ N₂)).comp N₁.subtype
  have hψ₁range : ψ₁.range = L := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hψ₁ker : ψ₁.ker = N₂.subgroupOf N₁ := by
    ext x
    change QuotientGroup.mk' (N₁ ⊓ N₂) x.1 = 1 ↔ x.1 ∈ N₂
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := N₁ ⊓ N₂) x.1).1 hx |>.2
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := N₁ ⊓ N₂) x.1).2 ⟨x.2, hx⟩
  have hL : C L := by
    let e₀ : N₁ ⧸ N₂.subgroupOf N₁ ≃* N₁ ⧸ ψ₁.ker :=
      QuotientGroup.quotientMulEquivOfEq hψ₁ker.symm
    let e₁ : N₁ ⧸ ψ₁.ker ≃* ψ₁.range := QuotientGroup.quotientKerEquivRange ψ₁
    let e₂ : ψ₁.range ≃* L := MulEquiv.subgroupCongr hψ₁range
    exact hC.isomClosed ⟨(e₀.trans e₁).trans e₂⟩ hQuotN₁
  exact hC.extensionClosed L hL hQuotL

/-- A Melnikov formation with subgroup closure gives the standard finite-class closure bundle. -/
theorem MelnikovFormation.closureBundle_of_subgroupClosed {C : FiniteGroupClass.{u}}
    (hC : MelnikovFormation C)
    (hSub : SubgroupClosed C) :
    Formation C ∧ SubgroupClosed C ∧ IsomClosed C ∧ QuotientClosed C ∧ ExtensionClosed C := by
  exact ⟨hC.formation, hSub, hC.isomClosed, hC.quotientClosed, hC.extensionClosed⟩

/-- For a formation, the quotient by the intersection of two normal subgroups whose
individual quotients lie in `C` also lies in `C`. This is the two-factor form of (C4). -/
theorem Formation.quotient_inf_mem {C : FiniteGroupClass.{u}}
    (hC : Formation C) {G : Type u} [Group G]
    (N₁ N₂ : Subgroup G) [N₁.Normal] [N₂.Normal]
    (h₁ : C (G ⧸ N₁)) (h₂ : C (G ⧸ N₂)) :
    C (G ⧸ (N₁ ⊓ N₂)) := by
  classical
  let H : ULift Bool → Type u
    | ⟨false⟩ => G ⧸ N₁
    | ⟨true⟩ => G ⧸ N₂
  letI : ∀ b : ULift Bool, Group (H b) := by
    intro b
    cases b with
    | up b =>
        cases b <;> infer_instance
  let f : G ⧸ (N₁ ⊓ N₂) →* ∀ b : ULift Bool, H b :=
    { toFun := fun x b =>
        match b with
        | ⟨false⟩ => QuotientGroup.map (N₁ ⊓ N₂) N₁ (MonoidHom.id G) inf_le_left x
        | ⟨true⟩ => QuotientGroup.map (N₁ ⊓ N₂) N₂ (MonoidHom.id G) inf_le_right x
      map_one' := by
        funext b
        cases b with
        | up b =>
            cases b <;> rfl
      map_mul' := by
        intro x y
        funext b
        cases b with
        | up b =>
            cases b with
            | false =>
                exact (QuotientGroup.map (N₁ ⊓ N₂) N₁ (MonoidHom.id G) inf_le_left).map_mul x y
            | true =>
                exact (QuotientGroup.map (N₁ ⊓ N₂) N₂ (MonoidHom.id G) inf_le_right).map_mul x y }
  refine hC.finiteSubdirectProductClosed (ι := ULift Bool) (H := H) f ?_ ?_ ?_
  · intro x y hxy
    rcases QuotientGroup.mk'_surjective (N₁ ⊓ N₂) x with ⟨gx, rfl⟩
    rcases QuotientGroup.mk'_surjective (N₁ ⊓ N₂) y with ⟨gy, rfl⟩
    apply QuotientGroup.eq.2
    constructor
    · have hfalse :
          f (QuotientGroup.mk' (N₁ ⊓ N₂) gx) ⟨false⟩ =
            f (QuotientGroup.mk' (N₁ ⊓ N₂) gy) ⟨false⟩ :=
        congrArg (fun z : ∀ b : ULift Bool, H b => z ⟨false⟩) hxy
      exact QuotientGroup.eq.1 (by simpa [f, H] using hfalse)
    · have htrue :
          f (QuotientGroup.mk' (N₁ ⊓ N₂) gx) ⟨true⟩ =
            f (QuotientGroup.mk' (N₁ ⊓ N₂) gy) ⟨true⟩ :=
        congrArg (fun z : ∀ b : ULift Bool, H b => z ⟨true⟩) hxy
      exact QuotientGroup.eq.1 (by simpa [f, H] using htrue)
  · intro b
    cases b with
    | up b =>
        cases b with
        | false =>
            intro x
            rcases QuotientGroup.mk'_surjective N₁ x with ⟨g, rfl⟩
            refine ⟨QuotientGroup.mk' (N₁ ⊓ N₂) g, ?_⟩
            simp only [QuotientGroup.mk'_apply, MonoidHom.coe_mk, OneHom.coe_mk, QuotientGroup.map_mk, MonoidHom.id_apply,
  H, f]
        | true =>
            intro x
            rcases QuotientGroup.mk'_surjective N₂ x with ⟨g, rfl⟩
            refine ⟨QuotientGroup.mk' (N₁ ⊓ N₂) g, ?_⟩
            simp only [QuotientGroup.mk'_apply, MonoidHom.coe_mk, OneHom.coe_mk, QuotientGroup.map_mk, MonoidHom.id_apply,
  H, f]
  · intro b
    cases b with
    | up b =>
      cases b with
      | false =>
          simpa [H] using h₁
      | true =>
          simpa [H] using h₂

end FiniteGroupClass

end ProCGroups
