import ProCGroups.FreeProC.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CrowellExactSequence/Profinite/FreeProCSourceData.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C data for the direct completed-partials route

This file contains only the free pro-`C` source data and the chosen finite family attached to a
finite basis.  Coordinate packages, source-refined middles, and conditional exactness routes live
elsewhere.
-/

namespace CrowellExactSequence

noncomputable section

open scoped Pointwise Topology
open Filter
open ProCGroups.ProC

universe u

/-- Packaged carrier for a free pro-`C` group on a set converging to `1`. -/
structure FreeProCSourceData (ProC : ProCGroupPredicate.{u}) where
  basis : Type u
  carrier : Type u
  instGroup : Group carrier
  instTopologicalSpace : TopologicalSpace carrier
  instIsTopologicalGroup : IsTopologicalGroup carrier
  inclusion : basis → carrier
  isFree :
    ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) basis carrier inclusion
  proCGroup : ProCGroup ProC carrier

attribute [instance] FreeProCSourceData.instGroup
attribute [instance] FreeProCSourceData.instTopologicalSpace
attribute [instance] FreeProCSourceData.instIsTopologicalGroup

/-- The carrier of packaged free pro-`C` data is a pro-`C` group by construction. -/
instance FreeProCSourceData.instProCGroup
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC) :
    ProCGroup ProC sourceData.carrier :=
  sourceData.proCGroup

/-- Choose an equivalence from a finite free pro-`C` basis to `Fin n`. -/
def freeProCChosenBasisEquivOfBasisCard
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    sourceData.basis ≃ Fin n :=
  Classical.choice ((Cardinal.mk_eq_nat_iff).1 hbasis)

/-- The concrete `Fin n`-indexed family obtained from the chosen free pro-`C` basis. -/
def freeProCChosenFamilyOfBasisCard
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    Fin n → sourceData.carrier :=
  fun i =>
    sourceData.inclusion
      ((freeProCChosenBasisEquivOfBasisCard (ProC := ProC) sourceData hbasis).symm i)

/-- The universe-lifted chosen finite family.  ProGroups' free pro-`C` API keeps the generator
space in the same universe as the carrier, while `Fin n` lives in universe `0`; this is the
canonical lifted version used when invoking that API. -/
def freeProCChosenULiftFamilyOfBasisCard
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    ULift.{u} (Fin n) → sourceData.carrier :=
  fun i => freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis i.down

/-- The lifted chosen family has the same range as the concrete `Fin n` family. -/
theorem freeProCChosenULiftFamilyOfBasisCard_range
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    Set.range (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis) =
      Set.range (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis) := by
  ext g
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.down, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨ULift.up i, rfl⟩

/-- The concrete `Fin n`-indexed chosen family is the same free pro-`C` converging basis,
reindexed.  This is the finite-coordinate form used by the Crowell exactness assembly. -/
theorem freeProCChosenFamilyOfBasisCard_isFree
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) (Fin n) sourceData.carrier
      (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis) := by
  let e : Fin n ≃ sourceData.basis :=
    (freeProCChosenBasisEquivOfBasisCard (ProC := ProC) sourceData hbasis).symm
  simpa [freeProCChosenFamilyOfBasisCard, e] using
    sourceData.isFree.precompEquiv e

/-- The lifted chosen `Fin n`-indexed family is the same free pro-`C` converging basis,
reindexed. -/
theorem freeProCChosenULiftFamilyOfBasisCard_isFree
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    ProCGroups.FreeProC.IsFreeProCGroupOnConvergingSet
      (ProC := ProC) (ULift.{u} (Fin n)) sourceData.carrier
      (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis) := by
  let e : ULift.{u} (Fin n) ≃ sourceData.basis :=
    { toFun := fun i =>
        (freeProCChosenBasisEquivOfBasisCard (ProC := ProC) sourceData hbasis).symm i.down
      invFun := fun b =>
        ULift.up ((freeProCChosenBasisEquivOfBasisCard (ProC := ProC) sourceData hbasis) b)
      left_inv := by
        intro i
        cases i
        simp only [Equiv.apply_symm_apply]
      right_inv := by
        intro b
        simp only [Equiv.symm_apply_apply]}
  simpa [freeProCChosenULiftFamilyOfBasisCard, freeProCChosenFamilyOfBasisCard, e] using
    sourceData.isFree.precompEquiv e

/-- Reindexing the chosen basis by `Fin n` preserves topological generation. -/
theorem freeProCChosenFamilyOfBasisCard_generates
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    ProCGroups.Generation.TopologicallyGenerates
      (G := sourceData.carrier)
      (Set.range (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis)) := by
  classical
  have hRange :
      Set.range (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis) =
        Set.range sourceData.inclusion := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact
        ⟨(freeProCChosenBasisEquivOfBasisCard (ProC := ProC) sourceData hbasis).symm i, rfl⟩
    · rintro ⟨b, rfl⟩
      exact
        ⟨(freeProCChosenBasisEquivOfBasisCard (ProC := ProC) sourceData hbasis) b, by
          simp only [freeProCChosenFamilyOfBasisCard, Equiv.symm_apply_apply]⟩
  simpa [hRange] using sourceData.isFree.generates_range

/-- The image of the concrete chosen finite free basis under any map converges to `1`,
because the indexing type is finite. -/
theorem freeProCChosenFamilyOfBasisCard_image_convergesToOne
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n)
    {H : Type u} [Group H] [TopologicalSpace H] (ψ : sourceData.carrier → H) :
    ProCGroups.FreeProC.FamilyConvergesToOne
      (G := H)
      (fun i : Fin n =>
        ψ (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis i)) := by
  exact ProCGroups.FreeProC.FamilyConvergesToOne.of_finite_domain
    (G := H)
    (fun i : Fin n =>
      ψ (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis i))

/-- A surjective continuous homomorphism carries the chosen finite free basis to a topological
generating family of the target. -/
theorem freeProCChosenFamilyOfBasisCard_image_generates_of_surjective
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi) :
    ProCGroups.Generation.TopologicallyGenerates
      (G := H)
      (Set.range
        (fun i : Fin n =>
          psi (freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis i))) := by
  let family : Fin n → sourceData.carrier :=
    freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  have hsourceGen :
      ProCGroups.Generation.TopologicallyGenerates
        (G := sourceData.carrier) (Set.range family) := by
    simpa [family] using
      freeProCChosenFamilyOfBasisCard_generates (ProC := ProC) sourceData hbasis
  have himage :=
    ProCGroups.Generation.topologicallyGenerates_image_of_continuousMonoidHom_surjective
      (G := sourceData.carrier) (H := H) psi hpsi hsourceGen
  have hrange :
      psi '' Set.range family = Set.range (fun i : Fin n => psi (family i)) := by
    ext h
    constructor
    · rintro ⟨g, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨family i, ⟨i, rfl⟩, rfl⟩
  simpa [family, hrange] using himage

/-- The universe-lifted chosen family also topologically generates the free pro-`C` source. -/
theorem freeProCChosenULiftFamilyOfBasisCard_generates
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n) :
    ProCGroups.Generation.TopologicallyGenerates
      (G := sourceData.carrier)
      (Set.range (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis)) := by
  simpa [freeProCChosenULiftFamilyOfBasisCard_range (ProC := ProC) sourceData hbasis] using
    freeProCChosenFamilyOfBasisCard_generates (ProC := ProC) sourceData hbasis

/-- The image of the finite lifted basis under any target homomorphism converges to `1` in the
converging-set sense used by the free pro-`C` API. -/
theorem freeProCChosenULiftFamilyOfBasisCard_image_convergesToOne
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n)
    {H : Type u} [Group H] [TopologicalSpace H]
    (ψ : sourceData.carrier →* H) :
    ProCGroups.FreeProC.FamilyConvergesToOne
      (G := H)
      (fun i : ULift.{u} (Fin n) =>
        ψ (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis i)) := by
  exact ProCGroups.FreeProC.FamilyConvergesToOne.of_finite_domain
    (G := H)
    (fun i : ULift.{u} (Fin n) =>
      ψ (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis i))

/-- A surjective continuous homomorphism carries the lifted chosen finite free basis to a
topological generating family of the target. -/
theorem freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi) :
    ProCGroups.Generation.TopologicallyGenerates
      (G := H)
      (Set.range
        (fun i : ULift.{u} (Fin n) =>
          psi (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis i))) := by
  let family : Fin n → sourceData.carrier :=
    freeProCChosenFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  let liftedFamily : ULift.{u} (Fin n) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  have hfin :
      ProCGroups.Generation.TopologicallyGenerates
        (G := H) (Set.range (fun i : Fin n => psi (family i))) := by
    simpa [family] using
      freeProCChosenFamilyOfBasisCard_image_generates_of_surjective
        (ProC := ProC) sourceData hbasis psi hpsi
  have hrange :
      Set.range (fun i : ULift.{u} (Fin n) => psi (liftedFamily i)) =
        Set.range (fun i : Fin n => psi (family i)) := by
    ext h
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.down, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ULift.up i, rfl⟩
  simpa [family, liftedFamily, hrange] using hfin

/-- For the lifted finite free basis, the converging-set universal lift of a surjective target map
is the target map itself.  This is the concrete bridge needed when Fox constructions produce a
right component from the universal property. -/
theorem freeProCChosenULiftFamilyOfBasisCard_liftHom_eq_of_surjective
    {ProC : ProCGroupPredicate.{u}} (sourceData : FreeProCSourceData ProC)
    {n : Nat} (hbasis : Cardinal.mk sourceData.basis = n)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hH : ProC (G := H))
    (psi : ContinuousMonoidHom sourceData.carrier H) (hpsi : Function.Surjective psi) :
    (freeProCChosenULiftFamilyOfBasisCard_isFree (ProC := ProC) sourceData hbasis).liftHom hH
        (fun i : ULift.{u} (Fin n) =>
          psi (freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis i))
        (freeProCChosenULiftFamilyOfBasisCard_image_convergesToOne
          (ProC := ProC) sourceData hbasis psi.toMonoidHom)
        (freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
          (ProC := ProC) sourceData hbasis psi hpsi) =
      psi := by
  let hfree :=
    freeProCChosenULiftFamilyOfBasisCard_isFree (ProC := ProC) sourceData hbasis
  let liftedFamily : ULift.{u} (Fin n) → sourceData.carrier :=
    freeProCChosenULiftFamilyOfBasisCard (ProC := ProC) sourceData hbasis
  let φ : ULift.{u} (Fin n) → H := fun i => psi (liftedFamily i)
  let hconv :
      ProCGroups.FreeProC.FamilyConvergesToOne (G := H) φ :=
    by
      simpa [φ, liftedFamily] using
        freeProCChosenULiftFamilyOfBasisCard_image_convergesToOne
          (ProC := ProC) sourceData hbasis psi.toMonoidHom
  let hgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ) := by
    simpa [φ, liftedFamily] using
      freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
        (ProC := ProC) sourceData hbasis psi hpsi
  ext g
  have hmon :
      psi.toMonoidHom = hfree.lift hH φ hconv hgen :=
    hfree.lift_unique hH φ hconv hgen psi.continuous_toFun (by
      intro i
      rfl)
  exact (congrArg (fun f : sourceData.carrier →* H => f g) hmon).symm

end

end CrowellExactSequence
