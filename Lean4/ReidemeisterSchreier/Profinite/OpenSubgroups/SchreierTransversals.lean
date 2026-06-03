import ProCGroups.FreeProC.Basic
import ProCGroups.WreathProducts
import ReidemeisterSchreier.Profinite.OpenSubgroups.RightQuotient

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Profinite/OpenSubgroups/SchreierTransversals.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite open-subgroup Schreier theory

Profinite open subgroup quotients, finite permutation targets, dense free models, exact right Schreier generation, and topological rank bounds.
-/

open Set
open scoped Topology Pointwise

namespace ReidemeisterSchreier
namespace Profinite

open ProCGroups
open ProCGroups.ProC
open ProCGroups.FreeProC
open ProCGroups.WreathProducts

universe u v

section LeftQuotientSections

variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- The normalized continuous section of the left quotient by an open subgroup. -/
noncomputable abbrev openSubgroupLeftSchreierSection (H : OpenSubgroup F) :
    F ⧸ (H : Subgroup F) → F :=
  ProCGroups.ProC.quotientOpenSubgroupSection (H : Subgroup F)

omit [IsTopologicalGroup F] in
theorem openSubgroupLeftSchreierSection_rightInverse (H : OpenSubgroup F) :
    Function.RightInverse (openSubgroupLeftSchreierSection (F := F) H)
      (QuotientGroup.mk (s := (H : Subgroup F))) := by
  simpa [openSubgroupLeftSchreierSection] using
    (ProCGroups.ProC.quotientOpenSubgroupSection_rightInverse
      (G := F) (U := (H : Subgroup F)))

theorem continuous_openSubgroupLeftSchreierSection (H : OpenSubgroup F) :
    Continuous (openSubgroupLeftSchreierSection (F := F) H) := by
  simpa [openSubgroupLeftSchreierSection] using
    (ProCGroups.ProC.continuous_quotientOpenSubgroupSection
      (G := F) (U := (H : Subgroup F)) H.isOpen')

omit [IsTopologicalGroup F] in
@[simp] theorem openSubgroupLeftSchreierSection_mk
    (H : OpenSubgroup F) (q : F ⧸ (H : Subgroup F)) :
    QuotientGroup.mk (s := (H : Subgroup F))
        (openSubgroupLeftSchreierSection (F := F) H q) = q :=
  openSubgroupLeftSchreierSection_rightInverse (F := F) H q

omit [IsTopologicalGroup F] in
@[simp] theorem openSubgroupLeftSchreierSection_one
    (H : OpenSubgroup F) :
    openSubgroupLeftSchreierSection (F := F) H
        (QuotientGroup.mk (s := (H : Subgroup F)) (1 : F)) = 1 := by
  simp only [openSubgroupLeftSchreierSection, quotientOpenSubgroupSection_one]

/-- For a normal open subgroup, right and left cosets can be identified by the same
representative. -/
noncomputable def openSubgroupRightQuotientEquivLeftQuotientOfNormal
    (H : OpenSubgroup F) [Subgroup.Normal (H : Subgroup F)] :
    OpenSubgroupRightQuotient H ≃ F ⧸ (H : Subgroup F) where
  toFun :=
    Quotient.map' id fun a b hab => by
      rw [QuotientGroup.leftRel_apply]
      exact Subgroup.Normal.mem_comm (show Subgroup.Normal (H : Subgroup F) by infer_instance)
        (QuotientGroup.rightRel_apply.mp hab)
  invFun :=
    Quotient.map' id fun a b hab => by
      rw [QuotientGroup.rightRel_apply]
      exact Subgroup.Normal.mem_comm (show Subgroup.Normal (H : Subgroup F) by infer_instance)
        (QuotientGroup.leftRel_apply.mp hab)
  left_inv := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    rfl
  right_inv := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro g
    rfl

omit [IsTopologicalGroup F] in
/-- Under normality, the left Schreier section also represents the corresponding right coset. -/
theorem rightCosetSection_eq_leftCosetSection_of_normal
    (H : OpenSubgroup F) [Subgroup.Normal (H : Subgroup F)]
    (q : OpenSubgroupRightQuotient H) :
    Quotient.mk'' (openSubgroupLeftSchreierSection (F := F) H
      (openSubgroupRightQuotientEquivLeftQuotientOfNormal (F := F) H q)) = q := by
  let e := openSubgroupRightQuotientEquivLeftQuotientOfNormal (F := F) H
  change e.symm (QuotientGroup.mk (s := (H : Subgroup F))
      (openSubgroupLeftSchreierSection (F := F) H (e q))) = q
  exact (Equiv.symm_apply_eq e).2 (openSubgroupLeftSchreierSection_mk (F := F) H (e q))

end LeftQuotientSections

section AbstractSchreierSections

variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {X : Type v}
variable (H : OpenSubgroup F)

/-- The two cocycle orientations used by left- and right-coset Schreier generators. -/
inductive SchreierOrientation where
  | left
  | right
deriving DecidableEq

namespace SchreierOrientation

/-- The oriented Schreier cocycle associated to a section and a next-coset operation. -/
def cocycle {Q : Type u} (o : SchreierOrientation)
    (sec : Q → F) (next : Q → X → Q) (ι : X → F) (q : Q) (x : X) : F :=
  match o with
  | left => (sec (next q x))⁻¹ * sec q * ι x
  | right => sec q * ι x * (sec (next q x))⁻¹

end SchreierOrientation

/-- A section-level Schreier generator package.  It abstracts over the quotient type, the
left/right cocycle orientation, and the next-coset operation, so the common generator-set,
continuity, closure, and cardinality API can be stated once. -/
structure SchreierSection where
  Q : Type u
  orientation : SchreierOrientation
  sectionMap : Q → F
  next : (X → F) → Q → X → Q
  cocycle_mem :
    ∀ (ι : X → F) (q : Q) (x : X),
      orientation.cocycle sectionMap (next ι) ι q x ∈ (H : Subgroup F)

namespace SchreierSection

variable {H}

/-- The subgroup-valued generator attached to an abstract Schreier section. -/
noncomputable def generator (S : SchreierSection (F := F) (X := X) H)
    (ι : X → F) (q : S.Q) (x : X) : ↥(H : Subgroup F) :=
  ⟨S.orientation.cocycle S.sectionMap (S.next ι) ι q x, S.cocycle_mem ι q x⟩

omit [IsTopologicalGroup F] in
@[simp] theorem generator_coe (S : SchreierSection (F := F) (X := X) H)
    (ι : X → F) (q : S.Q) (x : X) :
    ((S.generator ι q x : ↥(H : Subgroup F)) : F) =
      S.orientation.cocycle S.sectionMap (S.next ι) ι q x :=
  rfl

/-- Nontrivial generator values of an abstract Schreier section. -/
def generatorSet (S : SchreierSection (F := F) (X := X) H)
    (ι : X → F) : Set ↥(H : Subgroup F) :=
  {z | ∃ q : S.Q, ∃ x : X, z = S.generator ι q x ∧ z ≠ 1}

/-- Nontrivial section Schreier pairs. -/
def NontrivialPairs (S : SchreierSection (F := F) (X := X) H)
    (ι : X → F) : Type (max u v) :=
  {p : S.Q × X // S.generator ι p.1 p.2 ≠ 1}

omit [IsTopologicalGroup F] in
instance finite_nontrivialPairs
    (S : SchreierSection (F := F) (X := X) H) (ι : X → F)
    [Finite X] [Finite S.Q] :
    Finite (S.NontrivialPairs ι) :=
  Finite.of_injective (fun p : S.NontrivialPairs ι => p.1) (by
    intro a b h
    exact Subtype.ext h)

omit [IsTopologicalGroup F] in
/-- The tautological map from nontrivial abstract Schreier pairs to the generator value set. -/
noncomputable def nontrivialPairsToGeneratorSet
    (S : SchreierSection (F := F) (X := X) H) (ι : X → F) :
    S.NontrivialPairs ι → ↥(S.generatorSet ι) := fun p =>
  ⟨S.generator ι p.1.1 p.1.2, ⟨p.1.1, p.1.2, rfl, p.2⟩⟩

omit [IsTopologicalGroup F] in
theorem surjective_nontrivialPairsToGeneratorSet
    (S : SchreierSection (F := F) (X := X) H) (ι : X → F) :
    Function.Surjective (S.nontrivialPairsToGeneratorSet ι) := by
  intro z
  rcases z.2 with ⟨q, x, hz, hz_ne⟩
  refine ⟨⟨(q, x), ?_⟩, ?_⟩
  · simpa [hz] using hz_ne
  · apply Subtype.ext
    exact hz.symm

omit [IsTopologicalGroup F] in
theorem natCard_generatorSet_le_nontrivialPairs
    (S : SchreierSection (F := F) (X := X) H) (ι : X → F)
    [Finite X] [Finite S.Q] :
    Nat.card (S.generatorSet ι) ≤ Nat.card (S.NontrivialPairs ι) :=
  Nat.card_le_card_of_surjective (S.nontrivialPairsToGeneratorSet ι)
    (S.surjective_nontrivialPairsToGeneratorSet ι)

omit [IsTopologicalGroup F] in
theorem natCard_nontrivialPairs_le
    (S : SchreierSection (F := F) (X := X) H) (ι : X → F)
    [Finite X] [Finite S.Q] :
    Nat.card (S.NontrivialPairs ι) ≤ Nat.card S.Q * Nat.card X := by
  have hle : Nat.card (S.NontrivialPairs ι) ≤ Nat.card (S.Q × X) :=
    Nat.card_le_card_of_injective (fun p : S.NontrivialPairs ι => p.1) (by
      intro a b h
      exact Subtype.ext h)
  simpa [Nat.card_prod] using hle

omit [IsTopologicalGroup F] in
theorem natCard_generatorSet_le
    (S : SchreierSection (F := F) (X := X) H) (ι : X → F)
    [Finite X] [Finite S.Q] :
    Nat.card (S.generatorSet ι) ≤ Nat.card S.Q * Nat.card X :=
  (S.natCard_generatorSet_le_nontrivialPairs ι).trans (S.natCard_nontrivialPairs_le ι)

omit [IsTopologicalGroup F] in
theorem subgroupClosure_generatorSet_eq_closure_range
    (S : SchreierSection (F := F) (X := X) H) (ι : X → F) :
    Subgroup.closure (S.generatorSet ι) =
      Subgroup.closure (Set.range fun p : S.Q × X => S.generator ι p.1 p.2) := by
  simpa [generatorSet] using
    (ProCGroups.Generation.closure_nontrivial_range_eq_closure_range
      (G := ↥(H : Subgroup F))
      (fun p : S.Q × X => S.generator ι p.1 p.2))

theorem topologicallyGenerates_generatorSet_iff
    (S : SchreierSection (F := F) (X := X) H) (ι : X → F) :
    ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (S.generatorSet ι) ↔
      ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (Set.range fun p : S.Q × X => S.generator ι p.1 p.2) := by
  rw [ProCGroups.Generation.topologicallyGenerates_iff_dense,
    ProCGroups.Generation.topologicallyGenerates_iff_dense,
    S.subgroupClosure_generatorSet_eq_closure_range ι]

omit [IsTopologicalGroup F] in
theorem generator_eq_one_iff_left
    (S : SchreierSection (F := F) (X := X) H)
    (hleft : S.orientation = SchreierOrientation.left)
    (ι : X → F) (q : S.Q) (x : X) :
    S.generator ι q x = 1 ↔ S.sectionMap (S.next ι q x) = S.sectionMap q * ι x := by
  constructor
  · intro h
    have hval := congrArg Subtype.val h
    change S.orientation.cocycle S.sectionMap (S.next ι) ι q x = 1 at hval
    exact inv_mul_eq_one.mp (by
      simpa [SchreierOrientation.cocycle, hleft, mul_assoc] using hval)
  · intro hrep
    apply Subtype.ext
    simp only [generator, SchreierOrientation.cocycle, hleft, hrep, mul_inv_rev, mul_assoc, inv_mul_cancel,
  mul_one, OneMemClass.coe_one]

omit [IsTopologicalGroup F] in
theorem generator_eq_one_iff_right
    (S : SchreierSection (F := F) (X := X) H)
    (hright : S.orientation = SchreierOrientation.right)
    (ι : X → F) (q : S.Q) (x : X) :
    S.generator ι q x = 1 ↔ S.sectionMap (S.next ι q x) = S.sectionMap q * ι x := by
  constructor
  · intro h
    have hval := congrArg Subtype.val h
    change S.orientation.cocycle S.sectionMap (S.next ι) ι q x = 1 at hval
    exact (mul_inv_eq_one.mp
      (by simpa [SchreierOrientation.cocycle, hright, mul_assoc] using hval)).symm
  · intro hrep
    apply Subtype.ext
    simp only [generator, SchreierOrientation.cocycle, hright, hrep, mul_inv_rev, mul_assoc, mul_inv_cancel_left,
  mul_inv_cancel, OneMemClass.coe_one]

omit [IsTopologicalGroup F] in
theorem generator_eq_of_section_next_eq_one
    (S : SchreierSection (F := F) (X := X) H)
    (ι : X → F) (q : S.Q) (x : X)
    (hnext : S.sectionMap (S.next ι q x) = 1)
    (hmem : S.sectionMap q * ι x ∈ (H : Subgroup F)) :
    S.generator ι q x = ⟨S.sectionMap q * ι x, hmem⟩ := by
  apply Subtype.ext
  cases hside : S.orientation with
  | left =>
      simp only [generator, SchreierOrientation.cocycle, hside, hnext, inv_one, one_mul]
  | right =>
      simp only [generator, SchreierOrientation.cocycle, hside, hnext, inv_one, mul_one]

theorem continuous_generator
    (S : SchreierSection (F := F) (X := X) H)
    [TopologicalSpace S.Q] [TopologicalSpace X]
    (ι : X → F)
    (hsection : Continuous S.sectionMap)
    (hnext : Continuous (fun p : S.Q × X => S.next ι p.1 p.2))
    (hι : Continuous ι) :
    Continuous (fun p : S.Q × X => S.generator ι p.1 p.2) := by
  refine Continuous.subtype_mk ?_ ?_
  cases hside : S.orientation with
  | left =>
      have hcont :
          Continuous (fun p : S.Q × X =>
            (S.sectionMap (S.next ι p.1 p.2))⁻¹ * (S.sectionMap p.1 * ι p.2)) :=
        ((hsection.comp hnext).inv).mul
          ((hsection.comp continuous_fst).mul (hι.comp continuous_snd))
      simpa [generator, SchreierOrientation.cocycle, hside, mul_assoc] using hcont
  | right =>
      have hcont :
          Continuous (fun p : S.Q × X =>
            (S.sectionMap p.1 * ι p.2) * (S.sectionMap (S.next ι p.1 p.2))⁻¹) :=
        ((hsection.comp continuous_fst).mul (hι.comp continuous_snd)).mul
          ((hsection.comp hnext).inv)
      simpa [generator, SchreierOrientation.cocycle, hside, mul_assoc] using hcont

end SchreierSection

end AbstractSchreierSections

section LeftSchreierGenerators

variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable (H : OpenSubgroup F)
variable {X : Type v}
variable (σ : F ⧸ (H : Subgroup F) → F)
variable (hσ : Function.RightInverse σ (QuotientGroup.mk (s := (H : Subgroup F))))
variable (ι : X → F)

/-- Raw Schreier section cocycle for a section, a next-coset operation, and ambient generators. -/
def sectionCocycle {Q : Type u} (σ : Q → F) (next : Q → X → Q) (ι : X → F) :
    Q → X → F :=
  fun q x => (σ (next q x))⁻¹ * σ q * ι x

/-- The next left coset obtained from a chosen representative and a generator. -/
def leftSchreierNextCoset (q : F ⧸ (H : Subgroup F)) (x : X) : F ⧸ (H : Subgroup F) :=
  QuotientGroup.mk (s := (H : Subgroup F)) (σ q * ι x)

/-- Left-coset Schreier generator attached to a section of the quotient by an open subgroup. -/
noncomputable def leftSchreierGenerator
    (hσ : Function.RightInverse σ (QuotientGroup.mk (s := (H : Subgroup F))))
    (q : F ⧸ (H : Subgroup F)) (x : X) :
    ↥(H : Subgroup F) := by
  let qx := leftSchreierNextCoset (F := F) H σ ι q x
  refine ⟨sectionCocycle (F := F) (X := X) σ
    (leftSchreierNextCoset (F := F) H σ ι) ι q x, ?_⟩
  have hqx :
      QuotientGroup.mk (s := (H : Subgroup F)) (σ qx) =
        QuotientGroup.mk (s := (H : Subgroup F)) (σ q * ι x) := by
    simpa [qx, leftSchreierNextCoset] using hσ qx
  simpa [sectionCocycle, mul_assoc] using (QuotientGroup.eq.1 hqx)

/-- The left-coset Schreier data as an instance of the abstract section API. -/
noncomputable def leftSchreierSection :
    SchreierSection (F := F) (X := X) H where
  Q := F ⧸ (H : Subgroup F)
  orientation := SchreierOrientation.left
  sectionMap := σ
  next := fun ι q x => leftSchreierNextCoset (F := F) H σ ι q x
  cocycle_mem := by
    intro ι q x
    exact (leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) q x).property

omit [IsTopologicalGroup F] in
@[simp] theorem leftSchreierSection_generator
    (q : F ⧸ (H : Subgroup F)) (x : X) :
    (leftSchreierSection (F := F) (H := H) (σ := σ) (hσ := hσ) :
        SchreierSection (F := F) (X := X) H).generator ι q x =
      leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) q x := by
  apply Subtype.ext
  rfl

/-- The normalized left quotient section as abstract Schreier section data. -/
noncomputable def chosenLeftSchreierSection :
    SchreierSection (F := F) (X := X) H :=
  leftSchreierSection (F := F) (H := H)
    (σ := openSubgroupLeftSchreierSection (F := F) H)
    (hσ := openSubgroupLeftSchreierSection_rightInverse (F := F) H)

omit [IsTopologicalGroup F] in
theorem leftSchreierNextCoset_eq_of_mem
    (hσ : Function.RightInverse σ (QuotientGroup.mk (s := (H : Subgroup F))))
    {q : F ⧸ (H : Subgroup F)} {x : X}
    (hx : ι x ∈ (H : Subgroup F)) :
    leftSchreierNextCoset (F := F) H σ ι q x = q := by
  have hEq :
      QuotientGroup.mk (s := (H : Subgroup F)) (σ q) =
        QuotientGroup.mk (s := (H : Subgroup F)) (σ q * ι x) := by
    exact QuotientGroup.eq.2 (by simpa using hx)
  calc
    leftSchreierNextCoset (F := F) H σ ι q x
        = QuotientGroup.mk (s := (H : Subgroup F)) (σ q * ι x) := rfl
    _ = QuotientGroup.mk (s := (H : Subgroup F)) (σ q) := hEq.symm
    _ = q := hσ q

omit [IsTopologicalGroup F] in
theorem leftSchreierNextCoset_eq_basepoint_of_mul_mem
    {q : F ⧸ (H : Subgroup F)} {x : X}
    (hx : σ q * ι x ∈ (H : Subgroup F)) :
    leftSchreierNextCoset (F := F) H σ ι q x =
      QuotientGroup.mk (s := (H : Subgroup F)) (1 : F) := by
  apply QuotientGroup.eq.2
  simpa using (H : Subgroup F).inv_mem hx

omit [IsTopologicalGroup F] in
theorem leftSchreierGenerator_eq_of_mem
    {q : F ⧸ (H : Subgroup F)} {x : X}
    (hx : ι x ∈ (H : Subgroup F)) :
    leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) q x = ⟨ι x, hx⟩ := by
  apply Subtype.ext
  have hnext :
      leftSchreierNextCoset (F := F) H σ ι q x = q :=
    leftSchreierNextCoset_eq_of_mem (F := F) (H := H) (σ := σ) (ι := ι) hσ hx
  simp only [leftSchreierGenerator, sectionCocycle, hnext, inv_mul_cancel, one_mul]

omit [IsTopologicalGroup F] in
theorem leftSchreierGenerator_eq_one
    {q : F ⧸ (H : Subgroup F)} {x : X}
    (hx : ι x = 1) :
    leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) q x = 1 := by
  have hx' : ι x ∈ (H : Subgroup F) := by
    rw [hx]
    exact (H : Subgroup F).one_mem
  rw [leftSchreierGenerator_eq_of_mem (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) hx']
  simp only [hx, Subgroup.mk_eq_one]

omit [IsTopologicalGroup F] in
theorem leftSchreierGenerator_eq_one_iff
    {H : OpenSubgroup F}
    {σ : F ⧸ (H : Subgroup F) → F}
    (hσ : Function.RightInverse σ (QuotientGroup.mk (s := (H : Subgroup F))))
    {ι : X → F}
    {q : F ⧸ (H : Subgroup F)} {x : X} :
    leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) q x = 1 ↔
      σ (leftSchreierNextCoset (F := F) H σ ι q x) = σ q * ι x := by
  simpa using
    ((leftSchreierSection (F := F) (H := H) (σ := σ) (hσ := hσ) :
        SchreierSection (F := F) (X := X) H).generator_eq_one_iff_left
      rfl ι q x)

omit [IsTopologicalGroup F] in
theorem leftSchreierGenerator_eq_one_of_section_eq
    {q : F ⧸ (H : Subgroup F)} {x : X}
    (hrep : σ (leftSchreierNextCoset (F := F) H σ ι q x) = σ q * ι x) :
    leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) q x = 1 :=
  (leftSchreierGenerator_eq_one_iff
    (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι)
    (q := q) (x := x)).2 hrep

omit [IsTopologicalGroup F] in
theorem leftSchreierGenerator_eq_of_mul_mem
    (hσ1 : σ (QuotientGroup.mk (s := (H : Subgroup F)) (1 : F)) = 1)
    {q : F ⧸ (H : Subgroup F)} {x : X}
    (hx : σ q * ι x ∈ (H : Subgroup F)) :
    leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) q x =
      ⟨σ q * ι x, hx⟩ := by
  have hnext : leftSchreierNextCoset (F := F) H σ ι q x =
      QuotientGroup.mk (s := (H : Subgroup F)) (1 : F) := by
    apply QuotientGroup.eq.2
    simpa [mul_inv_rev] using (H : Subgroup F).inv_mem hx
  have hsectionNext :
      σ (leftSchreierNextCoset (F := F) H σ ι q x) = 1 := by
    simpa [hnext] using hσ1
  simpa using
    ((leftSchreierSection (F := F) (H := H) (σ := σ) (hσ := hσ) :
        SchreierSection (F := F) (X := X) H).generator_eq_of_section_next_eq_one
      ι q x hsectionNext hx)

section Topological

variable [TopologicalSpace X]

theorem continuous_leftSchreierNextCoset
    (hσcont : Continuous σ) (hιcont : Continuous ι) :
    Continuous (fun p : (F ⧸ (H : Subgroup F)) × X =>
      leftSchreierNextCoset (F := F) H σ ι p.1 p.2) := by
  simpa [leftSchreierNextCoset] using
    (QuotientGroup.continuous_mk.comp
      ((hσcont.comp continuous_fst).mul (hιcont.comp continuous_snd)))

theorem continuous_leftSchreierGenerator
    (hσcont : Continuous σ) (hιcont : Continuous ι) :
    Continuous (fun p : (F ⧸ (H : Subgroup F)) × X =>
      leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) p.1 p.2) := by
  letI : TopologicalSpace
      (leftSchreierSection (F := F) (H := H) (σ := σ) (hσ := hσ) :
        SchreierSection (F := F) (X := X) H).Q :=
    inferInstanceAs (TopologicalSpace (F ⧸ (H : Subgroup F)))
  simpa using
    ((leftSchreierSection (F := F) (H := H) (σ := σ) (hσ := hσ) :
        SchreierSection (F := F) (X := X) H).continuous_generator
      ι hσcont
      (continuous_leftSchreierNextCoset (F := F) (H := H) (σ := σ) (ι := ι)
        hσcont hιcont)
      hιcont)

end Topological

section FiniteCardinality

omit [IsTopologicalGroup F] in
theorem natCard_range_leftSchreierGenerator_le
    [Finite X] [Finite (F ⧸ (H : Subgroup F))] :
    Nat.card
        (Set.range fun p : (F ⧸ (H : Subgroup F)) × X =>
          leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) p.1 p.2) ≤
      Nat.card (F ⧸ (H : Subgroup F)) * Nat.card X := by
  simpa [Nat.card_prod] using
    (Finite.card_range_le
      (fun p : (F ⧸ (H : Subgroup F)) × X =>
        leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) p.1 p.2))

end FiniteCardinality

/-- The nontrivial left-coset Schreier generators attached to a section. -/
def leftSchreierGeneratorSet : Set ↥(H : Subgroup F) :=
  {z | ∃ q : F ⧸ (H : Subgroup F), ∃ x : X,
    z = leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) q x ∧
      z ≠ 1}

/-- Nontrivial left Schreier pairs for a chosen section. -/
def leftNontrivialSchreierPairs : Type (max u v) :=
  {p : (F ⧸ (H : Subgroup F)) × X //
    leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) p.1 p.2 ≠ 1}

omit [IsTopologicalGroup F] in
instance finite_leftNontrivialSchreierPairs
    [Finite X] [Finite (F ⧸ (H : Subgroup F))] :
    Finite (leftNontrivialSchreierPairs (F := F) H σ hσ ι) :=
  Finite.of_injective
    (fun p : leftNontrivialSchreierPairs (F := F) H σ hσ ι => p.1)
    (by
      intro a b h
      exact Subtype.ext h)

omit [IsTopologicalGroup F] in
theorem natCard_leftNontrivialSchreierPairs_le
    [Finite X] [Finite (F ⧸ (H : Subgroup F))] :
    Nat.card (leftNontrivialSchreierPairs (F := F) H σ hσ ι) ≤
      Nat.card (F ⧸ (H : Subgroup F)) * Nat.card X := by
  have hle :
      Nat.card (leftNontrivialSchreierPairs (F := F) H σ hσ ι) ≤
        Nat.card ((F ⧸ (H : Subgroup F)) × X) := by
    exact Nat.card_le_card_of_injective
      (fun p : leftNontrivialSchreierPairs (F := F) H σ hσ ι => p.1)
      (by
        intro a b h
        exact Subtype.ext h)
  simpa [Nat.card_prod] using hle

omit [IsTopologicalGroup F] in
/-- The tautological map from nontrivial left Schreier pairs to the nontrivial generator set. -/
noncomputable def leftNontrivialSchreierPairsToGeneratorSet :
    leftNontrivialSchreierPairs (F := F) H σ hσ ι →
      ↥(leftSchreierGeneratorSet (F := F) H σ hσ ι) := fun p =>
  ⟨leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) p.1.1 p.1.2,
    ⟨p.1.1, p.1.2, rfl, p.2⟩⟩

omit [IsTopologicalGroup F] in
@[simp] theorem leftNontrivialSchreierPairsToGeneratorSet_apply
    (p : leftNontrivialSchreierPairs (F := F) H σ hσ ι) :
    ((leftNontrivialSchreierPairsToGeneratorSet (F := F) H σ hσ ι p :
        ↥(leftSchreierGeneratorSet (F := F) H σ hσ ι)) : ↥(H : Subgroup F)) =
      leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι)
        p.1.1 p.1.2 :=
  rfl

omit [IsTopologicalGroup F] in
theorem surjective_leftNontrivialSchreierPairsToGeneratorSet :
    Function.Surjective
      (leftNontrivialSchreierPairsToGeneratorSet (F := F) H σ hσ ι) := by
  intro z
  rcases z.2 with ⟨q, x, hz, hz_ne⟩
  refine ⟨⟨(q, x), ?_⟩, ?_⟩
  · simpa [hz] using hz_ne
  · apply Subtype.ext
    exact hz.symm

omit [IsTopologicalGroup F] in
theorem natCard_leftSchreierGeneratorSet_le_nontrivialPairs
    [Finite X] [Finite (F ⧸ (H : Subgroup F))] :
    Nat.card (leftSchreierGeneratorSet (F := F) H σ hσ ι) ≤
      Nat.card (leftNontrivialSchreierPairs (F := F) H σ hσ ι) := by
  exact Nat.card_le_card_of_surjective
    (leftNontrivialSchreierPairsToGeneratorSet (F := F) H σ hσ ι)
    (surjective_leftNontrivialSchreierPairsToGeneratorSet
      (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι))

omit [IsTopologicalGroup F] in
theorem mem_leftSchreierGeneratorSet
    {H : OpenSubgroup F}
    {σ : F ⧸ (H : Subgroup F) → F}
    {hσ : Function.RightInverse σ (QuotientGroup.mk (s := (H : Subgroup F)))}
    {ι : X → F} {z : ↥(H : Subgroup F)} :
    z ∈ leftSchreierGeneratorSet (F := F) H σ hσ ι ↔
      ∃ q : F ⧸ (H : Subgroup F), ∃ x : X,
        z = leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) q x ∧
          z ≠ 1 :=
  Iff.rfl

omit [IsTopologicalGroup F] in
theorem leftSchreierGeneratorSet_subset_range :
    leftSchreierGeneratorSet (F := F) H σ hσ ι ⊆
      Set.range (fun p : (F ⧸ (H : Subgroup F)) × X =>
        leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) p.1 p.2) := by
  intro z hz
  rcases hz with ⟨q, x, rfl, _⟩
  exact ⟨(q, x), rfl⟩

omit [IsTopologicalGroup F] in
theorem subgroupClosure_leftSchreierGeneratorSet_eq_closure_range :
    Subgroup.closure (leftSchreierGeneratorSet (F := F) H σ hσ ι) =
      Subgroup.closure (Set.range fun p : (F ⧸ (H : Subgroup F)) × X =>
        leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) p.1 p.2) := by
  simpa [leftSchreierGeneratorSet, SchreierSection.generatorSet] using
    ((leftSchreierSection (F := F) (H := H) (σ := σ) (hσ := hσ) :
        SchreierSection (F := F) (X := X) H).subgroupClosure_generatorSet_eq_closure_range ι)

theorem topologicallyGenerates_leftSchreierGeneratorSet_iff
    {H : OpenSubgroup F}
    {σ : F ⧸ (H : Subgroup F) → F}
    {hσ : Function.RightInverse σ (QuotientGroup.mk (s := (H : Subgroup F)))}
    {ι : X → F} :
    ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (leftSchreierGeneratorSet (F := F) H σ hσ ι) ↔
      ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (Set.range fun p : (F ⧸ (H : Subgroup F)) × X =>
          leftSchreierGenerator (F := F) (H := H) (σ := σ) (hσ := hσ) (ι := ι) p.1 p.2) := by
  simpa [leftSchreierGeneratorSet, SchreierSection.generatorSet] using
    ((leftSchreierSection (F := F) (H := H) (σ := σ) (hσ := hσ) :
        SchreierSection (F := F) (X := X) H).topologicallyGenerates_generatorSet_iff ι)

omit [IsTopologicalGroup F] in
theorem natCard_leftSchreierGeneratorSet_le
    [Finite X] [Finite (F ⧸ (H : Subgroup F))] :
    Nat.card (leftSchreierGeneratorSet (F := F) H σ hσ ι) ≤
      Nat.card (F ⧸ (H : Subgroup F)) * Nat.card X := by
  letI : Finite
      (leftSchreierSection (F := F) (H := H) (σ := σ) (hσ := hσ) :
        SchreierSection (F := F) (X := X) H).Q :=
    inferInstanceAs (Finite (F ⧸ (H : Subgroup F)))
  simpa [leftSchreierGeneratorSet, SchreierSection.generatorSet] using
    ((leftSchreierSection (F := F) (H := H) (σ := σ) (hσ := hσ) :
        SchreierSection (F := F) (X := X) H).natCard_generatorSet_le ι)

end LeftSchreierGenerators

section RightSchreierGenerators

variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable (H : OpenSubgroup F)
variable {X : Type v}
variable (τ : OpenSubgroupRightQuotient H → F)
variable (hτ : ∀ q, Quotient.mk'' (τ q) = q)
variable (ι : X → F)

instance instMulActionOpenSubgroupRightQuotient :
    MulAction F (OpenSubgroupRightQuotient H) :=
  rightCosetMulAction (H : Subgroup F)

/-- The next right coset obtained from a chosen representative and a generator. -/
def rightSchreierNextCoset (q : OpenSubgroupRightQuotient H) (x : X) :
    OpenSubgroupRightQuotient H :=
  (ι x)⁻¹ • q

omit [IsTopologicalGroup F] in
theorem rightSchreierNextCoset_basepoint_eq_of_mem
    {x : X} (hx : ι x ∈ (H : Subgroup F)) :
    rightSchreierNextCoset (F := F) H ι (openSubgroupRightCoset H (1 : F)) x =
      openSubgroupRightCoset H (1 : F) := by
  calc
    rightSchreierNextCoset (F := F) H ι (openSubgroupRightCoset H (1 : F)) x =
        (ι x)⁻¹ • (Quotient.mk'' (1 : F) : OpenSubgroupRightQuotient H) := rfl
    _ = Quotient.mk'' ((1 : F) * ι x) := by
        rw [rightCosetMulAction_inv_mk_smul (H := (H : Subgroup F))]
    _ = openSubgroupRightCoset H (1 : F) := by
        exact (openSubgroupRightCoset_eq_basepoint_iff_mem (F := F) (H := H)).2
          (by simpa using hx)

omit [IsTopologicalGroup F] in
theorem rightSchreierNextCoset_eq_basepoint_of_mul_mem
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    {q : OpenSubgroupRightQuotient H} {x : X}
    (hx : τ q * ι x ∈ (H : Subgroup F)) :
    rightSchreierNextCoset (F := F) H ι q x = openSubgroupRightCoset H (1 : F) := by
  calc
    rightSchreierNextCoset (F := F) H ι q x =
        (ι x)⁻¹ • (Quotient.mk'' (τ q) : OpenSubgroupRightQuotient H) := by
          simp only [rightSchreierNextCoset, hτ q]
    _ = Quotient.mk'' (τ q * ι x) := by
        rw [rightCosetMulAction_inv_mk_smul (H := (H : Subgroup F))]
    _ = openSubgroupRightCoset H (1 : F) :=
        (openSubgroupRightCoset_eq_basepoint_iff_mem (F := F) (H := H)).2 hx

/-- Right-coset Schreier generator `t_q x t_{qx}^{-1}`. -/
noncomputable def rightSchreierGenerator (q : OpenSubgroupRightQuotient H) (x : X) :
    ↥(H : Subgroup F) :=
  rightQuotientSectionCocycle (H := (H : Subgroup F)) τ hτ (ι x) q

/-- The right-coset Schreier data as an instance of the abstract section API. -/
noncomputable def rightSchreierSection :
    SchreierSection (F := F) (X := X) H where
  Q := OpenSubgroupRightQuotient H
  orientation := SchreierOrientation.right
  sectionMap := τ
  next := fun ι q x => rightSchreierNextCoset (F := F) H ι q x
  cocycle_mem := by
    intro ι q x
    exact (rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x).property

omit [IsTopologicalGroup F] in
@[simp] theorem rightSchreierSection_generator
    (q : OpenSubgroupRightQuotient H) (x : X) :
    (rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierSection (F := F) (X := X) H).generator ι q x =
      rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x := by
  apply Subtype.ext
  rfl

/-- The normalized right quotient section as abstract Schreier section data. -/
noncomputable def chosenRightSchreierSection :
    SchreierSection (F := F) (X := X) H :=
  rightSchreierSection (F := F) (H := H)
    (τ := openSubgroupRightCosetSection (F := F) H)
    (hτ := openSubgroupRightCosetSection_spec (F := F) H)

omit [IsTopologicalGroup F] in
theorem rightSchreierGenerator_eq_one
    {q : OpenSubgroupRightQuotient H} {x : X}
    (hx : ι x = 1) :
    rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x = 1 := by
  apply Subtype.ext
  simp only [rightSchreierGenerator, rightQuotientSectionCocycle, hx, mul_one, inv_one, one_smul,
  mul_inv_cancel, OneMemClass.coe_one]

omit [IsTopologicalGroup F] in
theorem rightSchreierGenerator_eq_one_iff
    {H : OpenSubgroup F}
    {τ : OpenSubgroupRightQuotient H → F}
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    {ι : X → F}
    {q : OpenSubgroupRightQuotient H} {x : X} :
    rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x = 1 ↔
      τ ((ι x)⁻¹ • q) = τ q * ι x := by
  simpa using
    ((rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierSection (F := F) (X := X) H).generator_eq_one_iff_right
      rfl ι q x)

omit [IsTopologicalGroup F] in
theorem rightSchreierGenerator_eq_one_iff_nextCoset
    {H : OpenSubgroup F}
    {τ : OpenSubgroupRightQuotient H → F}
    (hτ : ∀ q, Quotient.mk'' (τ q) = q)
    {ι : X → F}
    {q : OpenSubgroupRightQuotient H} {x : X} :
    rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x = 1 ↔
      τ (rightSchreierNextCoset (F := F) H ι q x) = τ q * ι x := by
  simpa [rightSchreierNextCoset] using
    (rightSchreierGenerator_eq_one_iff
      (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι)
      (q := q) (x := x))

omit [IsTopologicalGroup F] in
theorem rightSchreierGenerator_eq_one_of_section_eq
    {q : OpenSubgroupRightQuotient H} {x : X}
    (hrep : τ ((ι x)⁻¹ • q) = τ q * ι x) :
    rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x = 1 :=
  (rightSchreierGenerator_eq_one_iff
    (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι)
    (q := q) (x := x)).2 hrep

omit [IsTopologicalGroup F] in
theorem rightSchreierGenerator_eq_of_mul_mem
    (hτ1 : τ (openSubgroupRightCoset H (1 : F)) = 1)
    {q : OpenSubgroupRightQuotient H} {x : X}
    (hx : τ q * ι x ∈ (H : Subgroup F)) :
    rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x =
      ⟨τ q * ι x, hx⟩ := by
  have hnext : (ι x)⁻¹ • q = openSubgroupRightCoset H (1 : F) := by
    calc
      (ι x)⁻¹ • q = (ι x)⁻¹ • (Quotient.mk'' (τ q) : OpenSubgroupRightQuotient H) := by
          rw [hτ q]
      _ = Quotient.mk'' (τ q * ι x) := by
          rw [rightCosetMulAction_inv_mk_smul (H := (H : Subgroup F))]
      _ = openSubgroupRightCoset H (1 : F) :=
          (openSubgroupRightCoset_eq_basepoint_iff_mem (F := F) (H := H)).2 hx
  have hsectionNext : τ ((ι x)⁻¹ • q) = 1 := by
    simpa [hnext] using hτ1
  simpa using
    ((rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierSection (F := F) (X := X) H).generator_eq_of_section_next_eq_one
      ι q x hsectionNext hx)

omit [IsTopologicalGroup F] in
theorem rightSchreierGenerator_basepoint_eq_of_mem
    (hτ1 : τ (openSubgroupRightCoset H (1 : F)) = 1)
    {x : X} (hx : ι x ∈ (H : Subgroup F)) :
    rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι)
        (openSubgroupRightCoset H (1 : F)) x =
      ⟨ι x, hx⟩ := by
  have hx' : τ (openSubgroupRightCoset H (1 : F)) * ι x ∈ (H : Subgroup F) := by
    simpa [hτ1] using hx
  simpa [hτ1] using
    (rightSchreierGenerator_eq_of_mul_mem
      (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι)
      hτ1 (q := openSubgroupRightCoset H (1 : F)) (x := x) hx')

section Topological

variable [TopologicalSpace X]
variable [TopologicalSpace (OpenSubgroupRightQuotient H)]
variable [DiscreteTopology (OpenSubgroupRightQuotient H)]

theorem continuous_rightSchreierNextCoset
    (hιcont : Continuous ι) :
    Continuous (fun p : OpenSubgroupRightQuotient H × X =>
      rightSchreierNextCoset (F := F) H ι p.1 p.2) := by
  letI : MulAction F (OpenSubgroupRightQuotient H) :=
    rightCosetMulAction (H : Subgroup F)
  refine (continuous_prod_of_discrete_left).2 ?_
  intro q
  have hqcont :
      Continuous fun x : X => ((ι x)⁻¹ • q : OpenSubgroupRightQuotient H) := by
    rw [continuous_discrete_rng]
    intro q'
    classical
    let a : F := q.out
    let b : F := q'.out
    have hpre :
        (fun x : X => ((ι x)⁻¹ • q : OpenSubgroupRightQuotient H)) ⁻¹' ({q'} :
            Set (OpenSubgroupRightQuotient H)) =
          (fun x : X => b * (ι x)⁻¹ * a⁻¹) ⁻¹' ((H : Subgroup F) : Set F) := by
      ext x
      constructor
      · intro hx
        have hEq :
            (Quotient.mk'' (a * ι x) : OpenSubgroupRightQuotient H) = Quotient.mk'' b := by
          calc
            (Quotient.mk'' (a * ι x) : OpenSubgroupRightQuotient H)
                = (ι x)⁻¹ • (Quotient.mk'' a : OpenSubgroupRightQuotient H) := by
                    rw [rightCosetMulAction_inv_mk_smul (H := (H : Subgroup F)) (ι x) a]
            _ = (ι x)⁻¹ • q := by rw [Quotient.out_eq' q]
            _ = q' := hx
            _ = Quotient.mk'' b := (Quotient.out_eq' q').symm
        have hrel :
            QuotientGroup.rightRel (H : Subgroup F) (a * ι x) b := Quotient.eq''.mp hEq
        simpa [a, b, mul_inv_rev, mul_assoc] using (QuotientGroup.rightRel_apply.mp hrel)
      · intro hx
        have hrel :
            QuotientGroup.rightRel (H : Subgroup F) (a * ι x) b := by
          rw [QuotientGroup.rightRel_apply]
          simpa only [a, b, mul_inv_rev, mul_assoc] using hx
        calc
          ((ι x)⁻¹ • q : OpenSubgroupRightQuotient H)
              = (ι x)⁻¹ • (Quotient.mk'' a : OpenSubgroupRightQuotient H) := by
                  rw [Quotient.out_eq' q]
          _ = Quotient.mk'' (a * ι x) := by
                rw [rightCosetMulAction_inv_mk_smul (H := (H : Subgroup F)) (ι x) a]
          _ = Quotient.mk'' b := Quotient.eq''.mpr hrel
          _ = q' := Quotient.out_eq' q'
    rw [show
      (fun x : X => ((ι x)⁻¹ • q : OpenSubgroupRightQuotient H)) ⁻¹' ({q'} :
          Set (OpenSubgroupRightQuotient H)) =
        (fun x : X => b * (ι x)⁻¹ * a⁻¹) ⁻¹' ((H : Subgroup F) : Set F) by
          simpa using hpre]
    exact H.isOpen'.preimage ((continuous_const.mul (hιcont.inv)).mul continuous_const)
  simpa [rightSchreierNextCoset] using hqcont

theorem continuous_rightSchreierGenerator
    (hτcont : Continuous τ) (hιcont : Continuous ι) :
    Continuous (fun p : OpenSubgroupRightQuotient H × X =>
      rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) p.1 p.2) := by
  letI : TopologicalSpace
      (rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierSection (F := F) (X := X) H).Q :=
    inferInstanceAs (TopologicalSpace (OpenSubgroupRightQuotient H))
  simpa using
    ((rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierSection (F := F) (X := X) H).continuous_generator
      ι hτcont
      (continuous_rightSchreierNextCoset (F := F) (H := H) (ι := ι) hιcont)
      hιcont)

end Topological


theorem natCard_range_rightSchreierGenerator_le
    [CompactSpace F] [Finite X] :
    Nat.card
        (Set.range fun p : OpenSubgroupRightQuotient H × X =>
          rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) p.1 p.2) ≤
      Nat.card (OpenSubgroupRightQuotient H) * Nat.card X := by
  simpa [Nat.card_prod] using
    (Finite.card_range_le
      (fun p : OpenSubgroupRightQuotient H × X =>
        rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) p.1 p.2))


/-- The nontrivial right-coset Schreier generators attached to a section. -/
def rightSchreierGeneratorSet : Set ↥(H : Subgroup F) :=
  {z | ∃ q : OpenSubgroupRightQuotient H, ∃ x : X,
    z = rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x ∧
      z ≠ 1}

/-- Nontrivial right Schreier pairs for a chosen section. -/
def rightNontrivialSchreierPairs : Type (max u v) :=
  {p : OpenSubgroupRightQuotient H × X //
    rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) p.1 p.2 ≠ 1}

omit [IsTopologicalGroup F] in
instance finite_rightNontrivialSchreierPairs
    [Finite X] [Finite (OpenSubgroupRightQuotient H)] :
    Finite (rightNontrivialSchreierPairs (F := F) H τ hτ ι) :=
  Finite.of_injective
    (fun p : rightNontrivialSchreierPairs (F := F) H τ hτ ι => p.1)
    (by
      intro a b h
      exact Subtype.ext h)

omit [IsTopologicalGroup F] in
theorem natCard_rightNontrivialSchreierPairs_le
    [Finite X] [Finite (OpenSubgroupRightQuotient H)] :
    Nat.card (rightNontrivialSchreierPairs (F := F) H τ hτ ι) ≤
      Nat.card (OpenSubgroupRightQuotient H) * Nat.card X := by
  have hle :
      Nat.card (rightNontrivialSchreierPairs (F := F) H τ hτ ι) ≤
        Nat.card (OpenSubgroupRightQuotient H × X) := by
    exact Nat.card_le_card_of_injective
      (fun p : rightNontrivialSchreierPairs (F := F) H τ hτ ι => p.1)
      (by
        intro a b h
        exact Subtype.ext h)
  simpa [Nat.card_prod] using hle

omit [IsTopologicalGroup F] in
/-- The tautological map from nontrivial right Schreier pairs to the nontrivial generator set. -/
noncomputable def rightNontrivialSchreierPairsToGeneratorSet :
    rightNontrivialSchreierPairs (F := F) H τ hτ ι →
      ↥(rightSchreierGeneratorSet (F := F) H τ hτ ι) := fun p =>
  ⟨rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) p.1.1 p.1.2,
    ⟨p.1.1, p.1.2, rfl, p.2⟩⟩

omit [IsTopologicalGroup F] in
@[simp] theorem rightNontrivialSchreierPairsToGeneratorSet_apply
    (p : rightNontrivialSchreierPairs (F := F) H τ hτ ι) :
    ((rightNontrivialSchreierPairsToGeneratorSet (F := F) H τ hτ ι p :
        ↥(rightSchreierGeneratorSet (F := F) H τ hτ ι)) : ↥(H : Subgroup F)) =
      rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι)
        p.1.1 p.1.2 :=
  rfl

omit [IsTopologicalGroup F] in
theorem surjective_rightNontrivialSchreierPairsToGeneratorSet :
    Function.Surjective
      (rightNontrivialSchreierPairsToGeneratorSet (F := F) H τ hτ ι) := by
  intro z
  rcases z.2 with ⟨q, x, hz, hz_ne⟩
  refine ⟨⟨(q, x), ?_⟩, ?_⟩
  · simpa [hz] using hz_ne
  · apply Subtype.ext
    exact hz.symm

omit [IsTopologicalGroup F] in
theorem natCard_rightSchreierGeneratorSet_le_nontrivialPairs
    [Finite X] [Finite (OpenSubgroupRightQuotient H)] :
    Nat.card (rightSchreierGeneratorSet (F := F) H τ hτ ι) ≤
      Nat.card (rightNontrivialSchreierPairs (F := F) H τ hτ ι) := by
  exact Nat.card_le_card_of_surjective
    (rightNontrivialSchreierPairsToGeneratorSet (F := F) H τ hτ ι)
    (surjective_rightNontrivialSchreierPairsToGeneratorSet
      (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι))

omit [IsTopologicalGroup F] in
theorem mem_rightSchreierGeneratorSet
    {H : OpenSubgroup F}
    {τ : OpenSubgroupRightQuotient H → F}
    {hτ : ∀ q, Quotient.mk'' (τ q) = q}
    {ι : X → F} {z : ↥(H : Subgroup F)} :
    z ∈ rightSchreierGeneratorSet (F := F) H τ hτ ι ↔
      ∃ q : OpenSubgroupRightQuotient H, ∃ x : X,
        z = rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x ∧
          z ≠ 1 :=
  Iff.rfl

omit [IsTopologicalGroup F] in
theorem rightSchreierGeneratorSet_subset_range :
    rightSchreierGeneratorSet (F := F) H τ hτ ι ⊆
      Set.range (fun p : OpenSubgroupRightQuotient H × X =>
        rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) p.1 p.2) := by
  intro z hz
  rcases hz with ⟨q, x, rfl, _⟩
  exact ⟨(q, x), rfl⟩

omit [IsTopologicalGroup F] in
theorem subgroupClosure_rightSchreierGeneratorSet_eq_closure_range :
    Subgroup.closure (rightSchreierGeneratorSet (F := F) H τ hτ ι) =
      Subgroup.closure (Set.range fun p : OpenSubgroupRightQuotient H × X =>
        rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) p.1 p.2) := by
  simpa [rightSchreierGeneratorSet, SchreierSection.generatorSet] using
    ((rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierSection (F := F) (X := X) H).subgroupClosure_generatorSet_eq_closure_range ι)

theorem topologicallyGenerates_rightSchreierGeneratorSet_iff
    {H : OpenSubgroup F}
    {τ : OpenSubgroupRightQuotient H → F}
    {hτ : ∀ q, Quotient.mk'' (τ q) = q}
    {ι : X → F} :
    ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (rightSchreierGeneratorSet (F := F) H τ hτ ι) ↔
      ProCGroups.Generation.TopologicallyGenerates (G := ↥(H : Subgroup F))
        (Set.range fun p : OpenSubgroupRightQuotient H × X =>
          rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) p.1 p.2) := by
  simpa [rightSchreierGeneratorSet, SchreierSection.generatorSet] using
    ((rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierSection (F := F) (X := X) H).topologicallyGenerates_generatorSet_iff ι)

theorem natCard_rightSchreierGeneratorSet_le
    [CompactSpace F] [Finite X] :
    Nat.card (rightSchreierGeneratorSet (F := F) H τ hτ ι) ≤
      Nat.card (OpenSubgroupRightQuotient H) * Nat.card X := by
  letI : Finite
      (rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierSection (F := F) (X := X) H).Q :=
    inferInstanceAs (Finite (OpenSubgroupRightQuotient H))
  simpa [rightSchreierGeneratorSet, SchreierSection.generatorSet, rightSchreierSection,
    Nat.card_eq_fintype_card] using
    ((rightSchreierSection (F := F) (H := H) (τ := τ) (hτ := hτ) :
        SchreierSection (F := F) (X := X) H).natCard_generatorSet_le ι)

omit [IsTopologicalGroup F] in
/-- The basepoint projection induced by a wreath-product homomorphism evaluates a right Schreier
generator by the corresponding left coordinate. -/
theorem rightQuotientBasepointProjectionHom_rightSchreierGenerator
    {A : Type*} [Group A]
    (ψ : F →* PermutationalWreathProduct A (OpenSubgroupRightQuotient H) F)
    (hψ :
      (SemidirectProduct.rightHom :
          PermutationalWreathProduct A (OpenSubgroupRightQuotient H) F →* F).comp ψ =
        MonoidHom.id F)
    (hτpure :
      ∀ q : OpenSubgroupRightQuotient H,
        wreathLeftCoordinate ψ
            (openSubgroupRightCoset H (1 : F)) (τ q) = 1)
    (q : OpenSubgroupRightQuotient H) (x : X) :
    rightQuotientBasepointProjectionHom (H : Subgroup F) ψ hψ
        (rightSchreierGenerator (F := F) (H := H) (τ := τ) (hτ := hτ) (ι := ι) q x) =
      wreathLeftCoordinate ψ q (ι x) := by
  exact rightQuotientBasepointProjectionHom_apply_cocycle
    (H : Subgroup F) τ hτ ψ hψ hτpure (ι x) q

end RightSchreierGenerators

end Profinite
end ReidemeisterSchreier
