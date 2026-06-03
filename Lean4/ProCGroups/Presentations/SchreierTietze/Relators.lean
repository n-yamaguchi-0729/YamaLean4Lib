import ProCGroups.Presentations.Profinite

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Presentations/SchreierTietze/Relators.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite presentations

Presentation-level API for profinite groups, finite quotients, relators, and Schreier-Tietze restrictions.
-/

noncomputable section

open scoped Topology

namespace ProCGroups.Presentations

universe u v w

section RelatorIndexing

variable {F : Type u}

/-- The relator set represented by an indexed family.  This is the profinite analogue of the
``relator family'' notation used in Reidemeister-Schreier/Tietze arguments. -/
def relatorFamilySet {ι : Sort v} (r : ι → F) : Set F :=
  Set.range r

@[simp] theorem mem_relatorFamilySet {ι : Sort v} (r : ι → F) (x : F) :
    x ∈ relatorFamilySet r ↔ ∃ i, r i = x :=
  Iff.rfl

/-- The relator set represented by a finite list.  This avoids quotienting the list by
permutation; order and repetitions are syntactic data, while the closed normal closure only sees
the induced set. -/
def relatorListSet (l : List F) : Set F :=
  {x | x ∈ l}

@[simp] theorem mem_relatorListSet (l : List F) (x : F) :
    x ∈ relatorListSet l ↔ x ∈ l :=
  Iff.rfl

@[simp] theorem relatorListSet_nil :
    relatorListSet ([] : List F) = (∅ : Set F) := by
  ext x
  simp only [relatorListSet, List.not_mem_nil, Set.setOf_false, Set.mem_empty_iff_false]

@[simp] theorem relatorListSet_cons (x : F) (l : List F) :
    relatorListSet (x :: l) = ({x} : Set F) ∪ relatorListSet l := by
  ext y
  simp only [relatorListSet, List.mem_cons, Set.mem_setOf_eq, Set.singleton_union, Set.mem_insert_iff]

@[simp] theorem relatorListSet_append (l m : List F) :
    relatorListSet (l ++ m) = relatorListSet l ∪ relatorListSet m := by
  ext x
  simp only [relatorListSet, List.mem_append, Set.mem_setOf_eq, Set.mem_union]

/-- The relator set represented by a finset. -/
def relatorFinsetSet (s : Finset F) : Set F :=
  {x | x ∈ s}

@[simp] theorem mem_relatorFinsetSet (s : Finset F) (x : F) :
    x ∈ relatorFinsetSet s ↔ x ∈ s :=
  Iff.rfl

@[simp] theorem relatorFinsetSet_empty :
    relatorFinsetSet (∅ : Finset F) = (∅ : Set F) := by
  ext x
  simp only [relatorFinsetSet, Finset.notMem_empty, Set.setOf_false, Set.mem_empty_iff_false]

@[simp] theorem relatorFinsetSet_insert [DecidableEq F] (x : F) (s : Finset F) :
    relatorFinsetSet (insert x s) = ({x} : Set F) ∪ relatorFinsetSet s := by
  ext y
  simp only [relatorFinsetSet, Finset.mem_insert, Set.mem_setOf_eq, SetLike.setOf_mem_eq, Set.singleton_union,
  Set.mem_insert_iff, SetLike.mem_coe]

@[simp] theorem relatorFinsetSet_union [DecidableEq F] (s t : Finset F) :
    relatorFinsetSet (s ∪ t) = relatorFinsetSet s ∪ relatorFinsetSet t := by
  ext x
  simp only [relatorFinsetSet, Finset.mem_union, Set.mem_setOf_eq, SetLike.setOf_mem_eq, Set.mem_union,
  SetLike.mem_coe]

/-- The relator set obtained from a Schreier rewriting map `τ`, a family of transversal labels,
and a family of original relators.  This is the profinite/presentation-level spelling of
`{ τ(t,r) | t ∈ T, r ∈ R }`. -/
def schreierRelatorSet {Q : Type v} {A : Type w}
    (τ : Q → A → F) (T : Set Q) (R : Set A) : Set F :=
  {x | ∃ t ∈ T, ∃ r ∈ R, τ t r = x}

@[simp] theorem mem_schreierRelatorSet
    {Q : Type v} {A : Type w}
    (τ : Q → A → F) (T : Set Q) (R : Set A) (x : F) :
    x ∈ schreierRelatorSet τ T R ↔ ∃ t ∈ T, ∃ r ∈ R, τ t r = x :=
  Iff.rfl

/-- List version of a Schreier rewritten relator family. -/
def schreierRelatorList {Q : Type v} {A : Type w}
    (τ : Q → A → F) : List Q → List A → List F
  | [], _ => []
  | t :: ts, rs => rs.map (τ t) ++ schreierRelatorList τ ts rs

@[simp] theorem mem_schreierRelatorList
    {Q : Type v} {A : Type w}
    (τ : Q → A → F) (ts : List Q) (rs : List A) (x : F) :
    x ∈ schreierRelatorList τ ts rs ↔ ∃ t ∈ ts, ∃ r ∈ rs, τ t r = x := by
  induction ts with
  | nil =>
      simp only [schreierRelatorList, List.not_mem_nil, false_and, exists_false]
  | cons t ts ih =>
      simp only [schreierRelatorList, List.mem_append, List.mem_map, ih, List.mem_cons, exists_eq_or_imp]

@[simp] theorem relatorListSet_schreierRelatorList
    {Q : Type v} {A : Type w}
    (τ : Q → A → F) (ts : List Q) (rs : List A) :
    relatorListSet (schreierRelatorList τ ts rs) =
      schreierRelatorSet τ (relatorListSet ts) (relatorListSet rs) := by
  ext x
  simp only [mem_relatorListSet, mem_schreierRelatorList, schreierRelatorSet, Set.mem_setOf_eq]

/-- Finset version of a Schreier rewritten relator family. -/
def schreierRelatorFinset {Q : Type v} {A : Type w} [DecidableEq F]
    (τ : Q → A → F) (ts : Finset Q) (rs : Finset A) : Finset F :=
  ts.biUnion fun t => rs.image (τ t)

@[simp] theorem mem_schreierRelatorFinset
    {Q : Type v} {A : Type w} [DecidableEq F]
    (τ : Q → A → F) (ts : Finset Q) (rs : Finset A) (x : F) :
    x ∈ schreierRelatorFinset τ ts rs ↔ ∃ t ∈ ts, ∃ r ∈ rs, τ t r = x := by
  simp only [schreierRelatorFinset, Finset.mem_biUnion, Finset.mem_image]

@[simp] theorem relatorFinsetSet_schreierRelatorFinset
    {Q : Type v} {A : Type w} [DecidableEq F]
    (τ : Q → A → F) (ts : Finset Q) (rs : Finset A) :
    relatorFinsetSet (schreierRelatorFinset τ ts rs) =
      schreierRelatorSet τ (relatorFinsetSet ts) (relatorFinsetSet rs) := by
  ext x
  simp only [mem_relatorFinsetSet, mem_schreierRelatorFinset, schreierRelatorSet, Set.mem_setOf_eq]

end RelatorIndexing

section RelatorPresentations

variable (C : ProCGroups.FiniteGroupClass.{u})
variable {F G : Type u} [Group F] [Group G]
variable [TopologicalSpace F] [TopologicalSpace G]
variable [IsTopologicalGroup F] [IsTopologicalGroup G]

/-- A pro-`C` presentation whose relator kernel is the closed normal closure of `R`. -/
def IsRelatorPresentationOf (R : Set F) : Prop :=
  IsQuotientByKernel C (F := F) (G := G) (closedNormalClosure R)

/-- A pro-`C` presentation `G = ⟨X | R⟩` whose source is the chosen free pro-`C`
group on `X`. -/
def IsFreeRelatorPresentationOfClass
    {X : Type u} [TopologicalSpace X] (ι : X → F) (R : Set F) : Prop :=
  IsFreePresentationOfClass C (G := G) ι R

theorem IsFreeRelatorPresentationOfClass.isRelatorPresentationOf
    {X : Type u} [TopologicalSpace X] {ι : X → F} {R : Set F} :
    IsFreeRelatorPresentationOfClass C (G := G) ι R →
      IsRelatorPresentationOf C (G := G) R := by
  intro h
  exact IsFreePresentationOfClass.isQuotientByKernel C h

/-- Tietze equivalence of two relator sets in the same profinite source. -/
structure RelatorTietzeData (R S : Set F) : Prop where
  left_relators : R ⊆ closedNormalClosure S
  right_relators : S ⊆ closedNormalClosure R

namespace RelatorTietzeData

variable {C}
variable {R S T : Set F}

theorem closedNormalClosure_eq (D : RelatorTietzeData R S) :
    closedNormalClosure R = closedNormalClosure S :=
  closedNormalClosure_eq_of_mutual_le D.left_relators D.right_relators

def refl (R : Set F) : RelatorTietzeData R R where
  left_relators := subset_closedNormalClosure R
  right_relators := subset_closedNormalClosure R

def symm (D : RelatorTietzeData R S) : RelatorTietzeData S R where
  left_relators := D.right_relators
  right_relators := D.left_relators

def trans (D₁ : RelatorTietzeData R S) (D₂ : RelatorTietzeData S T) :
    RelatorTietzeData R T where
  left_relators := by
    have hST : closedNormalClosure S ≤ closedNormalClosure T :=
      closedNormalClosure_le_closed_normal
        (F := F) (N := closedNormalClosure T)
        (closedNormalClosure_isClosed (F := F) T) D₂.left_relators
    exact fun x hx => hST (D₁.left_relators hx)
  right_relators := by
    have hSR : closedNormalClosure S ≤ closedNormalClosure R :=
      closedNormalClosure_le_closed_normal
        (F := F) (N := closedNormalClosure R)
        (closedNormalClosure_isClosed (F := F) R) D₁.right_relators
    exact fun x hx => hSR (D₂.right_relators hx)

theorem presentation (D : RelatorTietzeData R S) :
    IsRelatorPresentationOf C (G := G) R →
      IsRelatorPresentationOf C (G := G) S := by
  intro h
  simpa [IsRelatorPresentationOf, D.closedNormalClosure_eq] using h

theorem presentation_iff (D : RelatorTietzeData R S) :
    IsRelatorPresentationOf C (G := G) R ↔
      IsRelatorPresentationOf C (G := G) S := by
  constructor
  · exact D.presentation
  · exact D.symm.presentation

def of_closedNormalClosure_eq (h : closedNormalClosure R = closedNormalClosure S) :
    RelatorTietzeData R S where
  left_relators := by
    intro x hx
    simpa [h] using subset_closedNormalClosure (F := F) R hx
  right_relators := by
    intro x hx
    simpa [h] using subset_closedNormalClosure (F := F) S hx

def add_redundant_relators (hS : S ⊆ closedNormalClosure R) :
    RelatorTietzeData (R ∪ S) R where
  left_relators := by
    intro x hx
    exact hx.elim
      (fun hxR => subset_closedNormalClosure (F := F) R hxR)
      (fun hxS => hS hxS)
  right_relators := by
    intro x hx
    exact subset_closedNormalClosure (F := F) (R ∪ S) (Or.inl hx)

def delete_redundant_relators (hS : S ⊆ closedNormalClosure R) :
    RelatorTietzeData R (R ∪ S) :=
  (add_redundant_relators (F := F) hS).symm

def removeRelatorSubset (hS : S ⊆ closedNormalClosure (R \ S)) :
    RelatorTietzeData R (R \ S) where
  left_relators := by
    intro x hxR
    by_cases hxS : x ∈ S
    · exact hS hxS
    · exact subset_closedNormalClosure (F := F) (R \ S) ⟨hxR, hxS⟩
  right_relators := by
    intro x hx
    exact subset_closedNormalClosure (F := F) R hx.1

def replaceRelatorSubset
    {D E : Set F}
    (hD : D ⊆ closedNormalClosure ((R \ D) ∪ E))
    (hE : E ⊆ closedNormalClosure R) :
    RelatorTietzeData R ((R \ D) ∪ E) where
  left_relators := by
    intro x hxR
    by_cases hxD : x ∈ D
    · exact hD hxD
    · exact subset_closedNormalClosure (F := F) ((R \ D) ∪ E) (Or.inl ⟨hxR, hxD⟩)
  right_relators := by
    intro x hx
    exact hx.elim
      (fun hxRD => subset_closedNormalClosure (F := F) R hxRD.1)
      (fun hxE => hE hxE)

def replaceRelator
    {r s : F}
    (hr : r ∈ closedNormalClosure ((R \ {r}) ∪ ({s} : Set F)))
    (hs : s ∈ closedNormalClosure R) :
    RelatorTietzeData R ((R \ {r}) ∪ ({s} : Set F)) :=
  replaceRelatorSubset (F := F) (R := R) (D := ({r} : Set F)) (E := ({s} : Set F))
    (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact hr)
    (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact hs)

def add_trivial_relators
    {D : Set F} (hD : D ⊆ ({1} : Set F)) :
    RelatorTietzeData (R ∪ D) R :=
  add_redundant_relators (F := F) (R := R) (S := D)
    (subset_closedNormalClosure_of_subset_singleton_one (F := F) hD)

def delete_trivial_relators
    {D : Set F} (hD : D ⊆ ({1} : Set F)) :
    RelatorTietzeData R (R ∪ D) :=
  (add_trivial_relators (F := F) (R := R) hD).symm

end RelatorTietzeData

theorem isRelatorPresentationOf_of_kernelTietzeData
    {E : Type u} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
    {R : Set F} {S : Set E}
    (D : KernelTietzeData (closedNormalClosure R) (closedNormalClosure S)) :
    IsRelatorPresentationOf C (G := G) R →
      IsRelatorPresentationOf C (F := E) (G := G) S := by
  exact isPresentationOf_of_kernelTietzeData C D

/-- Same-source relator Tietze data is enough for cosmetic cleaning.  This structure is the
cross-source version used when a Tietze step also changes the Schreier generator source.  The
recorded homomorphisms only have to carry the named relators into the opposite closed normal
closure and be inverse modulo the corresponding closed normal closures. -/
structure RelatorMapTietzeData
    {E : Type u} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
    (R : Set F) (S : Set E) where
  toHom : F →ₜ* E
  invHom : E →ₜ* F
  maps_relators : R ⊆ Subgroup.comap toHom.toMonoidHom (closedNormalClosure S)
  maps_target_relators : S ⊆ Subgroup.comap invHom.toMonoidHom (closedNormalClosure R)
  inv_toHom : ∀ x : F, invHom (toHom x) * x⁻¹ ∈ closedNormalClosure R
  to_invHom : ∀ y : E, toHom (invHom y) * y⁻¹ ∈ closedNormalClosure S

namespace RelatorMapTietzeData

variable {C}
variable {R S : Set F}

def ofRelatorTietzeData (D : RelatorTietzeData R S) :
    RelatorMapTietzeData R S where
  toHom := ContinuousMonoidHom.id F
  invHom := ContinuousMonoidHom.id F
  maps_relators := by
    intro x hx
    simpa using D.left_relators hx
  maps_target_relators := by
    intro x hx
    simpa using D.right_relators hx
  inv_toHom := by
    intro x
    simp only [ContinuousMonoidHom.id_toFun, mul_inv_cancel, one_mem]
  to_invHom := by
    intro x
    simp only [ContinuousMonoidHom.id_toFun, mul_inv_cancel, one_mem]

variable {E : Type u} [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
variable {R : Set F} {S : Set E}

theorem maps_closedNormalClosure (D : RelatorMapTietzeData R S) :
    closedNormalClosure R ≤ Subgroup.comap D.toHom.toMonoidHom (closedNormalClosure S) := by
  let N : Subgroup F := Subgroup.comap D.toHom.toMonoidHom (closedNormalClosure S)
  haveI : N.Normal := by
    dsimp [N]
    infer_instance
  have hNclosed : IsClosed (N : Set F) := by
    change IsClosed (D.toHom ⁻¹' ((closedNormalClosure S : Subgroup E) : Set E))
    exact (closedNormalClosure_isClosed (F := E) S).preimage D.toHom.continuous_toFun
  exact closedNormalClosure_le_closed_normal (F := F) (N := N) hNclosed D.maps_relators

theorem maps_target_closedNormalClosure (D : RelatorMapTietzeData R S) :
    closedNormalClosure S ≤ Subgroup.comap D.invHom.toMonoidHom (closedNormalClosure R) := by
  let N : Subgroup E := Subgroup.comap D.invHom.toMonoidHom (closedNormalClosure R)
  haveI : N.Normal := by
    dsimp [N]
    infer_instance
  have hNclosed : IsClosed (N : Set E) := by
    change IsClosed (D.invHom ⁻¹' ((closedNormalClosure R : Subgroup F) : Set F))
    exact (closedNormalClosure_isClosed (F := F) R).preimage D.invHom.continuous_toFun
  exact closedNormalClosure_le_closed_normal (F := E) (N := N) hNclosed
    D.maps_target_relators

def toKernelTietzeData (D : RelatorMapTietzeData R S) :
    KernelTietzeData (closedNormalClosure R) (closedNormalClosure S) where
  toHom := D.toHom
  invHom := D.invHom
  mapsKernel := D.maps_closedNormalClosure
  mapsTargetKernel := D.maps_target_closedNormalClosure
  inv_toHom := D.inv_toHom
  to_invHom := D.to_invHom

theorem presentation (D : RelatorMapTietzeData R S) :
    IsRelatorPresentationOf C (G := G) R →
      IsRelatorPresentationOf C (F := E) (G := G) S :=
  isRelatorPresentationOf_of_kernelTietzeData C D.toKernelTietzeData

end RelatorMapTietzeData

theorem isRelatorPresentationOf_delete_redundant_relators
    {R D : Set F} (hD : D ⊆ closedNormalClosure R) :
    IsRelatorPresentationOf C (G := G) (R ∪ D) →
      IsRelatorPresentationOf C (G := G) R := by
  intro h
  simpa [IsRelatorPresentationOf, closedNormalClosure_union_eq_left (F := F) hD] using h

theorem isRelatorPresentationOf_add_redundant_relators
    {R D : Set F} (hD : D ⊆ closedNormalClosure R) :
    IsRelatorPresentationOf C (G := G) R →
      IsRelatorPresentationOf C (G := G) (R ∪ D) := by
  intro h
  simpa [IsRelatorPresentationOf, closedNormalClosure_union_eq_left (F := F) hD] using h

theorem isRelatorPresentationOf_delete_trivial_relators
    {R D : Set F} (hD : D ⊆ ({1} : Set F)) :
    IsRelatorPresentationOf C (G := G) (R ∪ D) →
      IsRelatorPresentationOf C (G := G) R :=
  isRelatorPresentationOf_delete_redundant_relators C
    (subset_closedNormalClosure_of_subset_singleton_one (F := F) hD)

theorem isRelatorPresentationOf_add_trivial_relators
    {R D : Set F} (hD : D ⊆ ({1} : Set F)) :
    IsRelatorPresentationOf C (G := G) R →
      IsRelatorPresentationOf C (G := G) (R ∪ D) :=
  isRelatorPresentationOf_add_redundant_relators C
    (subset_closedNormalClosure_of_subset_singleton_one (F := F) hD)

/-- The named relator families appearing in a profinite Reidemeister-Schreier presentation:
rewrites of the original relators, degenerate Schreier-generator relators, and a cleaned family
after Tietze deletions/substitutions. -/
structure ProfiniteSchreierRelatorSets (F : Type u) where
  rewritten : Set F
  degenerate : Set F
  cleaned : Set F

namespace ProfiniteSchreierRelatorSets

/-- The raw Schreier relators: rewritten original relators plus degenerate generator relators. -/
def raw (S : ProfiniteSchreierRelatorSets F) : Set F :=
  S.rewritten ∪ S.degenerate

/-- Data saying that the relators in `D` are redundant relative to `R` in the same ambient free
group.  This is relator deletion, not generator deletion: the presentation source is unchanged. -/
structure RedundantRelatorDeletionData (R D : Set F) : Prop where
  redundant : D ⊆ closedNormalClosure R

namespace RedundantRelatorDeletionData

variable {R D : Set F}

theorem closedNormalClosure_union_eq_left (H : RedundantRelatorDeletionData (F := F) R D) :
    closedNormalClosure (R ∪ D) = closedNormalClosure R := by
  exact _root_.ProCGroups.Presentations.closedNormalClosure_union_eq_left (F := F) H.redundant

theorem relatorTietze_union_left (H : RedundantRelatorDeletionData (F := F) R D) :
    RelatorTietzeData (R ∪ D) R where
  left_relators := by
    intro x hx
    have hx' : x ∈ closedNormalClosure (R ∪ D) :=
      subset_closedNormalClosure (F := F) (R ∪ D) hx
    simpa [H.closedNormalClosure_union_eq_left] using hx'
  right_relators := by
    intro x hx
    exact subset_closedNormalClosure (F := F) (R ∪ D) (Or.inl hx)

theorem isRelatorPresentationOf_delete_redundant_relators
    (H : RedundantRelatorDeletionData (F := F) R D) :
    IsRelatorPresentationOf C (G := G) (R ∪ D) →
      IsRelatorPresentationOf C (G := G) R :=
  H.relatorTietze_union_left.presentation

end RedundantRelatorDeletionData

/-- Tietze data for genuine generator deletion, where the ambient free group may change.

Unlike `RedundantRelatorDeletionData`, this records maps between two presentation sources and
inverse data modulo the respective closed normal closures. -/
structure GeneratorDeletionTietzeData
    (Fraw Fclean : Type u)
    [Group Fraw] [TopologicalSpace Fraw] [IsTopologicalGroup Fraw]
    [Group Fclean] [TopologicalSpace Fclean] [IsTopologicalGroup Fclean]
    (Rraw : Set Fraw) (Rclean : Set Fclean) where
  mapRawToClean : Fraw →* Fclean
  mapCleanToRaw : Fclean →* Fraw
  relators_forward : mapRawToClean '' Rraw ⊆ closedNormalClosure Rclean
  relators_backward : mapCleanToRaw '' Rclean ⊆ closedNormalClosure Rraw
  inverse_mod_relators_raw :
    ∀ x : Fraw, mapCleanToRaw (mapRawToClean x) * x⁻¹ ∈ closedNormalClosure Rraw
  inverse_mod_relators_clean :
    ∀ x : Fclean, mapRawToClean (mapCleanToRaw x) * x⁻¹ ∈ closedNormalClosure Rclean

/-- Schreier-specific redundant-relator deletion for degenerate relators. -/
abbrev DegenerateRelatorDeletionData (S : ProfiniteSchreierRelatorSets F) : Prop :=
  RedundantRelatorDeletionData S.rewritten S.degenerate

namespace DegenerateRelatorDeletionData

variable {S : ProfiniteSchreierRelatorSets F}

theorem closedNormalClosure_raw_eq_rewritten (D : DegenerateRelatorDeletionData S) :
    closedNormalClosure S.raw = closedNormalClosure S.rewritten := by
  exact D.closedNormalClosure_union_eq_left

theorem relatorTietze_raw_rewritten (D : DegenerateRelatorDeletionData S) :
    RelatorTietzeData S.raw S.rewritten :=
  D.relatorTietze_union_left

theorem isRelatorPresentationOf_delete_degenerate_relators
    (D : DegenerateRelatorDeletionData S) :
    IsRelatorPresentationOf C (G := G) S.raw →
      IsRelatorPresentationOf C (G := G) S.rewritten :=
  D.relatorTietze_raw_rewritten.presentation

end DegenerateRelatorDeletionData

/-- Cleaning data saying that degenerate relators are Tietze-redundant and that the cleaned
family generates the same closed normal subgroup as the rewritten relators. -/
structure CleaningData (S : ProfiniteSchreierRelatorSets F) : Prop where
  degenerate_le : S.degenerate ⊆ closedNormalClosure S.rewritten
  rewritten_le_cleaned : S.rewritten ⊆ closedNormalClosure S.cleaned
  cleaned_le_rewritten : S.cleaned ⊆ closedNormalClosure S.rewritten

namespace CleaningData

variable {S : ProfiniteSchreierRelatorSets F}

def toDegenerateRelatorDeletionData (D : CleaningData S) :
    DegenerateRelatorDeletionData S where
  redundant := D.degenerate_le

theorem closedNormalClosure_raw_eq_rewritten (D : CleaningData S) :
    closedNormalClosure S.raw = closedNormalClosure S.rewritten := by
  exact D.toDegenerateRelatorDeletionData.closedNormalClosure_raw_eq_rewritten

theorem relatorTietze_raw_rewritten (D : CleaningData S) :
    RelatorTietzeData S.raw S.rewritten :=
  D.toDegenerateRelatorDeletionData.relatorTietze_raw_rewritten

theorem relatorTietze_rewritten_cleaned (D : CleaningData S) :
    RelatorTietzeData S.rewritten S.cleaned where
  left_relators := D.rewritten_le_cleaned
  right_relators := D.cleaned_le_rewritten

theorem relatorTietze_raw_cleaned (D : CleaningData S) :
    RelatorTietzeData S.raw S.cleaned :=
  (D.relatorTietze_raw_rewritten).trans D.relatorTietze_rewritten_cleaned

theorem closedNormalClosure_raw_eq_cleaned (D : CleaningData S) :
    closedNormalClosure S.raw = closedNormalClosure S.cleaned :=
  D.relatorTietze_raw_cleaned.closedNormalClosure_eq

theorem isRelatorPresentationOf_cleaned
    (D : CleaningData S) :
    IsRelatorPresentationOf C (G := G) S.raw →
      IsRelatorPresentationOf C (G := G) S.cleaned :=
  D.relatorTietze_raw_cleaned.presentation

theorem isRelatorPresentationOf_cleaned_iff
    (D : CleaningData S) :
    IsRelatorPresentationOf C (G := G) S.raw ↔
      IsRelatorPresentationOf C (G := G) S.cleaned :=
  D.relatorTietze_raw_cleaned.presentation_iff

end CleaningData

end ProfiniteSchreierRelatorSets

/-- A list-level spelling of the three Schreier relator families.  It is useful for statements
whose input is literally a relator list in a paper or construction. -/
structure ProfiniteSchreierRelatorLists (F : Type u) where
  rewritten : List F
  degenerate : List F
  cleaned : List F

namespace ProfiniteSchreierRelatorLists

def raw (S : ProfiniteSchreierRelatorLists F) : List F :=
  S.rewritten ++ S.degenerate

def toRelatorSets (S : ProfiniteSchreierRelatorLists F) :
    ProfiniteSchreierRelatorSets F where
  rewritten := relatorListSet S.rewritten
  degenerate := relatorListSet S.degenerate
  cleaned := relatorListSet S.cleaned

omit [Group F] [TopologicalSpace F] [IsTopologicalGroup F] in
@[simp] theorem relatorListSet_raw (S : ProfiniteSchreierRelatorLists F) :
    relatorListSet S.raw = S.toRelatorSets.raw := by
  ext x
  simp only [raw, relatorListSet_append, Set.mem_union, mem_relatorListSet, ProfiniteSchreierRelatorSets.raw,
  toRelatorSets]

abbrev DegenerateRelatorDeletionData (S : ProfiniteSchreierRelatorLists F) : Prop :=
  ProfiniteSchreierRelatorSets.DegenerateRelatorDeletionData S.toRelatorSets

abbrev CleaningData (S : ProfiniteSchreierRelatorLists F) : Prop :=
  ProfiniteSchreierRelatorSets.CleaningData S.toRelatorSets

theorem isRelatorPresentationOf_delete_degenerate_relators
    {S : ProfiniteSchreierRelatorLists F}
    (D : DegenerateRelatorDeletionData S) :
    IsRelatorPresentationOf C (G := G) (relatorListSet S.raw) →
      IsRelatorPresentationOf C (G := G) (relatorListSet S.rewritten) := by
  intro h
  have hraw : IsRelatorPresentationOf C (G := G) S.toRelatorSets.raw := by
    simpa [relatorListSet_raw] using h
  have hrewritten :
      IsRelatorPresentationOf C (G := G) S.toRelatorSets.rewritten :=
    ProfiniteSchreierRelatorSets.DegenerateRelatorDeletionData.isRelatorPresentationOf_delete_degenerate_relators
      (C := C) (G := G) D hraw
  simpa [toRelatorSets] using hrewritten

theorem isRelatorPresentationOf_cleaned
    {S : ProfiniteSchreierRelatorLists F}
    (D : CleaningData S) :
    IsRelatorPresentationOf C (G := G) (relatorListSet S.raw) →
      IsRelatorPresentationOf C (G := G) (relatorListSet S.cleaned) := by
  intro h
  have hraw : IsRelatorPresentationOf C (G := G) S.toRelatorSets.raw := by
    simpa [relatorListSet_raw] using h
  have hcleaned :
      IsRelatorPresentationOf C (G := G) S.toRelatorSets.cleaned :=
    ProfiniteSchreierRelatorSets.CleaningData.isRelatorPresentationOf_cleaned
      (C := C) (G := G) D hraw
  simpa [toRelatorSets] using hcleaned

theorem isRelatorPresentationOf_cleaned_iff
    {S : ProfiniteSchreierRelatorLists F}
    (D : CleaningData S) :
    IsRelatorPresentationOf C (G := G) (relatorListSet S.raw) ↔
      IsRelatorPresentationOf C (G := G) (relatorListSet S.cleaned) := by
  have hsets :
      IsRelatorPresentationOf C (G := G) S.toRelatorSets.raw ↔
        IsRelatorPresentationOf C (G := G) S.toRelatorSets.cleaned :=
    ProfiniteSchreierRelatorSets.CleaningData.isRelatorPresentationOf_cleaned_iff
      (C := C) (G := G) D
  simpa [relatorListSet_raw, toRelatorSets] using hsets

end ProfiniteSchreierRelatorLists

/-- A finset-level spelling of the three Schreier relator families. -/
structure ProfiniteSchreierRelatorFinsets (F : Type u) where
  rewritten : Finset F
  degenerate : Finset F
  cleaned : Finset F

namespace ProfiniteSchreierRelatorFinsets

def raw [DecidableEq F] (S : ProfiniteSchreierRelatorFinsets F) : Finset F :=
  S.rewritten ∪ S.degenerate

def toRelatorSets (S : ProfiniteSchreierRelatorFinsets F) :
    ProfiniteSchreierRelatorSets F where
  rewritten := relatorFinsetSet S.rewritten
  degenerate := relatorFinsetSet S.degenerate
  cleaned := relatorFinsetSet S.cleaned

omit [Group F] [TopologicalSpace F] [IsTopologicalGroup F] in
@[simp] theorem relatorFinsetSet_raw [DecidableEq F] (S : ProfiniteSchreierRelatorFinsets F) :
    relatorFinsetSet S.raw = S.toRelatorSets.raw := by
  ext x
  simp only [raw, relatorFinsetSet_union, Set.mem_union, mem_relatorFinsetSet, ProfiniteSchreierRelatorSets.raw,
  toRelatorSets]

abbrev DegenerateRelatorDeletionData (S : ProfiniteSchreierRelatorFinsets F) : Prop :=
  ProfiniteSchreierRelatorSets.DegenerateRelatorDeletionData S.toRelatorSets

abbrev CleaningData (S : ProfiniteSchreierRelatorFinsets F) : Prop :=
  ProfiniteSchreierRelatorSets.CleaningData S.toRelatorSets

theorem isRelatorPresentationOf_delete_degenerate_relators
    [DecidableEq F] {S : ProfiniteSchreierRelatorFinsets F}
    (D : DegenerateRelatorDeletionData S) :
    IsRelatorPresentationOf C (G := G) (relatorFinsetSet S.raw) →
      IsRelatorPresentationOf C (G := G) (relatorFinsetSet S.rewritten) := by
  intro h
  have hraw : IsRelatorPresentationOf C (G := G) S.toRelatorSets.raw := by
    simpa [relatorFinsetSet_raw] using h
  have hrewritten :
      IsRelatorPresentationOf C (G := G) S.toRelatorSets.rewritten :=
    ProfiniteSchreierRelatorSets.DegenerateRelatorDeletionData.isRelatorPresentationOf_delete_degenerate_relators
      (C := C) (G := G) D hraw
  simpa [toRelatorSets] using hrewritten

theorem isRelatorPresentationOf_cleaned
    [DecidableEq F] {S : ProfiniteSchreierRelatorFinsets F}
    (D : CleaningData S) :
    IsRelatorPresentationOf C (G := G) (relatorFinsetSet S.raw) →
      IsRelatorPresentationOf C (G := G) (relatorFinsetSet S.cleaned) := by
  intro h
  have hraw : IsRelatorPresentationOf C (G := G) S.toRelatorSets.raw := by
    simpa [relatorFinsetSet_raw] using h
  have hcleaned :
      IsRelatorPresentationOf C (G := G) S.toRelatorSets.cleaned :=
    ProfiniteSchreierRelatorSets.CleaningData.isRelatorPresentationOf_cleaned
      (C := C) (G := G) D hraw
  simpa [toRelatorSets] using hcleaned

end ProfiniteSchreierRelatorFinsets

/-- Schreier relator data built directly from a rewriting map `tau`.  The rewritten relators are
definitionally `{ tau(t,r) | t ∈ transversal, r ∈ originalRelators }`. -/
structure ProfiniteSchreierRewritingRelatorSets
    (Q : Type v) (A : Type w) (F : Type u) where
  tau : Q → A → F
  transversal : Set Q
  originalRelators : Set A
  degenerate : Set F
  cleaned : Set F

namespace ProfiniteSchreierRewritingRelatorSets

variable {Q : Type v} {A : Type w}

def rewritten (S : ProfiniteSchreierRewritingRelatorSets Q A F) : Set F :=
  schreierRelatorSet S.tau S.transversal S.originalRelators

def toRelatorSets (S : ProfiniteSchreierRewritingRelatorSets Q A F) :
    ProfiniteSchreierRelatorSets F where
  rewritten := S.rewritten
  degenerate := S.degenerate
  cleaned := S.cleaned

def raw (S : ProfiniteSchreierRewritingRelatorSets Q A F) : Set F :=
  S.toRelatorSets.raw

abbrev DegenerateRelatorDeletionData
    (S : ProfiniteSchreierRewritingRelatorSets Q A F) : Prop :=
  ProfiniteSchreierRelatorSets.DegenerateRelatorDeletionData S.toRelatorSets

abbrev CleaningData
    (S : ProfiniteSchreierRewritingRelatorSets Q A F) : Prop :=
  ProfiniteSchreierRelatorSets.CleaningData S.toRelatorSets

theorem isRelatorPresentationOf_delete_degenerate_relators
    {S : ProfiniteSchreierRewritingRelatorSets Q A F}
    (D : DegenerateRelatorDeletionData S) :
    IsRelatorPresentationOf C (G := G) S.toRelatorSets.raw →
      IsRelatorPresentationOf C (G := G) S.toRelatorSets.rewritten := by
  intro h
  exact
    ProfiniteSchreierRelatorSets.DegenerateRelatorDeletionData.isRelatorPresentationOf_delete_degenerate_relators
      (C := C) (G := G) D h

theorem isRelatorPresentationOf_cleaned
    {S : ProfiniteSchreierRewritingRelatorSets Q A F}
    (D : CleaningData S) :
    IsRelatorPresentationOf C (G := G) S.toRelatorSets.raw →
      IsRelatorPresentationOf C (G := G) S.toRelatorSets.cleaned := by
  intro h
  exact ProfiniteSchreierRelatorSets.CleaningData.isRelatorPresentationOf_cleaned
    (C := C) (G := G) D h

end ProfiniteSchreierRewritingRelatorSets

/-- List-level Schreier relator data built from a rewriting map `tau`. -/
structure ProfiniteSchreierRewritingRelatorLists
    (Q : Type v) (A : Type w) (F : Type u) where
  tau : Q → A → F
  transversal : List Q
  originalRelators : List A
  degenerate : List F
  cleaned : List F

namespace ProfiniteSchreierRewritingRelatorLists

variable {Q : Type v} {A : Type w}

def rewritten (S : ProfiniteSchreierRewritingRelatorLists Q A F) : List F :=
  schreierRelatorList S.tau S.transversal S.originalRelators

def toRelatorLists (S : ProfiniteSchreierRewritingRelatorLists Q A F) :
    ProfiniteSchreierRelatorLists F where
  rewritten := S.rewritten
  degenerate := S.degenerate
  cleaned := S.cleaned

def raw (S : ProfiniteSchreierRewritingRelatorLists Q A F) : List F :=
  S.toRelatorLists.raw

abbrev DegenerateRelatorDeletionData
    (S : ProfiniteSchreierRewritingRelatorLists Q A F) : Prop :=
  ProfiniteSchreierRelatorLists.DegenerateRelatorDeletionData S.toRelatorLists

abbrev CleaningData
    (S : ProfiniteSchreierRewritingRelatorLists Q A F) : Prop :=
  ProfiniteSchreierRelatorLists.CleaningData S.toRelatorLists

theorem isRelatorPresentationOf_delete_degenerate_relators
    {S : ProfiniteSchreierRewritingRelatorLists Q A F}
    (D : DegenerateRelatorDeletionData S) :
    IsRelatorPresentationOf C (G := G) (relatorListSet S.raw) →
      IsRelatorPresentationOf C (G := G) (relatorListSet S.rewritten) :=
  ProfiniteSchreierRelatorLists.isRelatorPresentationOf_delete_degenerate_relators
    (C := C) (G := G) D

theorem isRelatorPresentationOf_cleaned
    {S : ProfiniteSchreierRewritingRelatorLists Q A F}
    (D : CleaningData S) :
    IsRelatorPresentationOf C (G := G) (relatorListSet S.raw) →
      IsRelatorPresentationOf C (G := G) (relatorListSet S.cleaned) :=
  ProfiniteSchreierRelatorLists.isRelatorPresentationOf_cleaned
    (C := C) (G := G) D

end ProfiniteSchreierRewritingRelatorLists

/-- Finset-level Schreier relator data built from a rewriting map `tau`. -/
structure ProfiniteSchreierRewritingRelatorFinsets
    (Q : Type v) (A : Type w) (F : Type u) where
  tau : Q → A → F
  transversal : Finset Q
  originalRelators : Finset A
  degenerate : Finset F
  cleaned : Finset F

namespace ProfiniteSchreierRewritingRelatorFinsets

variable {Q : Type v} {A : Type w}

def rewritten [DecidableEq F] (S : ProfiniteSchreierRewritingRelatorFinsets Q A F) :
    Finset F :=
  schreierRelatorFinset S.tau S.transversal S.originalRelators

def toRelatorFinsets [DecidableEq F] (S : ProfiniteSchreierRewritingRelatorFinsets Q A F) :
    ProfiniteSchreierRelatorFinsets F where
  rewritten := S.rewritten
  degenerate := S.degenerate
  cleaned := S.cleaned

def raw [DecidableEq F] (S : ProfiniteSchreierRewritingRelatorFinsets Q A F) :
    Finset F :=
  S.toRelatorFinsets.raw

abbrev DegenerateRelatorDeletionData
    [DecidableEq F] (S : ProfiniteSchreierRewritingRelatorFinsets Q A F) : Prop :=
  ProfiniteSchreierRelatorFinsets.DegenerateRelatorDeletionData S.toRelatorFinsets

abbrev CleaningData
    [DecidableEq F] (S : ProfiniteSchreierRewritingRelatorFinsets Q A F) : Prop :=
  ProfiniteSchreierRelatorFinsets.CleaningData S.toRelatorFinsets

theorem isRelatorPresentationOf_delete_degenerate_relators
    [DecidableEq F] {S : ProfiniteSchreierRewritingRelatorFinsets Q A F}
    (D : DegenerateRelatorDeletionData S) :
    IsRelatorPresentationOf C (G := G) (relatorFinsetSet S.raw) →
      IsRelatorPresentationOf C (G := G) (relatorFinsetSet S.rewritten) :=
  ProfiniteSchreierRelatorFinsets.isRelatorPresentationOf_delete_degenerate_relators
    (C := C) (G := G) D

theorem isRelatorPresentationOf_cleaned
    [DecidableEq F] {S : ProfiniteSchreierRewritingRelatorFinsets Q A F}
    (D : CleaningData S) :
    IsRelatorPresentationOf C (G := G) (relatorFinsetSet S.raw) →
      IsRelatorPresentationOf C (G := G) (relatorFinsetSet S.cleaned) :=
  ProfiniteSchreierRelatorFinsets.isRelatorPresentationOf_cleaned
    (C := C) (G := G) D

end ProfiniteSchreierRewritingRelatorFinsets

end RelatorPresentations

end ProCGroups.Presentations
