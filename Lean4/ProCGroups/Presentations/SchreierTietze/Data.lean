import ProCGroups.Presentations.SchreierTietze.Restricted

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Presentations/SchreierTietze/Data.lean
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

section SchreierRelatorPresentationData

variable (C : ProCGroups.FiniteGroupClass.{u})
variable {E F G : Type u} [Group E] [Group F] [Group G]
variable [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G]
variable [IsTopologicalGroup E] [IsTopologicalGroup F] [IsTopologicalGroup G]

/-- The presentation map to an open-subgroup target after a proposed Schreier source
maps into the source preimage. -/
def schreierPresentationHom
    (π : F →ₜ* G) (U : Subgroup G)
    (α : E →ₜ* presentationSubgroupPreimage π U) : E →ₜ* U :=
  (restrictPresentationHom π U).comp α

/-- The same map, specialized to an open subgroup target. -/
def openSchreierPresentationHom
    (π : F →ₜ* G) (U : OpenSubgroup G)
    (α : E →ₜ* presentationSubgroupPreimage π (U : Subgroup G)) :
    E →ₜ* ↥(U : Subgroup G) :=
  schreierPresentationHom π (U : Subgroup G) α

/-- Abstract profinite Reidemeister-Schreier presentation data.

Here `E` is the proposed source on Schreier generators, `R` is the raw or cleaned
set of rewritten relators in `E`, and `α` is the continuous map from `E` to
`π⁻¹(U)`.  A concrete rewriting construction proves the two recorded facts:
surjectivity onto `U` and equality of the kernel with the closed normal closure
of the rewritten relators. -/
structure SchreierRelatorPresentationData
    (π : F →ₜ* G) (U : Subgroup G) (R : Set E) where
  targetProC : ProCGroups.ProC.IsProCGroup C U
  sourceToPreimage : E →ₜ* presentationSubgroupPreimage π U
  sourceToOpen_surjective :
    Function.Surjective (schreierPresentationHom π U sourceToPreimage)
  kernel_eq_closedNormalClosure :
    (schreierPresentationHom π U sourceToPreimage).toMonoidHom.ker =
      closedNormalClosure R

/-- Open-subgroup Schreier presentation data with the rewriting map, surjectivity, and kernel
identity recorded explicitly. -/
structure OpenSubgroupSchreierRelatorPresentationData
    (π : F →ₜ* G) (U : OpenSubgroup G) (R : Set E) where
  sourceToPreimage : E →ₜ* presentationSubgroupPreimage π (U : Subgroup G)
  sourceToOpen_surjective :
    Function.Surjective (openSchreierPresentationHom π U sourceToPreimage)
  kernel_eq_closedNormalClosure :
    (openSchreierPresentationHom π U sourceToPreimage).toMonoidHom.ker =
      closedNormalClosure R

namespace SchreierRelatorPresentationData

variable {C}
variable {π : F →ₜ* G} {U : Subgroup G} {R S D : Set E}

omit [IsTopologicalGroup F] in
theorem isRelatorPresentationOf
    (D : SchreierRelatorPresentationData C π U R) :
    IsRelatorPresentationOf C (F := E) (G := U) R := by
  exact ⟨D.targetProC, schreierPresentationHom π U D.sourceToPreimage,
    D.sourceToOpen_surjective, D.kernel_eq_closedNormalClosure⟩

def clean
    (D : SchreierRelatorPresentationData C π U R)
    (T : RelatorTietzeData R S) :
    SchreierRelatorPresentationData C π U S where
  targetProC := D.targetProC
  sourceToPreimage := D.sourceToPreimage
  sourceToOpen_surjective := D.sourceToOpen_surjective
  kernel_eq_closedNormalClosure := by
    simpa [T.closedNormalClosure_eq] using D.kernel_eq_closedNormalClosure

def delete_redundant_relators
    (Ddata : SchreierRelatorPresentationData C π U (R ∪ D))
    (hD : D ⊆ closedNormalClosure R) :
    SchreierRelatorPresentationData C π U R where
  targetProC := Ddata.targetProC
  sourceToPreimage := Ddata.sourceToPreimage
  sourceToOpen_surjective := Ddata.sourceToOpen_surjective
  kernel_eq_closedNormalClosure := by
    simpa [closedNormalClosure_union_eq_left (F := E) hD] using
      Ddata.kernel_eq_closedNormalClosure

def add_redundant_relators
    (Ddata : SchreierRelatorPresentationData C π U R)
    (hD : D ⊆ closedNormalClosure R) :
    SchreierRelatorPresentationData C π U (R ∪ D) where
  targetProC := Ddata.targetProC
  sourceToPreimage := Ddata.sourceToPreimage
  sourceToOpen_surjective := Ddata.sourceToOpen_surjective
  kernel_eq_closedNormalClosure := by
    simpa [closedNormalClosure_union_eq_left (F := E) hD] using
      Ddata.kernel_eq_closedNormalClosure

def delete_trivial_relators
    (Ddata : SchreierRelatorPresentationData C π U (R ∪ D))
    (hD : D ⊆ ({1} : Set E)) :
    SchreierRelatorPresentationData C π U R :=
  Ddata.delete_redundant_relators
    (subset_closedNormalClosure_of_subset_singleton_one (F := E) hD)

def add_trivial_relators
    (Ddata : SchreierRelatorPresentationData C π U R)
    (hD : D ⊆ ({1} : Set E)) :
    SchreierRelatorPresentationData C π U (R ∪ D) :=
  Ddata.add_redundant_relators
    (subset_closedNormalClosure_of_subset_singleton_one (F := E) hD)

def delete_degenerate_schreier_relators
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : SchreierRelatorPresentationData C π U T.raw)
    (H : ProfiniteSchreierRelatorSets.DegenerateRelatorDeletionData T) :
    SchreierRelatorPresentationData C π U T.rewritten :=
  Ddata.clean H.relatorTietze_raw_rewritten

def clean_schreier_relators
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : SchreierRelatorPresentationData C π U T.raw)
    (H : ProfiniteSchreierRelatorSets.CleaningData T) :
    SchreierRelatorPresentationData C π U T.cleaned :=
  Ddata.clean H.relatorTietze_raw_cleaned

end SchreierRelatorPresentationData

namespace OpenSubgroupSchreierRelatorPresentationData

variable {C}
variable {π : F →ₜ* G} {U : OpenSubgroup G} {R S D : Set E}

def targetProC
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hG : ProCGroups.ProC.IsProCGroup C G) :
    ProCGroups.ProC.IsProCGroup C ↥(U : Subgroup G) := by
  have hUclosed : IsClosed (((U : Subgroup G) : Set G)) :=
    ProCGroups.openSubgroup_isClosed (G := G) U
  exact ProCGroups.ProC.IsProCGroup.of_isClosed_subgroup_of_fullFormation
    hC hG (U : Subgroup G) hUclosed

def toSchreierRelatorPresentationData
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U R)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hG : ProCGroups.ProC.IsProCGroup C G) :
    SchreierRelatorPresentationData C π (U : Subgroup G) R where
  targetProC := targetProC (C := C) (U := U) hC hG
  sourceToPreimage := Ddata.sourceToPreimage
  sourceToOpen_surjective := Ddata.sourceToOpen_surjective
  kernel_eq_closedNormalClosure := Ddata.kernel_eq_closedNormalClosure

omit [IsTopologicalGroup F] in
theorem isRelatorPresentationOf
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U R)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hG : ProCGroups.ProC.IsProCGroup C G) :
    IsRelatorPresentationOf C (F := E) (G := ↥(U : Subgroup G)) R :=
  (Ddata.toSchreierRelatorPresentationData hC hG).isRelatorPresentationOf

theorem isRelatorPresentationOf_of_ambientPresentation
    {R₀ : Set F}
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U R)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient : IsRelatorPresentationOf C (F := F) (G := G) R₀) :
    IsRelatorPresentationOf C (F := E) (G := ↥(U : Subgroup G)) R :=
  Ddata.isRelatorPresentationOf hC hambient.1

def clean
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U R)
    (T : RelatorTietzeData R S) :
    OpenSubgroupSchreierRelatorPresentationData π U S where
  sourceToPreimage := Ddata.sourceToPreimage
  sourceToOpen_surjective := Ddata.sourceToOpen_surjective
  kernel_eq_closedNormalClosure := by
    simpa [T.closedNormalClosure_eq] using Ddata.kernel_eq_closedNormalClosure

def delete_redundant_relators
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U (R ∪ D))
    (hD : D ⊆ closedNormalClosure R) :
    OpenSubgroupSchreierRelatorPresentationData π U R where
  sourceToPreimage := Ddata.sourceToPreimage
  sourceToOpen_surjective := Ddata.sourceToOpen_surjective
  kernel_eq_closedNormalClosure := by
    simpa [closedNormalClosure_union_eq_left (F := E) hD] using
      Ddata.kernel_eq_closedNormalClosure

def add_redundant_relators
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U R)
    (hD : D ⊆ closedNormalClosure R) :
    OpenSubgroupSchreierRelatorPresentationData π U (R ∪ D) where
  sourceToPreimage := Ddata.sourceToPreimage
  sourceToOpen_surjective := Ddata.sourceToOpen_surjective
  kernel_eq_closedNormalClosure := by
    simpa [closedNormalClosure_union_eq_left (F := E) hD] using
      Ddata.kernel_eq_closedNormalClosure

def delete_trivial_relators
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U (R ∪ D))
    (hD : D ⊆ ({1} : Set E)) :
    OpenSubgroupSchreierRelatorPresentationData π U R :=
  Ddata.delete_redundant_relators
    (subset_closedNormalClosure_of_subset_singleton_one (F := E) hD)

def add_trivial_relators
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U R)
    (hD : D ⊆ ({1} : Set E)) :
    OpenSubgroupSchreierRelatorPresentationData π U (R ∪ D) :=
  Ddata.add_redundant_relators
    (subset_closedNormalClosure_of_subset_singleton_one (F := E) hD)

def delete_degenerate_schreier_relators
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U T.raw)
    (H : ProfiniteSchreierRelatorSets.DegenerateRelatorDeletionData T) :
    OpenSubgroupSchreierRelatorPresentationData π U T.rewritten :=
  Ddata.clean H.relatorTietze_raw_rewritten

def clean_schreier_relators
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U T.raw)
    (H : ProfiniteSchreierRelatorSets.CleaningData T) :
    OpenSubgroupSchreierRelatorPresentationData π U T.cleaned :=
  Ddata.clean H.relatorTietze_raw_cleaned

theorem cleanedRelatorPresentationOf_of_ambientPresentation
    {R₀ : Set F} {T : ProfiniteSchreierRelatorSets E}
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U T.raw)
    (H : ProfiniteSchreierRelatorSets.CleaningData T)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient : IsRelatorPresentationOf C (F := F) (G := G) R₀) :
    IsRelatorPresentationOf C (F := E) (G := ↥(U : Subgroup G)) T.cleaned :=
  (Ddata.clean_schreier_relators H).isRelatorPresentationOf hC hambient.1

end OpenSubgroupSchreierRelatorPresentationData

section StandardPresentationData

variable {Eₛ : Type u} [Group Eₛ] [TopologicalSpace Eₛ] [IsTopologicalGroup Eₛ]

/-- A standard-form Schreier presentation package when the final Tietze step may change the
presentation source, as in deletion of redundant Schreier generators. -/
structure SchreierStandardPresentationData
    (π : F →ₜ* G) (U : Subgroup G)
    (rawRelators : Set E) (standardRelators : Set Eₛ) where
  rawData : SchreierRelatorPresentationData C π U rawRelators
  standardTietze : RelatorMapTietzeData rawRelators standardRelators

namespace SchreierStandardPresentationData

variable {C}
variable {π : F →ₜ* G} {U : Subgroup G}
variable {rawRelators : Set E} {standardRelators : Set Eₛ}

omit [IsTopologicalGroup F] in
theorem isRelatorPresentationOf
    (D : SchreierStandardPresentationData C π U rawRelators standardRelators) :
    IsRelatorPresentationOf C (F := Eₛ) (G := U) standardRelators :=
  D.standardTietze.presentation (C := C) (G := U) D.rawData.isRelatorPresentationOf

def ofCleaningData
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : SchreierRelatorPresentationData C π U T.raw)
    (H : ProfiniteSchreierRelatorSets.CleaningData T) :
    SchreierStandardPresentationData C π U T.raw T.cleaned where
  rawData := Ddata
  standardTietze :=
    RelatorMapTietzeData.ofRelatorTietzeData H.relatorTietze_raw_cleaned

end SchreierStandardPresentationData

/-- Standard-form data for an open subgroup, consisting of a raw Schreier presentation datum and
a Tietze datum from the raw source to the final standard source. -/
structure OpenSubgroupSchreierStandardPresentationData
    (π : F →ₜ* G) (U : OpenSubgroup G)
    (rawRelators : Set E) (standardRelators : Set Eₛ) where
  rawData : OpenSubgroupSchreierRelatorPresentationData π U rawRelators
  standardTietze : RelatorMapTietzeData rawRelators standardRelators

namespace OpenSubgroupSchreierStandardPresentationData

variable {C}
variable {π : F →ₜ* G} {U : OpenSubgroup G}
variable {rawRelators : Set E} {standardRelators : Set Eₛ}

omit [IsTopologicalGroup F] in
theorem isRelatorPresentationOf
    (D : OpenSubgroupSchreierStandardPresentationData π U rawRelators standardRelators)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hG : ProCGroups.ProC.IsProCGroup C G) :
    IsRelatorPresentationOf C (F := Eₛ) (G := ↥(U : Subgroup G)) standardRelators :=
  D.standardTietze.presentation (C := C) (G := ↥(U : Subgroup G))
    (D.rawData.isRelatorPresentationOf hC hG)

theorem isRelatorPresentationOf_of_ambientPresentation
    {R₀ : Set F}
    (D : OpenSubgroupSchreierStandardPresentationData π U rawRelators standardRelators)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient : IsRelatorPresentationOf C (F := F) (G := G) R₀) :
    IsRelatorPresentationOf C (F := Eₛ) (G := ↥(U : Subgroup G)) standardRelators :=
  D.isRelatorPresentationOf hC hambient.1

theorem isRelatorPresentationOf_of_ambientFreeRelatorPresentation
    {X : Type u} [TopologicalSpace X] {ι : X → F} {R₀ : Set F}
    (D : OpenSubgroupSchreierStandardPresentationData π U rawRelators standardRelators)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient : IsFreeRelatorPresentationOfClass C (F := F) (G := G) ι R₀) :
    IsRelatorPresentationOf C (F := Eₛ) (G := ↥(U : Subgroup G)) standardRelators :=
  D.isRelatorPresentationOf hC
    (IsFreeRelatorPresentationOfClass.isRelatorPresentationOf (C := C) (G := G) hambient).1

def ofCleaningData
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U T.raw)
    (H : ProfiniteSchreierRelatorSets.CleaningData T) :
    OpenSubgroupSchreierStandardPresentationData π U T.raw T.cleaned where
  rawData := Ddata
  standardTietze :=
    RelatorMapTietzeData.ofRelatorTietzeData H.relatorTietze_raw_cleaned

omit [IsTopologicalGroup F] in
theorem isRelatorPresentationOf_ofCleaningData
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U T.raw)
    (H : ProfiniteSchreierRelatorSets.CleaningData T)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hG : ProCGroups.ProC.IsProCGroup C G) :
    IsRelatorPresentationOf C (F := E) (G := ↥(U : Subgroup G)) T.cleaned :=
  (ofCleaningData Ddata H).isRelatorPresentationOf hC hG

theorem isRelatorPresentationOf_ofCleaningData_of_ambientFreeRelatorPresentation
    {X : Type u} [TopologicalSpace X] {ι : X → F} {R₀ : Set F}
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : OpenSubgroupSchreierRelatorPresentationData π U T.raw)
    (H : ProfiniteSchreierRelatorSets.CleaningData T)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient : IsFreeRelatorPresentationOfClass C (F := F) (G := G) ι R₀) :
    IsRelatorPresentationOf C (F := E) (G := ↥(U : Subgroup G)) T.cleaned :=
  (ofCleaningData Ddata H).isRelatorPresentationOf_of_ambientFreeRelatorPresentation
    hC hambient

end OpenSubgroupSchreierStandardPresentationData

section FreeSourcePresentationData

variable {Y Yₛ : Type u} [TopologicalSpace Y] [TopologicalSpace Yₛ]
variable {η : Y → E} {ηₛ : Yₛ → Eₛ}

/-- A Schreier relator-presentation datum whose source is explicitly the free pro-`C` group on
the chosen Schreier generators.  This is the direct formal shape of
`U = ⟨Schreier generators | rewritten relators⟩_{pro-C}`. -/
structure SchreierFreeRelatorPresentationData
    (η : Y → E) (π : F →ₜ* G) (U : Subgroup G) (R : Set E) where
  freeSource :
    ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) η
  relatorData : SchreierRelatorPresentationData C π U R

namespace SchreierFreeRelatorPresentationData

variable {C}
variable {π : F →ₜ* G} {U : Subgroup G} {R S D : Set E}

omit [IsTopologicalGroup F] in
theorem isFreeRelatorPresentationOfClass
    (Ddata : SchreierFreeRelatorPresentationData C η π U R) :
    IsFreeRelatorPresentationOfClass C (F := E) (G := U) η R := by
  exact ⟨Ddata.freeSource, by simpa using Ddata.relatorData.targetProC,
    schreierPresentationHom π U Ddata.relatorData.sourceToPreimage,
    Ddata.relatorData.sourceToOpen_surjective,
    Ddata.relatorData.kernel_eq_closedNormalClosure⟩

omit [IsTopologicalGroup F] in
theorem isRelatorPresentationOf
    (Ddata : SchreierFreeRelatorPresentationData C η π U R) :
    IsRelatorPresentationOf C (F := E) (G := U) R :=
  Ddata.isFreeRelatorPresentationOfClass.isRelatorPresentationOf

def clean
    (Ddata : SchreierFreeRelatorPresentationData C η π U R)
    (T : RelatorTietzeData R S) :
    SchreierFreeRelatorPresentationData C η π U S where
  freeSource := Ddata.freeSource
  relatorData := Ddata.relatorData.clean T

def delete_redundant_relators
    (Ddata : SchreierFreeRelatorPresentationData C η π U (R ∪ D))
    (hD : D ⊆ closedNormalClosure R) :
    SchreierFreeRelatorPresentationData C η π U R where
  freeSource := Ddata.freeSource
  relatorData := Ddata.relatorData.delete_redundant_relators hD

def delete_trivial_relators
    (Ddata : SchreierFreeRelatorPresentationData C η π U (R ∪ D))
    (hD : D ⊆ ({1} : Set E)) :
    SchreierFreeRelatorPresentationData C η π U R where
  freeSource := Ddata.freeSource
  relatorData := Ddata.relatorData.delete_trivial_relators hD

def delete_degenerate_schreier_relators
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : SchreierFreeRelatorPresentationData C η π U T.raw)
    (H : ProfiniteSchreierRelatorSets.DegenerateRelatorDeletionData T) :
    SchreierFreeRelatorPresentationData C η π U T.rewritten :=
  Ddata.clean H.relatorTietze_raw_rewritten

def clean_schreier_relators
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : SchreierFreeRelatorPresentationData C η π U T.raw)
    (H : ProfiniteSchreierRelatorSets.CleaningData T) :
    SchreierFreeRelatorPresentationData C η π U T.cleaned :=
  Ddata.clean H.relatorTietze_raw_cleaned

end SchreierFreeRelatorPresentationData

/-- The open-subgroup version of `SchreierFreeRelatorPresentationData`.  The open subgroup is
shown to be pro-`C` from the ambient presentation and full-formation hypothesis. -/
structure OpenSubgroupSchreierFreeRelatorPresentationData
    (η : Y → E) (π : F →ₜ* G) (U : OpenSubgroup G) (R : Set E) where
  freeSource :
    ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) η
  relatorData : OpenSubgroupSchreierRelatorPresentationData π U R

namespace OpenSubgroupSchreierFreeRelatorPresentationData

variable {C}
variable {π : F →ₜ* G} {U : OpenSubgroup G} {R S D : Set E}

omit [IsTopologicalGroup F] in
theorem isFreeRelatorPresentationOfClass
    (Ddata : OpenSubgroupSchreierFreeRelatorPresentationData C η π U R)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hG : ProCGroups.ProC.IsProCGroup C G) :
    IsFreeRelatorPresentationOfClass C (F := E) (G := ↥(U : Subgroup G)) η R := by
  have hU : ProCGroups.ProC.IsProCGroup C ↥(U : Subgroup G) :=
    OpenSubgroupSchreierRelatorPresentationData.targetProC (C := C) (U := U) hC hG
  exact ⟨Ddata.freeSource, by simpa using hU,
    openSchreierPresentationHom π U Ddata.relatorData.sourceToPreimage,
    Ddata.relatorData.sourceToOpen_surjective,
    Ddata.relatorData.kernel_eq_closedNormalClosure⟩

theorem isFreeRelatorPresentationOfClass_of_ambientPresentation
    {R₀ : Set F}
    (Ddata : OpenSubgroupSchreierFreeRelatorPresentationData C η π U R)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient : IsRelatorPresentationOf C (F := F) (G := G) R₀) :
    IsFreeRelatorPresentationOfClass C (F := E) (G := ↥(U : Subgroup G)) η R :=
  Ddata.isFreeRelatorPresentationOfClass hC hambient.1

theorem isFreeRelatorPresentationOfClass_of_ambientFreeRelatorPresentation
    {X : Type u} [TopologicalSpace X] {ι : X → F} {R₀ : Set F}
    (Ddata : OpenSubgroupSchreierFreeRelatorPresentationData C η π U R)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient : IsFreeRelatorPresentationOfClass C (F := F) (G := G) ι R₀) :
    IsFreeRelatorPresentationOfClass C (F := E) (G := ↥(U : Subgroup G)) η R :=
  Ddata.isFreeRelatorPresentationOfClass hC
    (IsFreeRelatorPresentationOfClass.isRelatorPresentationOf
      (C := C) (G := G) hambient).1

def clean
    (Ddata : OpenSubgroupSchreierFreeRelatorPresentationData C η π U R)
    (T : RelatorTietzeData R S) :
    OpenSubgroupSchreierFreeRelatorPresentationData C η π U S where
  freeSource := Ddata.freeSource
  relatorData := Ddata.relatorData.clean T

def delete_redundant_relators
    (Ddata : OpenSubgroupSchreierFreeRelatorPresentationData C η π U (R ∪ D))
    (hD : D ⊆ closedNormalClosure R) :
    OpenSubgroupSchreierFreeRelatorPresentationData C η π U R where
  freeSource := Ddata.freeSource
  relatorData := Ddata.relatorData.delete_redundant_relators hD

def delete_trivial_relators
    (Ddata : OpenSubgroupSchreierFreeRelatorPresentationData C η π U (R ∪ D))
    (hD : D ⊆ ({1} : Set E)) :
    OpenSubgroupSchreierFreeRelatorPresentationData C η π U R where
  freeSource := Ddata.freeSource
  relatorData := Ddata.relatorData.delete_trivial_relators hD

def delete_degenerate_schreier_relators
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : OpenSubgroupSchreierFreeRelatorPresentationData C η π U T.raw)
    (H : ProfiniteSchreierRelatorSets.DegenerateRelatorDeletionData T) :
    OpenSubgroupSchreierFreeRelatorPresentationData C η π U T.rewritten :=
  Ddata.clean H.relatorTietze_raw_rewritten

def clean_schreier_relators
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : OpenSubgroupSchreierFreeRelatorPresentationData C η π U T.raw)
    (H : ProfiniteSchreierRelatorSets.CleaningData T) :
    OpenSubgroupSchreierFreeRelatorPresentationData C η π U T.cleaned :=
  Ddata.clean H.relatorTietze_raw_cleaned

theorem cleanedFreeRelatorPresentationOf_of_ambientFreeRelatorPresentation
    {X : Type u} [TopologicalSpace X] {ι : X → F} {R₀ : Set F}
    {T : ProfiniteSchreierRelatorSets E}
    (Ddata : OpenSubgroupSchreierFreeRelatorPresentationData C η π U T.raw)
    (H : ProfiniteSchreierRelatorSets.CleaningData T)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient : IsFreeRelatorPresentationOfClass C (F := F) (G := G) ι R₀) :
    IsFreeRelatorPresentationOfClass C (F := E) (G := ↥(U : Subgroup G)) η T.cleaned :=
  (Ddata.clean_schreier_relators H)
    |>.isFreeRelatorPresentationOfClass_of_ambientFreeRelatorPresentation hC hambient

end OpenSubgroupSchreierFreeRelatorPresentationData

/-- Standard-form free Schreier presentation data.  The final source is explicitly free on the
surviving Schreier generators after generator deletion. -/
structure OpenSubgroupSchreierStandardFreeRelatorPresentationData
    (ηₛ : Yₛ → Eₛ) (π : F →ₜ* G) (U : OpenSubgroup G)
    (rawRelators : Set E) (standardRelators : Set Eₛ) where
  freeStandardSource :
    ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) ηₛ
  standardData :
    OpenSubgroupSchreierStandardPresentationData π U rawRelators standardRelators

namespace OpenSubgroupSchreierStandardFreeRelatorPresentationData

variable {C}
variable {π : F →ₜ* G} {U : OpenSubgroup G}
variable {rawRelators : Set E} {standardRelators : Set Eₛ}

omit [IsTopologicalGroup F] in
theorem isFreeRelatorPresentationOfClass
    (D : OpenSubgroupSchreierStandardFreeRelatorPresentationData
      C ηₛ π U rawRelators standardRelators)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hG : ProCGroups.ProC.IsProCGroup C G) :
    IsFreeRelatorPresentationOfClass C
      (F := Eₛ) (G := ↥(U : Subgroup G)) ηₛ standardRelators := by
  rcases D.standardData.isRelatorPresentationOf hC hG with
    ⟨hU, ρ, hρsurj, hρker⟩
  exact ⟨D.freeStandardSource, by simpa using hU, ρ, hρsurj, hρker⟩

theorem isFreeRelatorPresentationOfClass_of_ambientFreeRelatorPresentation
    {X : Type u} [TopologicalSpace X] {ι : X → F} {R₀ : Set F}
    (D : OpenSubgroupSchreierStandardFreeRelatorPresentationData
      C ηₛ π U rawRelators standardRelators)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient : IsFreeRelatorPresentationOfClass C (F := F) (G := G) ι R₀) :
    IsFreeRelatorPresentationOfClass C
      (F := Eₛ) (G := ↥(U : Subgroup G)) ηₛ standardRelators :=
  D.isFreeRelatorPresentationOfClass hC
    (IsFreeRelatorPresentationOfClass.isRelatorPresentationOf
      (C := C) (G := G) hambient).1

end OpenSubgroupSchreierStandardFreeRelatorPresentationData

section RewritingFreeSourcePresentationData

variable {Q : Type v}
variable {Srw : ProfiniteSchreierRewritingRelatorSets Q F E}

/-- Open-subgroup free Schreier presentation data whose rewritten relators are definitionally
constructed from a map `tau`. -/
structure OpenSubgroupSchreierFreeRewritingPresentationData
    (η : Y → E) (π : F →ₜ* G) (U : OpenSubgroup G)
    (Srw : ProfiniteSchreierRewritingRelatorSets Q F E) where
  freeSource :
    ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) η
  relatorData :
    OpenSubgroupSchreierRelatorPresentationData π U Srw.toRelatorSets.raw

namespace OpenSubgroupSchreierFreeRewritingPresentationData

variable {C}
variable {π : F →ₜ* G} {U : OpenSubgroup G}

def toRawFreeRelatorPresentationData
    (Ddata : OpenSubgroupSchreierFreeRewritingPresentationData C η π U Srw) :
    OpenSubgroupSchreierFreeRelatorPresentationData C η π U Srw.toRelatorSets.raw where
  freeSource := Ddata.freeSource
  relatorData := Ddata.relatorData

theorem rawFreeRelatorPresentationOf_of_ambientFreeRelatorPresentation
    {X : Type u} [TopologicalSpace X] {ι : X → F}
    (Ddata : OpenSubgroupSchreierFreeRewritingPresentationData C η π U Srw)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient :
      IsFreeRelatorPresentationOfClass C (F := F) (G := G) ι Srw.originalRelators) :
    IsFreeRelatorPresentationOfClass C
      (F := E) (G := ↥(U : Subgroup G)) η Srw.toRelatorSets.raw :=
  Ddata.toRawFreeRelatorPresentationData
    |>.isFreeRelatorPresentationOfClass_of_ambientFreeRelatorPresentation hC hambient

theorem rewrittenFreeRelatorPresentationOf_of_ambientFreeRelatorPresentation
    {X : Type u} [TopologicalSpace X] {ι : X → F}
    (Ddata : OpenSubgroupSchreierFreeRewritingPresentationData C η π U Srw)
    (H : ProfiniteSchreierRewritingRelatorSets.DegenerateRelatorDeletionData Srw)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient :
      IsFreeRelatorPresentationOfClass C (F := F) (G := G) ι Srw.originalRelators) :
    IsFreeRelatorPresentationOfClass C
      (F := E) (G := ↥(U : Subgroup G)) η Srw.toRelatorSets.rewritten :=
  (Ddata.toRawFreeRelatorPresentationData.delete_degenerate_schreier_relators H)
    |>.isFreeRelatorPresentationOfClass_of_ambientFreeRelatorPresentation hC hambient

theorem cleanedFreeRelatorPresentationOf_of_ambientFreeRelatorPresentation
    {X : Type u} [TopologicalSpace X] {ι : X → F}
    (Ddata : OpenSubgroupSchreierFreeRewritingPresentationData C η π U Srw)
    (H : ProfiniteSchreierRewritingRelatorSets.CleaningData Srw)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient :
      IsFreeRelatorPresentationOfClass C (F := F) (G := G) ι Srw.originalRelators) :
    IsFreeRelatorPresentationOfClass C
      (F := E) (G := ↥(U : Subgroup G)) η Srw.toRelatorSets.cleaned :=
  (Ddata.toRawFreeRelatorPresentationData.clean_schreier_relators H)
    |>.isFreeRelatorPresentationOfClass_of_ambientFreeRelatorPresentation hC hambient

end OpenSubgroupSchreierFreeRewritingPresentationData

/-- Standard-form free Schreier presentation data whose raw relators are built from `tau`.  The
standard source may differ from the raw source after deleting redundant Schreier generators. -/
structure OpenSubgroupSchreierStandardFreeRewritingPresentationData
    (ηₛ : Yₛ → Eₛ) (π : F →ₜ* G) (U : OpenSubgroup G)
    (Srw : ProfiniteSchreierRewritingRelatorSets Q F E)
    (standardRelators : Set Eₛ) where
  freeStandardSource :
    ProCGroups.FreeProC.IsFreeProCGroup
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) ηₛ
  standardData :
    OpenSubgroupSchreierStandardPresentationData π U Srw.toRelatorSets.raw standardRelators

namespace OpenSubgroupSchreierStandardFreeRewritingPresentationData

variable {C}
variable {π : F →ₜ* G} {U : OpenSubgroup G}
variable {standardRelators : Set Eₛ}

def toStandardFreeRelatorPresentationData
    (D : OpenSubgroupSchreierStandardFreeRewritingPresentationData
      C ηₛ π U Srw standardRelators) :
    OpenSubgroupSchreierStandardFreeRelatorPresentationData
      C ηₛ π U Srw.toRelatorSets.raw standardRelators where
  freeStandardSource := D.freeStandardSource
  standardData := D.standardData

theorem isFreeRelatorPresentationOfClass_of_ambientFreeRelatorPresentation
    {X : Type u} [TopologicalSpace X] {ι : X → F}
    (D : OpenSubgroupSchreierStandardFreeRewritingPresentationData
      C ηₛ π U Srw standardRelators)
    (hC : ProCGroups.FiniteGroupClass.FullFormation C)
    (hambient :
      IsFreeRelatorPresentationOfClass C (F := F) (G := G) ι Srw.originalRelators) :
    IsFreeRelatorPresentationOfClass C
      (F := Eₛ) (G := ↥(U : Subgroup G)) ηₛ standardRelators :=
  D.toStandardFreeRelatorPresentationData
    |>.isFreeRelatorPresentationOfClass_of_ambientFreeRelatorPresentation hC hambient

end OpenSubgroupSchreierStandardFreeRewritingPresentationData

end RewritingFreeSourcePresentationData

end FreeSourcePresentationData

end StandardPresentationData

end SchreierRelatorPresentationData

end ProCGroups.Presentations
