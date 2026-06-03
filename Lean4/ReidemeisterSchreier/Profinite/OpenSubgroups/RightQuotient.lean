import ProCGroups.ProC.Subgroups.Products
import ReidemeisterSchreier.RightQuotient

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Profinite/OpenSubgroups/RightQuotient.lean
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

universe u

section RightQuotientSections

variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

/-- The right-coset space `H \ F`, encoded via right quotients. -/
abbrev OpenSubgroupRightQuotient (H : OpenSubgroup F) :=
  _root_.ReidemeisterSchreier.RightQuotient (H : Subgroup F)

/-- The right coset of an element modulo an open subgroup. -/
def openSubgroupRightCoset (H : OpenSubgroup F) (g : F) : OpenSubgroupRightQuotient H :=
  _root_.ReidemeisterSchreier.rightCoset (H : Subgroup F) g

omit [IsTopologicalGroup F] in
/-- A right coset is the base coset exactly when its representative lies in the subgroup. -/
theorem openSubgroupRightCoset_eq_basepoint_iff_mem
    {H : OpenSubgroup F} {g : F} :
    openSubgroupRightCoset H g = openSubgroupRightCoset H (1 : F) ↔
      g ∈ (H : Subgroup F) := by
  exact _root_.ReidemeisterSchreier.rightCoset_eq_basepoint_iff_mem (H := (H : Subgroup F))

omit [IsTopologicalGroup F] in
@[simp] theorem openSubgroupRightCoset_smul
    (H : OpenSubgroup F) (g a : F) :
    letI : MulAction F (OpenSubgroupRightQuotient H) :=
      _root_.ReidemeisterSchreier.rightCosetMulAction (H : Subgroup F)
    g • openSubgroupRightCoset H a = openSubgroupRightCoset H (a * g⁻¹) :=
  _root_.ReidemeisterSchreier.rightCosetMulAction_mk_smul (H := (H : Subgroup F)) g a

omit [IsTopologicalGroup F] in
@[simp] theorem openSubgroupRightCoset_inv_smul
    (H : OpenSubgroup F) (g a : F) :
    letI : MulAction F (OpenSubgroupRightQuotient H) :=
      _root_.ReidemeisterSchreier.rightCosetMulAction (H : Subgroup F)
    g⁻¹ • openSubgroupRightCoset H a = openSubgroupRightCoset H (a * g) :=
  _root_.ReidemeisterSchreier.rightCosetMulAction_inv_mk_smul (H := (H : Subgroup F)) g a

/-- Right cosets of an open subgroup are finite because they are equivalent to the left quotient. -/
instance finite_openSubgroupRightQuotient (H : OpenSubgroup F) [CompactSpace F] :
    Finite (OpenSubgroupRightQuotient H) := by
  let e :=
    QuotientGroup.quotientRightRelEquivQuotientLeftRel (H : Subgroup F)
  exact Finite.of_equiv (F ⧸ (H : Subgroup F)) e.symm

/-- Right cosets of an open subgroup inherit a `Fintype` from compactness. -/
noncomputable instance fintype_openSubgroupRightQuotient (H : OpenSubgroup F) [CompactSpace F] :
    Fintype (OpenSubgroupRightQuotient H) :=
  Fintype.ofFinite (OpenSubgroupRightQuotient H)

/-- The quotient topology on right cosets of an open subgroup is discrete. -/
instance discreteTopology_openSubgroupRightQuotient (H : OpenSubgroup F) :
    DiscreteTopology (OpenSubgroupRightQuotient H) := by
  classical
  refine discreteTopology_iff_isOpen_singleton.2 ?_
  intro q
  rw [← isQuotientMap_quotient_mk'.isOpen_preimage]
  let qmk : F → OpenSubgroupRightQuotient H :=
    @Quotient.mk' F (QuotientGroup.rightRel (H : Subgroup F))
  let a : F := q.out
  have hpre :
      qmk ⁻¹' ({q} : Set (OpenSubgroupRightQuotient H)) =
        (fun x : F => a * x⁻¹) ⁻¹' ((H : Subgroup F) : Set F) := by
    ext x
    constructor
    · intro hx
      have hEq : (Quotient.mk'' x : OpenSubgroupRightQuotient H) = Quotient.mk'' a := by
        calc
          (Quotient.mk'' x : OpenSubgroupRightQuotient H) = q := hx
          _ = Quotient.mk'' a := (Quotient.out_eq' q).symm
      have hrel : QuotientGroup.rightRel (H : Subgroup F) x a := Quotient.eq''.mp hEq
      simpa [a] using (QuotientGroup.rightRel_apply.mp hrel)
    · intro hx
      have hrel : QuotientGroup.rightRel (H : Subgroup F) x a := by
        rw [QuotientGroup.rightRel_apply]
        simpa [a] using hx
      change (Quotient.mk'' x : OpenSubgroupRightQuotient H) = q
      calc
        (Quotient.mk'' x : OpenSubgroupRightQuotient H) = Quotient.mk'' a :=
          Quotient.eq''.mpr hrel
        _ = q := by simp only [Quotient.out_eq, a]
  have hpreOpen : IsOpen (qmk ⁻¹' ({q} : Set (OpenSubgroupRightQuotient H))) := by
    rw [hpre]
    exact H.isOpen'.preimage (continuous_const.mul continuous_inv)
  simpa [qmk] using hpreOpen

/-- A normalized section of the right-coset projection, sending the trivial coset to `1`. -/
noncomputable def openSubgroupRightCosetSection
    (H : OpenSubgroup F) : OpenSubgroupRightQuotient H → F := by
  classical
  intro q
  exact
    if hq : q = openSubgroupRightCoset H (1 : F) then
      1
    else
      q.out

omit [IsTopologicalGroup F] in
@[simp] theorem openSubgroupRightCosetSection_spec
    (H : OpenSubgroup F) (q : OpenSubgroupRightQuotient H) :
    Quotient.mk'' (openSubgroupRightCosetSection (F := F) H q) = q := by
  classical
  by_cases hq : q = openSubgroupRightCoset H (1 : F)
  · subst hq
    simp only [openSubgroupRightCosetSection, openSubgroupRightCoset, rightCoset, ↓reduceDIte]
  · simp only [openSubgroupRightCosetSection, hq, ↓reduceDIte, Quotient.out_eq]

omit [IsTopologicalGroup F] in
@[simp] theorem openSubgroupRightCosetSection_one
    (H : OpenSubgroup F) :
    openSubgroupRightCosetSection (F := F) H (openSubgroupRightCoset H (1 : F)) = 1 := by
  classical
  simp only [openSubgroupRightCosetSection, ↓reduceDIte]

/-- The normalized right-coset section is continuous because the right quotient is discrete. -/
theorem continuous_openSubgroupRightCosetSection
    (H : OpenSubgroup F) :
    Continuous (openSubgroupRightCosetSection (F := F) H) :=
  continuous_of_discreteTopology

end RightQuotientSections

end Profinite
end ReidemeisterSchreier
