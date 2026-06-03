import ReidemeisterSchreier.Profinite.OpenSubgroups.BasisTheorems
import ReidemeisterSchreier.Profinite.OpenSubgroups.RankBound

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Profinite/OpenSubgroups/BasisFiniteRank.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite open-subgroup Schreier theory

Profinite open subgroup quotients, finite permutation targets, dense free models, exact right Schreier generation, and topological rank bounds.
-/

open scoped Topology Pointwise

namespace ReidemeisterSchreier
namespace Profinite

open ProCGroups
open ProCGroups.FreeProC
open ProCGroups.ProC

universe u

/-- Hypotheses used by the finite-rank Schreier basis theorem.  The bundle keeps the theorem
statement from hiding the variety/isomorphism/extension/cyclic assumptions behind short names. -/
structure SchreierBasisFiniteRankHypotheses
    (C : ProCGroups.FiniteGroupClass.{u}) : Prop where
  variety : ProCGroups.FiniteGroupClass.Variety C
  isomClosed : ProCGroups.FiniteGroupClass.IsomClosed C
  extensionClosed : ProCGroups.FiniteGroupClass.ExtensionClosed C
  hasNontrivialCyclic :
    ∃ (A : Type u) (_ : Group A) (_ : Finite A),
      C A ∧ IsCyclic A ∧ Nontrivial A


/-- Finite converging-set basis data for an open subgroup of a free pro-`C` group on a finite
converging set.  The carrier is the open subgroup itself. -/
theorem exists_finiteIndexBasisCarrierAndMap_openSubgroup
    (C : ProCGroups.FiniteGroupClass.{u})
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ (B : Type u), Finite B ∧
      ∃ μ : B → ↥(H : Subgroup F),
        IsFreeProCGroupOnConvergingSet
          (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C)
          B ↥(H : Subgroup F) μ := by
  classical
  letI : CompactSpace F := IsProCGroup.compactSpace hF.isProC
  letI : T2Space F := IsProCGroup.t2Space hF.isProC
  letI : TopologicalSpace X := ⊥
  letI : DiscreteTopology X := ⟨rfl⟩
  letI : Fintype X := Fintype.ofFinite X
  rcases
      exists_compactPointedBasis_openSubgroup_of_freeProCOnConvergingSet
        C hForm hSub hIso hQuot hExt hF H with
    ⟨κ, _hκcont, _hκallBase, _hκbase, _hκcompact, _hκclosed, hκfree⟩
  letI : Finite (OpenSubgroupRightQuotient H) :=
    finite_openSubgroupRightQuotient (F := F) H
  have hRangeFin : (Set.range ι).Finite := Set.finite_range ι
  letI : Finite (Set.range ι) := hRangeFin.to_subtype
  letI : Fintype (Set.range ι) := Fintype.ofFinite (Set.range ι)
  letI : Finite (OnePoint X) := Finite.of_fintype (OnePoint X)
  letI : Finite (Set.range κ) := (Set.finite_range κ).to_subtype
  let x0 : Set.range κ :=
    ⟨κ (openSubgroupRightCoset H (1 : F), OnePoint.infty),
      ⟨(openSubgroupRightCoset H (1 : F), OnePoint.infty), rfl⟩⟩
  letI : DiscreteTopology (Set.range κ) :=
    DiscreteTopology.of_finite_of_isClosed_singleton fun _ => isClosed_singleton
  let B : Type u := {y : Set.range κ // y ≠ x0}
  let μ : B → ↥(H : Subgroup F) := fun y => y.1.1
  have hμfree :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) B ↥(H : Subgroup F) μ := by
    simpa [B, μ, x0] using
      freeOnFinitePointedDiscreteSpace_has_convergingSetBasis
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) hκfree
  exact ⟨B, inferInstance, μ, hμfree⟩

/-- Finite converging-set basis model for an open subgroup of a finite-rank free pro-`C` group on
a converging set. -/
theorem exists_finiteFreeProCSourceData_openSubgroup
    (C : ProCGroups.FiniteGroupClass.{u})
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧ Finite Fdata.basis := by
  rcases exists_finiteIndexBasisCarrierAndMap_openSubgroup
      C hForm hSub hIso hQuot hExt hF H with
    ⟨B, hBfin, μ, hμfree⟩
  letI : Finite B := hBfin
  let Fdata : FreeProCGroupOnConvergingSetData
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) :=
    { basis := B
      carrier := ↥(H : Subgroup F)
      instGroup := inferInstance
      instTopologicalSpace := inferInstance
      instIsTopologicalGroup := inferInstance
      inclusion := μ
      isFree := hμfree }
  exact ⟨Fdata, ⟨ContinuousMulEquiv.refl _⟩, inferInstance⟩

/-- An exact-size finite generating family for the open subgroup, indexed by the Schreier
rank-transform cardinal.  This is a generating family, not a basis: the padding step may repeat
the distinguished padding element `1`. -/
theorem exists_exactGeneratingFamily_openSubgroup_of_finiteBasis
    (C : ProCGroups.FiniteGroupClass.{u})
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ κ :
        ULift (Fin (_root_.ReidemeisterSchreier.Schreier.rankTransform
          (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))))) →
          ↥(H : Subgroup F),
      Generation.GeneratesAndConvergesToOne
        (G := ↥(H : Subgroup F)) (Set.range κ) := by
  classical
  let n : ℕ := _root_.ReidemeisterSchreier.Schreier.rankTransform
    (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F)))
  rcases exists_finiteIndexBasisCarrierAndMap_openSubgroup
      C hForm hSub hIso hQuot hExt hF H with
    ⟨B, hBfin, μ, hμfree⟩
  letI : Finite B := hBfin
  letI : Fintype B := Fintype.ofFinite B
  let Fdata : FreeProCGroupOnConvergingSetData
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) :=
    { basis := B
      carrier := ↥(H : Subgroup F)
      instGroup := inferInstance
      instTopologicalSpace := inferInstance
      instIsTopologicalGroup := inferInstance
      inclusion := μ
      isFree := hμfree }
  letI : Fintype X := Fintype.ofFinite X
  let Fambient : FreeProCGroupOnConvergingSetData
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) :=
    { basis := X
      carrier := F
      instGroup := inferInstance
      instTopologicalSpace := inferInstance
      instIsTopologicalGroup := inferInstance
      inclusion := ι
      isFree := hF }
  have hAmbientRank :
      Cardinal.mk X = Generation.topologicalRank F :=
    basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fambient
  have hdF : Generation.topologicalRank F = Nat.card X := by
    calc
      Generation.topologicalRank F = Cardinal.mk X := hAmbientRank.symm
      _ = (Nat.card X : Cardinal) := by simp only [Cardinal.mk_fintype, Nat.card_eq_fintype_card]
  have hdHle :
      Generation.topologicalRank ↥(H : Subgroup F) ≤ (n : Cardinal) := by
    simpa [n] using
      topologicalRank_openSubgroup_le_rankTransform_of_topologicalRank_eq_nat
        (G := F) hF.isProC.1 hdF H
  have hBasisRank :
      Cardinal.mk B = Generation.topologicalRank ↥(H : Subgroup F) := by
    simpa [Fdata] using
      basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fdata
  have hBcardLe : Cardinal.mk B ≤ (n : Cardinal) := hBasisRank.trans_le hdHle
  have hBcardNat : Fintype.card B ≤ Fintype.card (ULift (Fin n)) := by
    have hleNat : Fintype.card B ≤ n := by
      simpa [Nat.card_eq_fintype_card] using
        Cardinal.toNat_le_toNat hBcardLe (Cardinal.natCast_lt_aleph0 (n := n))
    simpa using hleNat
  have hEmb : Nonempty (B ↪ ULift (Fin n)) :=
    Function.Embedding.nonempty_of_card_le hBcardNat
  let e : B ↪ ULift (Fin n) := Classical.choice hEmb
  let κ : ULift (Fin n) → ↥(H : Subgroup F) :=
    Function.extend e μ (fun _ => 1)
  have hext : κ ∘ e = μ := by
    simpa [κ] using
      (Function.extend_comp e.injective μ (fun _ => (1 : ↥(H : Subgroup F))))
  have hrange :
      Set.range μ ⊆ Set.range κ := by
    rintro z ⟨b, rfl⟩
    refine ⟨e b, ?_⟩
    exact congrArg (fun f => f b) hext
  have hκgen :
      Generation.TopologicallyGenerates (G := ↥(H : Subgroup F)) (Set.range κ) :=
    Generation.topologicallyGenerates_mono (G := ↥(H : Subgroup F)) hμfree.generates_range hrange
  have hκconv : Generation.ConvergesToOne (G := ↥(H : Subgroup F)) (Set.range κ) :=
    Generation.ConvergesToOne.of_finite (G := ↥(H : Subgroup F)) (Set.finite_range κ)
  exact ⟨κ, ⟨hκgen, hκconv⟩⟩

/-- Finite-rank extension-closed variety case with the exact Schreier rank-transform cardinality. -/
theorem exists_basis_openSubgroup_of_extensionClosed_finiteRank
    (C : ProCGroups.FiniteGroupClass.{u})
    (hVar : ProCGroups.FiniteGroupClass.Variety C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
      Cardinal.mk Fdata.basis =
        (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) :
          Cardinal) := by
  classical
  rcases hVar.closureBundle_of_isomClosed_extensionClosed hIso hExt with
    ⟨hForm, hSub, hIso', hQuot, hExt'⟩
  let n : ℕ := _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F)))
  rcases exists_finiteIndexBasisCarrierAndMap_openSubgroup
      C hForm hSub hIso' hQuot hExt' hF H with
    ⟨B, hBfin, μ, hμfree⟩
  letI : Finite B := hBfin
  letI : Fintype B := Fintype.ofFinite B
  let Fdata : FreeProCGroupOnConvergingSetData
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) :=
    { basis := B
      carrier := ↥(H : Subgroup F)
      instGroup := inferInstance
      instTopologicalSpace := inferInstance
      instIsTopologicalGroup := inferInstance
      inclusion := μ
      isFree := hμfree }
  letI : Fintype X := Fintype.ofFinite X
  let Fambient : FreeProCGroupOnConvergingSetData
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) :=
    { basis := X
      carrier := F
      instGroup := inferInstance
      instTopologicalSpace := inferInstance
      instIsTopologicalGroup := inferInstance
      inclusion := ι
      isFree := hF }
  have hAmbientRank :
      Cardinal.mk X = Generation.topologicalRank F :=
    basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fambient
  have hdF : Generation.topologicalRank F = Nat.card X := by
    calc
      Generation.topologicalRank F = Cardinal.mk X := hAmbientRank.symm
      _ = (Nat.card X : Cardinal) := by simp only [Cardinal.mk_fintype, Nat.card_eq_fintype_card]
  have hdHle :
      Generation.topologicalRank ↥(H : Subgroup F) ≤ (n : Cardinal) := by
    simpa [n] using
      topologicalRank_openSubgroup_le_rankTransform_of_topologicalRank_eq_nat
        (G := F) hF.isProC.1 hdF H
  have hDataBasis :
      Cardinal.mk Fdata.basis = Generation.topologicalRank Fdata.carrier :=
    basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fdata
  have hle : Cardinal.mk Fdata.basis ≤ (n : Cardinal) := by
    simpa [Fdata] using hDataBasis.trans_le hdHle
  rcases exists_exactGeneratingFamily_openSubgroup_of_finiteBasis
      C hForm hSub hIso' hQuot hExt' hcyc hF H with
    ⟨κ, hκ⟩
  letI : TopologicalSpace (FreeGroup (ULift.{u} (Fin n))) := ⊥
  letI : DiscreteTopology (FreeGroup (ULift.{u} (Fin n))) := ⟨rfl⟩
  letI : IsTopologicalGroup (FreeGroup (ULift.{u} (Fin n))) := by infer_instance
  let φ : FreeGroup (ULift.{u} (Fin n)) →ₜ* ↥(H : Subgroup F) :=
    { toMonoidHom := FreeGroup.lift κ
      continuous_toFun := continuous_of_discreteTopology }
  have hComp :
      ProCGroups.Completion.IsProCCompletion
        (ProCGroups.ProC.finiteGroupClassProCPredicate C)
        (FreeGroup (ULift.{u} (Fin n))) ↥(H : Subgroup F) φ := by
    letI : CompactSpace F := IsProCGroup.compactSpace hF.isProC
    obtain ⟨Y, hYfree, hYcard⟩ :=
      exists_freeBasis_comap_freeGroupLift_of_openSubgroup_of_rankTransform
        (F := F) (X := X) hF.generates_range H
    let βF : FreeGroup X →* F := FreeGroup.lift ι
    let L : Subgroup (FreeGroup X) := Subgroup.comap βF (H : Subgroup F)
    let ψ : L →* ↥(H : Subgroup F) :=
      { toFun := fun g => ⟨βF g.1, g.2⟩
        map_one' := by simp only [OneMemClass.coe_one, map_one, Subgroup.mk_eq_one]
        map_mul' := by
          intro a b
          ext
          simp only [Subgroup.coe_mul, map_mul]}
    letI : TopologicalSpace (FreeGroup X) := ⊥
    letI : DiscreteTopology (FreeGroup X) := ⟨rfl⟩
    letI : IsTopologicalGroup (FreeGroup X) := by infer_instance
    have hβFdense : DenseRange βF :=
      denseRange_freeGroupLift_of_topologicallyGenerates
        (F := F) (X := X) hF.generates_range
    have hψdense : DenseRange ψ := by
      exact denseRange_comapMap_of_openSubgroup (φ := βF) hβFdense H.isOpen'
    letI : TopologicalSpace (FreeGroup Y) := ⊥
    letI : DiscreteTopology (FreeGroup Y) := ⟨rfl⟩
    letI : IsTopologicalGroup (FreeGroup Y) := by infer_instance
    let bY : FreeGroupBasis Y L := Classical.choice hYfree
    let eY : FreeGroup Y ≃* L := bY.repr.symm
    let φY : FreeGroup Y →ₜ* ↥(H : Subgroup F) :=
      { toMonoidHom := ψ.comp eY.toMonoidHom
        continuous_toFun := continuous_of_discreteTopology }
    have hψcont : Continuous ψ := by
      simpa using (continuous_of_discreteTopology : Continuous ψ)
    have hφYdense : DenseRange φY := by
      simpa [φY] using
        hψdense.comp (Function.Surjective.denseRange eY.surjective) hψcont
    have hψfinite :
        ∀ {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
          [Finite Q] [DiscreteTopology Q],
          C Q →
          ∀ χL : L →* Q,
            ∃! φbar : ↥(H : Subgroup F) →* Q,
              Continuous φbar ∧ φbar.comp ψ = χL := by
      intro Q _ _ _ _ _ hQ χL
      rcases
          exists_continuousFiniteQuotientLift_of_comap_freeGroupLift
            (C := C)
            (hForm := hForm) (hSub := hSub) (hIso := hIso')
            (hQuot := hQuot) (hExt := hExt')
            (X := X) (F := F) (ι := ι) hF H hQ χL with
        ⟨φbar, hφbarCont, hφbarFac⟩
      refine ⟨φbar, ⟨hφbarCont, hφbarFac⟩, ?_⟩
      intro φbar' hφbar'
      have hEq : (fun h : ↥(H : Subgroup F) => φbar h) = fun h => φbar' h := by
        apply DenseRange.equalizer (f := ψ) hψdense
        · exact hφbarCont
        · exact hφbar'.1
        · funext l
          exact congrArg (fun f : L →* Q => f l) (hφbarFac.trans hφbar'.2.symm)
      apply MonoidHom.ext
      intro h
      simpa using (congrArg (fun f : ↥(H : Subgroup F) → Q => f h) hEq).symm
    have hfinite :
        DenseAbstractSchreierFiniteQuotientLiftProperty
          (C := C) H φY.toMonoidHom := by
      exact denseAbstractSchreierFiniteQuotientLiftProperty_of_equiv
        (C := C) (H := H) (eY := eY) (ψ := ψ) hψfinite
    have hCompY :
        ProCGroups.Completion.IsProCCompletion
          (ProCGroups.ProC.finiteGroupClassProCPredicate C)
          (FreeGroup Y) ↥(H : Subgroup F) φY := by
      exact isProCCompletion_denseAbstractSchreier_of_finiteQuotientLifts
        (C := C)
        (hForm := hForm) (hSub := hSub) (hIso := hIso') (hQuot := hQuot)
        (X := X) (F := F) (ι := ι) hF H hφYdense hfinite
    exact
      isProCCompletion_freeGroupLift_of_exactGeneratingFamily_of_completion
        (C := C) hSub hIso' hQuot hcyc
        (n := n) (Y := Y) (by simpa [n] using hYcard) hCompY hκ
  let Fexact : FreeProCGroupOnConvergingSetData
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) :=
    { basis := ULift.{u} (Fin n)
      carrier := ↥(H : Subgroup F)
      instGroup := inferInstance
      instTopologicalSpace := inferInstance
      instIsTopologicalGroup := inferInstance
      inclusion := κ
      isFree := by
        have hfree :=
          proCCompletionOfAbstractFreeGroup_is_free
            (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C)
            (X := ULift.{u} (Fin n)) (Fhat := ↥(H : Subgroup F)) (ι := φ) hComp
        convert hfree using 1
        ext x
        change ((κ x : ↥(H : Subgroup F)) : F) =
          ((FreeGroup.lift κ (FreeGroup.of x) : ↥(H : Subgroup F)) : F)
        simp only [FreeGroup.lift_apply_of]}
  have hExactBasis :
      Cardinal.mk Fexact.basis = Generation.topologicalRank Fexact.carrier :=
    basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fexact
  have hExactCard : Cardinal.mk Fexact.basis = (n : Cardinal) := by
    simp only [Cardinal.mk_fintype, Fintype.card_ulift, Fintype.card_fin, Fexact]
  have hge : (n : Cardinal) ≤ Cardinal.mk Fdata.basis := by
    exact le_of_eq <| by
      calc
        (n : Cardinal) = Cardinal.mk Fexact.basis := hExactCard.symm
        _ = Generation.topologicalRank Fexact.carrier := hExactBasis
        _ = Generation.topologicalRank Fdata.carrier := by rfl
        _ = Cardinal.mk Fdata.basis := hDataBasis.symm
  refine ⟨Fdata, ⟨ContinuousMulEquiv.refl _⟩, ?_⟩
  have hCard : Cardinal.mk Fdata.basis = (n : Cardinal) := le_antisymm hle hge
  simpa [n] using hCard

/-- Finite-rank Schreier basis theorem using a bundled hypothesis record. -/
theorem exists_basis_openSubgroup_of_finiteRank_of_schreierBasisHypotheses
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : SchreierBasisFiniteRankHypotheses C)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
      Cardinal.mk Fdata.basis =
        (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) :
          Cardinal) :=
  exists_basis_openSubgroup_of_extensionClosed_finiteRank
    (C := C) hC.variety hC.isomClosed hC.extensionClosed hC.hasNontrivialCyclic hF H

/-- Finite-rank Melnikov-formation variant with explicit subgroup closure and exact Schreier
rank-transform cardinality. -/
theorem exists_basis_openSubgroup_of_melnikovFormation_finiteRank_of_subgroupClosed
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.MelnikovFormation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
      Cardinal.mk Fdata.basis =
        (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) :
          Cardinal) := by
  let hVar : ProCGroups.FiniteGroupClass.Variety C :=
    { subgroupClosed := hSub
      quotientClosed := hC.quotientClosed
      finiteProductClosed := hC.formation.finiteProductClosed }
  exact
    exists_basis_openSubgroup_of_extensionClosed_finiteRank
      (C := C) hVar hC.isomClosed hC.extensionClosed hcyc hF H

/-- Finite-rank Melnikov-formation open-subgroup variant. -/
theorem exists_basis_openNormalSubgroup_of_melnikovFormation_finiteRank
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.MelnikovFormation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    [DiscreteTopology (Set.range ι)]
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
      Cardinal.mk Fdata.basis =
        (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) :
          Cardinal) :=
  exists_basis_openSubgroup_of_melnikovFormation_finiteRank_of_subgroupClosed
    (C := C) hC hSub hcyc hF H

/-- Finite-rank open-subnormal Melnikov statement. The current Schreier package records the
expected bounded generating family converging to `1`; it does not claim that this family is already
identified as a free pro-`C` basis. -/
theorem exists_basis_openSubnormalSubgroup_of_melnikovFormation_finiteRank
    (C : ProCGroups.FiniteGroupClass.{u})
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hF : IsFreeProCGroupOnConvergingSet
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X F ι)
    (H : OpenSubgroup F) :
    ∃ (Y : Type u) (κ : Y → ↥(H : Subgroup F)),
      Generation.GeneratesAndConvergesToOne (G := ↥(H : Subgroup F)) (Set.range κ) ∧
      Cardinal.mk Y ≤
        (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) :
          Cardinal) := by
  classical
  let hFprof : ProCGroups.IsProfiniteGroup F := hF.isProC.1
  letI : CompactSpace F := ProCGroups.IsProfiniteGroup.compactSpace hFprof
  letI : T2Space F := ProCGroups.IsProfiniteGroup.t2Space hFprof
  letI : TotallyDisconnectedSpace F := ProCGroups.IsProfiniteGroup.totallyDisconnectedSpace hFprof
  let hHprof : ProCGroups.IsProfiniteGroup ↥(H : Subgroup F) :=
    ProCGroups.IsProfiniteGroup.of_isClosed_subgroup
      (G := F) hFprof (H : Subgroup F)
      (Subgroup.isClosed_of_isOpen (H : Subgroup F) H.isOpen')
  have hdFleX : Generation.topologicalRank F ≤ (Nat.card X : Cardinal) := by
    letI : Fintype X := Fintype.ofFinite X
    calc
      Generation.topologicalRank F ≤ Cardinal.mk (Set.range ι) := by
        exact Generation.topologicalRank_le_mk_of_generatesAndConvergesToOne
          (G := F)
          ⟨hF.generates_range, hF.convergesToOne.range⟩
      _ ≤ Cardinal.mk X := Cardinal.mk_range_le
      _ = (Nat.card X : Cardinal) := by simp only [Cardinal.mk_fintype, Nat.card_eq_fintype_card]
  have hdFlt : Generation.topologicalRank F < Cardinal.aleph0 :=
    lt_of_le_of_lt hdFleX (Cardinal.natCast_lt_aleph0 (n := Nat.card X))
  let d : ℕ := Cardinal.toNat (Generation.topologicalRank F)
  have hdF : Generation.topologicalRank F = d := by
    symm
    exact Cardinal.cast_toNat_of_lt_aleph0 hdFlt
  have hdle : d ≤ Nat.card X := by
    simpa [d, Cardinal.toNat_natCast] using
      Cardinal.toNat_le_toNat hdFleX (Cardinal.natCast_lt_aleph0 (n := Nat.card X))
  have hdHle :
      Generation.topologicalRank ↥(H : Subgroup F) ≤
        (_root_.ReidemeisterSchreier.Schreier.rankTransform d (Nat.card (F ⧸ (H : Subgroup F))) : Cardinal) :=
    topologicalRank_openSubgroup_le_rankTransform_of_topologicalRank_eq_nat
      (G := F) hFprof hdF H
  have hRankMono :
      _root_.ReidemeisterSchreier.Schreier.rankTransform d (Nat.card (F ⧸ (H : Subgroup F))) ≤
        _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) :=
    _root_.ReidemeisterSchreier.Schreier.rankTransform_mono_left hdle
  rcases Generation.exists_generatorsConvergingToOne (G := ↥(H : Subgroup F)) hHprof with
    ⟨S0, hS0⟩
  rcases Generation.exists_generatesAndConvergesToOne_card_eq_topologicalRank
      (G := ↥(H : Subgroup F)) ⟨S0, hS0⟩ with
    ⟨S, hS, hScard⟩
  let κ : S → ↥(H : Subgroup F) := Subtype.val
  have hκrange : Set.range κ = S := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact s.2
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
  refine ⟨S, κ, ?_, ?_⟩
  · simpa [κ, hκrange] using hS
  · calc
      Cardinal.mk S = Generation.topologicalRank ↥(H : Subgroup F) := hScard
      _ ≤ (_root_.ReidemeisterSchreier.Schreier.rankTransform d (Nat.card (F ⧸ (H : Subgroup F))) : Cardinal) := hdHle
      _ ≤ (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))) :
          Cardinal) := by
        exact_mod_cast hRankMono

/-- Finite discrete pointed input gives a finite converging-set basis model for every open
subgroup, without an external pointed-to-converging-set bridge. -/
theorem exists_finiteConvergingSetBasis_openSubgroup_of_finitePointedFreeProC
    {C : ProCGroups.FiniteGroupClass.{u}}
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [Finite X]
    {x0 : X}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    {ι : X → F}
    (hF : IsPointedFreeProCGroupOn
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) X x0 F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : FreeProCGroupOnConvergingSetData
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧ Finite Fdata.basis := by
  classical
  letI : CompactSpace F := IsProCGroup.compactSpace hF.isProC
  letI : T2Space F := IsProCGroup.t2Space hF.isProC
  rcases
      exists_pointedFreeRightSchreierGeneratorFamily_of_openSubgroup
        (C := C) hForm hSub hIso hQuot hExt hF H with
    ⟨κ, _hκcont, _hκbase, _hκone, _hκcompact, _hκclosed, hκfree⟩
  letI : Finite (OpenSubgroupRightQuotient H) :=
    finite_openSubgroupRightQuotient (F := F) H
  letI : Finite (Set.range κ) := (Set.finite_range κ).to_subtype
  letI : DiscreteTopology (Set.range κ) :=
    DiscreteTopology.of_finite_of_isClosed_singleton fun _ => isClosed_singleton
  exact
    freeOnFinitePointedDiscreteSpace_has_finiteConvergingSetBasis
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C) hκfree



end Profinite
end ReidemeisterSchreier
