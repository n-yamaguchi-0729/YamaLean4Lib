import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.ZMod
import ProCGroups.Abelian.TopologicalAbelianization
import ProCGroups.FreeProC.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProC/Abelianization.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Abelianization coordinates of free pro-C groups

This module records finite cyclic coordinate maps out of the topological abelianization of a
finite-rank free pro-`Σ` group.
-/

open scoped Topology

namespace ProCGroups.FreeProC

universe u v

/-- A finite cyclic coordinate on the topological abelianization of a finite-rank free
pro-`Σ` group, sending one chosen basis element to the standard generator. -/
theorem exists_freeAbelianizationCyclicCoordinate
    {sigma : Set ℕ}
    {F : Type u} [TopologicalSpace F] [Group F] [IsTopologicalGroup F]
    {r L : ℕ} (hLpos : 0 < L)
    (hLsigma : ProCGroups.FiniteGroupClass.IsSigmaNumber sigma L)
    (X : Fin r → F)
    (hFree :
      IsFreeProCGroupOnConvergingSet
        (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate
          (ProCGroups.FiniteGroupClass.sigmaGroup sigma)) (Fin r) F X)
    (i : Fin r) :
    ∃ χ : TopologicalAbelianization F →ₜ* Multiplicative (ZMod L),
      χ (ProCGroups.Abelian.TopologicalAbelianization.mk F (X i)) =
        Multiplicative.ofAdd (1 : ZMod L) := by
  classical
  let C : ProCGroups.FiniteGroupClass.{u} := ProCGroups.FiniteGroupClass.sigmaGroup sigma
  letI : NeZero L := ⟨Nat.ne_of_gt hLpos⟩
  let T : Type u := ULift.{u} (Multiplicative (ZMod L))
  letI : Group T := inferInstance
  letI : CommGroup T := inferInstance
  letI : TopologicalSpace T := ⊥
  letI : DiscreteTopology T := ⟨rfl⟩
  letI : IsTopologicalGroup T := by infer_instance
  let φ : Fin r → T :=
    fun j => if j = i then ULift.up (Multiplicative.ofAdd (1 : ZMod L)) else 1
  have hφ : FamilyConvergesToOne (G := T) φ :=
    FamilyConvergesToOne.of_finite_domain φ
  have htarget :
      (ProCGroups.ProC.finiteGroupClassProCPredicate C)
        (G := T) := by
    letI : Finite T := by
      exact Finite.of_equiv (Multiplicative (ZMod L)) Equiv.ulift.symm
    exact
      ProCGroups.ProC.IsProCGroup.of_finite_discrete
        (C := C) (G := T)
        (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed sigma)
        (ProCGroups.FiniteGroupClass.sigmaGroup_cyclicZMod (sigma := sigma) hLpos hLsigma)
  rcases
      hFree.existsUnique_liftHom_of_convergesToOne_of_finiteGroupClass
        C
        (ProCGroups.FiniteGroupClass.sigmaGroup_isomClosed sigma)
        (ProCGroups.FiniteGroupClass.sigmaGroup_subgroupClosed sigma)
        (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed sigma)
        htarget φ hφ with
    ⟨χF, hχF, _⟩
  letI : TopologicalSpace (Multiplicative (ZMod L)) := ⊥
  letI : DiscreteTopology (Multiplicative (ZMod L)) := ⟨rfl⟩
  letI : IsTopologicalGroup (Multiplicative (ZMod L)) := by infer_instance
  let down : T →ₜ* Multiplicative (ZMod L) :=
    { toMonoidHom := (MulEquiv.ulift : T ≃* Multiplicative (ZMod L)).toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  refine ⟨down.comp (ProCGroups.Abelian.TopologicalAbelianization.lift χF), ?_⟩
  change down (ProCGroups.Abelian.TopologicalAbelianization.lift χF
    (ProCGroups.Abelian.TopologicalAbelianization.mk F (X i))) =
      Multiplicative.ofAdd (1 : ZMod L)
  rw [ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk, hχF]
  change (MulEquiv.ulift : T ≃* Multiplicative (ZMod L)) (φ i) =
    Multiplicative.ofAdd (1 : ZMod L)
  simp only [↓reduceIte, φ]
  rfl

end ProCGroups.FreeProC
