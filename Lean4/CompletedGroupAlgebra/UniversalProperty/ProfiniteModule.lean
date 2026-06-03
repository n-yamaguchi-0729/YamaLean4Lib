import CompletedGroupAlgebra.UniversalProperty.OpenSubmoduleQuotient

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/UniversalProperty/ProfiniteModule.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite-target universal property

This module upgrades finite-discrete and open-quotient lifting results to the universal property for profinite target modules.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The closed fiber in a profinite target determined by the quotient-valued extension modulo
one open submodule. -/
def completedGroupAlgebraLiftFiberSet
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f)
    (x : Carrier R G)
    (W : ProfiniteModuleOpenSubmodule (R := R) N) : Set N :=
  {y | Submodule.mkQ W.1 y =
    completedGroupAlgebraLiftToOpenSubmoduleQuotient
      (R := R) (G := G) hG N hN f hf W.1 W.2 x}

/-- The quotient fiber attached to an open submodule is closed. -/
theorem completedGroupAlgebraLiftFiberSet_isClosed
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f)
    (x : Carrier R G)
    (W : ProfiniteModuleOpenSubmodule (R := R) N) :
    IsClosed (completedGroupAlgebraLiftFiberSet
      (R := R) (G := G) hG N hN f hf x W) := by
  let hdisc : IsDiscreteModule R (N ⧸ W.1) :=
    quotient_openSubmodule_isDiscreteModule R N hN W.1 W.2
  letI : DiscreteTopology (N ⧸ W.1) := hdisc.2
  have hqcont : Continuous (Submodule.mkQ W.1 : N → N ⧸ W.1) := by
    change Continuous (Submodule.Quotient.mk (p := W.1))
    exact continuous_quotient_mk'
  change IsClosed ((Submodule.mkQ W.1 : N → N ⧸ W.1) ⁻¹'
    ({completedGroupAlgebraLiftToOpenSubmoduleQuotient
      (R := R) (G := G) hG N hN f hf W.1 W.2 x} : Set (N ⧸ W.1)))
  exact (isClosed_discrete _).preimage hqcont

/-- Finite intersection property for the fibers used to assemble the profinite-target lift. -/
theorem completedGroupAlgebraLiftFiberSet_finite_inter_nonempty
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f)
    (x : Carrier R G)
    (s : Finset (ProfiniteModuleOpenSubmodule (R := R) N)) :
    (⋂ W ∈ s, completedGroupAlgebraLiftFiberSet
      (R := R) (G := G) hG N hN f hf x W).Nonempty := by
  classical
  rcases exists_openSubmodule_le_finset (R := R) N s with ⟨K, hK⟩
  rcases Submodule.mkQ_surjective K.1
      (completedGroupAlgebraLiftToOpenSubmoduleQuotient
        (R := R) (G := G) hG N hN f hf K.1 K.2 x) with
    ⟨z, hz⟩
  refine ⟨z, ?_⟩
  simp only [Set.mem_iInter]
  intro W hWs
  dsimp [completedGroupAlgebraLiftFiberSet]
  calc
    Submodule.mkQ W.1 z = Submodule.factor (hK W hWs) (Submodule.mkQ K.1 z) := by
      rw [Submodule.factor_mk]
    _ = Submodule.factor (hK W hWs)
        (completedGroupAlgebraLiftToOpenSubmoduleQuotient
          (R := R) (G := G) hG N hN f hf K.1 K.2 x) := by
      rw [hz]
    _ = completedGroupAlgebraLiftToOpenSubmoduleQuotient
        (R := R) (G := G) hG N hN f hf W.1 W.2 x := by
      exact completedGroupAlgebraLiftToOpenSubmoduleQuotient_factor
        (R := R) (G := G) hG N hN f hf (hK W hWs) K.2 W.2 x

/-- Compactness of the profinite target gives a simultaneous lift of the compatible quotient
values. -/
theorem completedGroupAlgebraLiftFiberSet_iInter_nonempty
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f)
    (x : Carrier R G) :
    (⋂ W : ProfiniteModuleOpenSubmodule (R := R) N,
      completedGroupAlgebraLiftFiberSet
        (R := R) (G := G) hG N hN f hf x W).Nonempty := by
  letI : CompactSpace N := hN.2.2.2.1
  exact CompactSpace.iInter_nonempty
    (t := fun W : ProfiniteModuleOpenSubmodule (R := R) N =>
      completedGroupAlgebraLiftFiberSet
        (R := R) (G := G) hG N hN f hf x W)
    (fun W => completedGroupAlgebraLiftFiberSet_isClosed
      (R := R) (G := G) hG N hN f hf x W)
    (fun s => completedGroupAlgebraLiftFiberSet_finite_inter_nonempty
      (R := R) (G := G) hG N hN f hf x s)

/-- The assembled pointwise lift from `[[RG]]` to a profinite target module. -/
def completedGroupAlgebraLiftToProfiniteModuleFun
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f) :
    Carrier R G → N :=
  fun x => Classical.choose
    (completedGroupAlgebraLiftFiberSet_iInter_nonempty
      (R := R) (G := G) hG N hN f hf x)

/-- The assembled point maps to the prescribed quotient-valued extension modulo every open
submodule. -/
theorem completedGroupAlgebraLiftToProfiniteModuleFun_quotient
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f)
    (W : ProfiniteModuleOpenSubmodule (R := R) N)
    (x : Carrier R G) :
    Submodule.mkQ W.1
        (completedGroupAlgebraLiftToProfiniteModuleFun
          (R := R) (G := G) hG N hN f hf x) =
      completedGroupAlgebraLiftToOpenSubmoduleQuotient
        (R := R) (G := G) hG N hN f hf W.1 W.2 x := by
  have hmem := Classical.choose_spec
    (completedGroupAlgebraLiftFiberSet_iInter_nonempty
      (R := R) (G := G) hG N hN f hf x)
  exact (Set.mem_iInter.1 hmem W : _)

/-- The assembled lift has the prescribed values on the completed group-like elements. -/
@[simp]
theorem completedGroupAlgebraLiftToProfiniteModuleFun_apply_of
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f)
    (g : G) :
    completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) hG N hN f hf (completedGroupAlgebraOf R G g) = f g := by
  apply profiniteModule_ext_of_openSubmoduleQuotients (R := R) N hN
  intro W hW
  rw [completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) hG N hN f hf ⟨W, hW⟩,
    completedGroupAlgebraLiftToOpenSubmoduleQuotient_apply_of]

/-- Additivity of the assembled profinite-target lift, checked after all open-submodule
quotients. -/
theorem completedGroupAlgebraLiftToProfiniteModuleFun_add
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f)
    (x y : Carrier R G) :
    completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) hG N hN f hf (x + y) =
      completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) hG N hN f hf x +
      completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) hG N hN f hf y := by
  apply profiniteModule_ext_of_openSubmoduleQuotients (R := R) N hN
  intro W hW
  rw [completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) hG N hN f hf ⟨W, hW⟩,
    map_add,
    ← completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) hG N hN f hf ⟨W, hW⟩ x,
    ← completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) hG N hN f hf ⟨W, hW⟩ y]
  rfl

/-- Scalar compatibility of the assembled profinite-target lift, checked after all
open-submodule quotients. -/
theorem completedGroupAlgebraLiftToProfiniteModuleFun_smul
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f)
    (r : R) (x : Carrier R G) :
    completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) hG N hN f hf (r • x) =
      r • completedGroupAlgebraLiftToProfiniteModuleFun
        (R := R) (G := G) hG N hN f hf x := by
  apply profiniteModule_ext_of_openSubmoduleQuotients (R := R) N hN
  intro W hW
  rw [completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) hG N hN f hf ⟨W, hW⟩,
    map_smul,
    ← completedGroupAlgebraLiftToProfiniteModuleFun_quotient
      (R := R) (G := G) hG N hN f hf ⟨W, hW⟩ x]
  rfl

/-- Existence half of Lemma 5.3.5(d): a continuous map from the profinite group `G` to a
profinite `R`-module extends to a continuous `R`-linear map out of `[[RG]]`. -/
def completedGroupAlgebraLiftToProfiniteModule
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f) :
    Carrier R G →L[R] N where
  toFun := completedGroupAlgebraLiftToProfiniteModuleFun (R := R) (G := G) hG N hN f hf
  map_add' := completedGroupAlgebraLiftToProfiniteModuleFun_add
    (R := R) (G := G) hG N hN f hf
  map_smul' := completedGroupAlgebraLiftToProfiniteModuleFun_smul
    (R := R) (G := G) hG N hN f hf
  cont := by
    apply continuous_of_forall_openSubmodule_quotient_continuous (R := R) N hN
    intro W hW
    have hEq : (fun x : Carrier R G =>
        Submodule.mkQ W
          (completedGroupAlgebraLiftToProfiniteModuleFun
            (R := R) (G := G) hG N hN f hf x)) =
        completedGroupAlgebraLiftToOpenSubmoduleQuotient
          (R := R) (G := G) hG N hN f hf W hW := by
      funext x
      exact completedGroupAlgebraLiftToProfiniteModuleFun_quotient
        (R := R) (G := G) hG N hN f hf ⟨W, hW⟩ x
    rw [hEq]
    exact (completedGroupAlgebraLiftToOpenSubmoduleQuotient
      (R := R) (G := G) hG N hN f hf W hW).continuous

/-- The profinite-target lift has the prescribed value on completed group-like elements. -/
@[simp]
theorem completedGroupAlgebraLiftToProfiniteModule_apply_of
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f)
    (g : G) :
    completedGroupAlgebraLiftToProfiniteModule
        (R := R) (G := G) hG N hN f hf (completedGroupAlgebraOf R G g) = f g :=
  completedGroupAlgebraLiftToProfiniteModuleFun_apply_of
    (R := R) (G := G) hG N hN f hf g

/-- Full universal property in Lemma 5.3.5(d). -/
theorem completedGroupAlgebra_existsUnique_lift_to_profiniteModule
    (hG : ProCGroups.IsProfiniteGroup G)
    (N : Type (max u v)) [AddCommGroup N] [TopologicalSpace N] [Module R N]
    (hN : IsProfiniteModule R N) (f : G → N) (hf : Continuous f) :
    ∃! F : Carrier R G →L[R] N,
      ∀ g : G, F (completedGroupAlgebraOf R G g) = f g := by
  letI : T2Space N := hN.2.2.2.2.1
  let F := completedGroupAlgebraLiftToProfiniteModule (R := R) (G := G) hG N hN f hf
  refine ⟨F, ?_, ?_⟩
  · intro g
    exact completedGroupAlgebraLiftToProfiniteModule_apply_of
      (R := R) (G := G) hG N hN f hf g
  · intro K hK
    apply completedGroupAlgebraContinuousLinearMap_ext_of_basis (R := R) (G := G) hG
    intro g
    rw [completedGroupAlgebraLiftToProfiniteModule_apply_of, hK]

/-- Book Lemma 5.3.5(d): `[[RG]]` is the free profinite `R`-module on the profinite space
`G`, with basis map `g ↦ g` inside the completed group algebra. -/
theorem completedGroupAlgebraOf_freeProfiniteModule
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G) :
    IsFreeProfiniteModuleOn R G (Carrier R G) (completedGroupAlgebraOf R G) := by
  refine ⟨hR, completedGroupAlgebra_isProfiniteModule (R := R) (G := G) hR,
    continuous_completedGroupAlgebraOf (R := R) (G := G),
    completedGroupAlgebraOf_dense_span (R := R) (G := G) hG, ?_⟩
  intro N _addN _topN _modN hN f hf
  exact completedGroupAlgebra_existsUnique_lift_to_profiniteModule
    (R := R) (G := G) hG N hN f hf
end

end CompletedGroupAlgebra
