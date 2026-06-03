import FoxDifferential.Completed.FreeProC.SemidirectKernelBasis
import FoxDifferential.Completed.ProCIntegerCoefficients.Augmentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Continuous/Topology.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Continuous crossed differentials

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.Completion
open scoped BigOperators

universe u v

/-- The finite quotients of the all-finite pro-`C` predicate are exactly finite groups. -/
instance instFactFiniteOnlyAllFiniteProCFiniteQuotientClass :
    Fact (ProCGroups.FiniteGroupClass.FiniteOnly
      ProCGroups.ProC.allFiniteProC.finiteQuotientClass) :=
  ⟨by
    intro G _ hG
    exact (ProCGroups.ProC.allFiniteProC_finiteQuotientClass_iff_finite).1 hG⟩

section BoundaryMapContinuity

variable {R : Type u} [Ring R] [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R]
variable {X : Type v} [Fintype X]

/-- A finite Fox boundary map is continuous over any topological ring. -/
theorem continuous_foxBoundaryMap (generatorBoundary : X → R) :
    Continuous (foxBoundaryMap generatorBoundary) := by
  change Continuous (fun v : X → R => ∑ x : X, v x * generatorBoundary x)
  exact continuous_finset_sum _ fun x _ => (continuous_apply x).mul continuous_const

end BoundaryMapContinuity

section CompletedGroupAlgebraTopology

variable (C : ProCGroups.FiniteGroupClass.{u})
variable [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The discrete topology on a finite pro-`C` stage of `Z_C[[G]]`. -/
instance instTopologicalSpaceZCCompletedGroupAlgebraStage
    (i : ZCCompletedGroupAlgebraIndex C G) :
    TopologicalSpace (ZCCompletedGroupAlgebraStage C G i) :=
  ⊥

instance instDiscreteTopologyZCCompletedGroupAlgebraStage
    (i : ZCCompletedGroupAlgebraIndex C G) :
    DiscreteTopology (ZCCompletedGroupAlgebraStage C G i) :=
  ⟨rfl⟩

instance instCompactSpaceZCCompletedGroupAlgebraStage
    (i : ZCCompletedGroupAlgebraIndex C G) :
    CompactSpace (ZCCompletedGroupAlgebraStage C G i) := by
  letI : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  letI : Finite (ZCCompletedGroupAlgebraStage C G i) :=
    finite_modNCompletedGroupAlgebraStageInClass
      (n := i.1.modulus) (G := G) C
      (Fact.out (p := ProCGroups.FiniteGroupClass.FiniteOnly C)) i.2
  letI : Fintype (ZCCompletedGroupAlgebraStage C G i) := Fintype.ofFinite _
  infer_instance

instance instT2SpaceZCCompletedGroupAlgebraStage
    (i : ZCCompletedGroupAlgebraIndex C G) :
    T2Space (ZCCompletedGroupAlgebraStage C G i) :=
  inferInstance

instance instTotallyDisconnectedSpaceZCCompletedGroupAlgebraStage
    (i : ZCCompletedGroupAlgebraIndex C G) :
    TotallyDisconnectedSpace (ZCCompletedGroupAlgebraStage C G i) :=
  inferInstance

/-- The pro-`C` completed group algebra is compact in its inverse-limit topology. -/
instance instCompactSpaceZCCompletedGroupAlgebra :
    CompactSpace (ZCCompletedGroupAlgebra C G) := by
  let S := zcCompletedGroupAlgebraSystem C G
  change CompactSpace S.inverseLimit
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C G, TopologicalSpace (S.X i) := fun _ =>
    inferInstance
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C G, CompactSpace (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    infer_instance
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C G, T2Space (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    infer_instance
  infer_instance

/-- The pro-`C` completed group algebra is Hausdorff in its inverse-limit topology. -/
instance instT2SpaceZCCompletedGroupAlgebra :
    T2Space (ZCCompletedGroupAlgebra C G) := by
  let S := zcCompletedGroupAlgebraSystem C G
  change T2Space S.inverseLimit
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C G, TopologicalSpace (S.X i) := fun _ =>
    inferInstance
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C G, T2Space (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    infer_instance
  exact S.t2Space_inverseLimit

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- A finite stage projection from `Z_C[[G]]` is continuous. -/
theorem continuous_zcCompletedGroupAlgebraProjection
    (i : ZCCompletedGroupAlgebraIndex C G) :
    Continuous (zcCompletedGroupAlgebraProjection C G i) :=
  (continuous_apply i).comp continuous_subtype_val

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- A finite stage projection from `Z_C[[G]]`, regarded as a ring homomorphism, is continuous. -/
theorem continuous_zcCompletedGroupAlgebraProjectionRingHom
    (i : ZCCompletedGroupAlgebraIndex C G) :
    Continuous (zcCompletedGroupAlgebraProjectionRingHom C G i) :=
  continuous_zcCompletedGroupAlgebraProjection C G i

/-- The pro-`C` completed group algebra is totally disconnected in its inverse-limit
topology. -/
instance instTotallyDisconnectedSpaceZCCompletedGroupAlgebra :
    TotallyDisconnectedSpace (ZCCompletedGroupAlgebra C G) := by
  let S := zcCompletedGroupAlgebraSystem C G
  change TotallyDisconnectedSpace S.inverseLimit
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C G, TopologicalSpace (S.X i) := fun _ =>
    inferInstance
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C G, TotallyDisconnectedSpace (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    infer_instance
  exact S.totallyDisconnectedSpace_inverseLimit

/-- Addition on the pro-`C` completed group algebra is continuous. -/
instance instContinuousAddZCCompletedGroupAlgebra :
    ContinuousAdd (ZCCompletedGroupAlgebra C G) where
  continuous_add := by
    have hval : Continuous (fun p : ZCCompletedGroupAlgebra C G ×
        ZCCompletedGroupAlgebra C G =>
        ((p.1 + p.2 : ZCCompletedGroupAlgebra C G) :
          (i : ZCCompletedGroupAlgebraIndex C G) → ZCCompletedGroupAlgebraStage C G i)) := by
      exact continuous_pi fun i =>
        (continuous_of_discreteTopology :
          Continuous (fun q : ZCCompletedGroupAlgebraStage C G i ×
              ZCCompletedGroupAlgebraStage C G i => q.1 + q.2)).comp
            (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).prodMk
              ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
    simpa [Subtype.eta] using
      (Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible C G) hval
        (fun p => (p.1 + p.2 : ZCCompletedGroupAlgebra C G).property))

/-- Negation on the pro-`C` completed group algebra is continuous. -/
instance instContinuousNegZCCompletedGroupAlgebra :
    ContinuousNeg (ZCCompletedGroupAlgebra C G) where
  continuous_neg := by
    change Continuous (fun x : ZCCompletedGroupAlgebra C G => -x)
    have hval : Continuous (fun x : ZCCompletedGroupAlgebra C G =>
        ((-x : ZCCompletedGroupAlgebra C G) :
          (i : ZCCompletedGroupAlgebraIndex C G) → ZCCompletedGroupAlgebraStage C G i)) := by
      exact continuous_pi fun i =>
        (continuous_of_discreteTopology :
          Continuous (fun y : ZCCompletedGroupAlgebraStage C G i => -y)).comp
          ((continuous_apply i).comp continuous_subtype_val)
    simpa [Subtype.eta] using
      (Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible C G) hval
        (fun x => (-x : ZCCompletedGroupAlgebra C G).property))

/-- The additive group structure on the pro-`C` completed group algebra is topological. -/
instance instIsTopologicalAddGroupZCCompletedGroupAlgebra :
    IsTopologicalAddGroup (ZCCompletedGroupAlgebra C G) where
  continuous_add := continuous_add
  continuous_neg := continuous_neg

/-- Multiplication on the pro-`C` completed group algebra is continuous. -/
instance instContinuousMulZCCompletedGroupAlgebra :
    ContinuousMul (ZCCompletedGroupAlgebra C G) where
  continuous_mul := by
    have hval : Continuous (fun p : ZCCompletedGroupAlgebra C G ×
        ZCCompletedGroupAlgebra C G =>
        ((p.1 * p.2 : ZCCompletedGroupAlgebra C G) :
          (i : ZCCompletedGroupAlgebraIndex C G) → ZCCompletedGroupAlgebraStage C G i)) := by
      exact continuous_pi fun i =>
        (continuous_of_discreteTopology :
          Continuous (fun q : ZCCompletedGroupAlgebraStage C G i ×
              ZCCompletedGroupAlgebraStage C G i => q.1 * q.2)).comp
            (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).prodMk
              ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
    simpa [Subtype.eta] using
      (Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible C G) hval
        (fun p => (p.1 * p.2 : ZCCompletedGroupAlgebra C G).property))

/-- The completed group algebra is a topological ring in its inverse-limit topology. -/
instance instIsTopologicalRingZCCompletedGroupAlgebra :
    IsTopologicalRing (ZCCompletedGroupAlgebra C G) where
  continuous_add := continuous_add
  continuous_mul := continuous_mul
  continuous_neg := continuous_neg

/-- Scalar multiplication of `Z_C[[G]]` on itself is continuous. -/
instance instContinuousSMulZCCompletedGroupAlgebraSelf :
    ContinuousSMul (ZCCompletedGroupAlgebra C G) (ZCCompletedGroupAlgebra C G) :=
  ContinuousMul.to_continuousSMul

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- The scalar action map on the completed group algebra is continuous. -/
theorem continuous_zcCompletedGroupAlgebra_smul :
    Continuous (fun p : ZCCompletedGroupAlgebra C G × ZCCompletedGroupAlgebra C G =>
      p.1 • p.2) :=
  continuous_smul

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- The completed group-like map `G -> Z_C[[G]]` is continuous. -/
theorem continuous_zcGroupLike : Continuous (zcGroupLike C G) := by
  have hval : Continuous (fun g : G =>
      ((zcGroupLike C G g : ZCCompletedGroupAlgebra C G) :
        (i : ZCCompletedGroupAlgebraIndex C G) → ZCCompletedGroupAlgebraStage C G i)) := by
    refine continuous_pi fun i => ?_
    letI : DiscreteTopology (CompletedGroupAlgebraQuotientInClass G C i.2) :=
      QuotientGroup.discreteTopology
        (ProCGroups.openNormalSubgroup_isOpen (G := G)
          ((OrderDual.ofDual i.2).1 : OpenNormalSubgroup G))
    exact (continuous_of_discreteTopology :
        Continuous (fun q : CompletedGroupAlgebraQuotientInClass G C i.2 =>
          MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass G C i.2) q)).comp
      (continuous_quotient_mk' : Continuous (fun g : G =>
        QuotientGroup.mk' (((OrderDual.ofDual i.2).1 : OpenNormalSubgroup G) : Subgroup G) g))
  simpa [Subtype.eta] using
    (Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible C G) hval
      (fun g => (zcGroupLike C G g : ZCCompletedGroupAlgebra C G).property))

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- The completed augmentation `Z_C[[G]] -> Z_C` is continuous in the inverse-limit topology. -/
theorem continuous_zcCompletedGroupAlgebraAugmentation
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Continuous (zcCompletedGroupAlgebraAugmentation C G) := by
  have hval : Continuous (fun x : ZCCompletedGroupAlgebra C G =>
      (zcCompletedGroupAlgebraAugmentation C G x :
        (i : ProCIntegerIndex C) → ProCIntegerStage C i)) := by
    refine continuous_pi fun i => ?_
    letI : Fact (0 < i.modulus) := ⟨i.positive⟩
    let U := zcCompletedGroupAlgebraTopIndex C G
    letI : TopologicalSpace (ModNCompletedGroupAlgebraStageInClass i.modulus G C U) := ⊥
    letI : DiscreteTopology (ModNCompletedGroupAlgebraStageInClass i.modulus G C U) := ⟨rfl⟩
    exact
      (continuous_of_discreteTopology :
        Continuous (modNCompletedGroupAlgebraStageAugmentationInClass i.modulus G C U)).comp
        ((continuous_apply (i, U)).comp continuous_subtype_val)
  simpa [zcCompletedGroupAlgebraAugmentation, Subtype.eta] using
    (Continuous.subtype_mk (p := ProCIntegerCompatible C) hval
      (fun x => (zcCompletedGroupAlgebraAugmentation C G x).property))

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- The completed augmentation ideal is closed in `Z_C[[G]]`. -/
theorem isClosed_zcCompletedGroupAlgebraAugmentationIdeal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    IsClosed
      ((zcCompletedGroupAlgebraAugmentationIdeal C G :
        Ideal (ZCCompletedGroupAlgebra C G)) : Set (ZCCompletedGroupAlgebra C G)) := by
  change IsClosed ((zcCompletedGroupAlgebraAugmentation C G) ⁻¹' ({0} : Set (ZCCoeff C)))
  exact isClosed_singleton.preimage
    (continuous_zcCompletedGroupAlgebraAugmentation (C := C) (G := G))

/-- The completed augmentation ideal is compact as a closed subspace of `Z_C[[G]]`. -/
instance instCompactSpaceZCCompletedGroupAlgebraAugmentationIdeal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    CompactSpace (ZCCompletedGroupAlgebraAugmentationIdeal C G) := by
  exact
    (isClosed_zcCompletedGroupAlgebraAugmentationIdeal
      (C := C) (G := G)).isClosedEmbedding_subtypeVal.compactSpace

/-- The completed augmentation ideal is Hausdorff. -/
instance instT2SpaceZCCompletedGroupAlgebraAugmentationIdeal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    T2Space (ZCCompletedGroupAlgebraAugmentationIdeal C G) :=
  inferInstance

variable {A : Type v} [Group A] [TopologicalSpace A]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- The completed group-algebra boundary `a ↦ [ψ a] - 1` is continuous whenever `ψ` is
continuous. -/
theorem continuous_zcCompletedGroupAlgebraBoundary
    (ψ : A →* G) (hψ : Continuous ψ) :
    Continuous (zcCompletedGroupAlgebraBoundary C ψ) := by
  simpa [zcCompletedGroupAlgebraBoundary] using
    ((continuous_zcGroupLike (C := C) (G := G)).comp hψ).sub continuous_const

variable {X : Type v} [Fintype X] [DecidableEq X]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] in
/-- The completed `Z_C[[G]]` Fox boundary/Euler map is continuous. -/
theorem continuous_zcFreeGroupFoxBoundary (ψ : FreeGroup X →* G) :
    Continuous (zcFreeGroupFoxBoundary C ψ) := by
  classical
  rw [zcFreeGroupFoxBoundary_eq_foxBoundaryMap]
  exact continuous_foxBoundaryMap _

end CompletedGroupAlgebraTopology

section CompletedSourceBoundary

variable (C : ProCGroups.FiniteGroupClass.{u})
variable [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
variable {X H : Type u} [Fintype X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Source-shaped completed Fox boundary map for a finite generating set.  It evaluates a vector
of completed Fox coefficients against the generator boundaries `[φ x] - 1`. -/
def freeProCZCCompletedFoxBoundary (φ : X → H) :
    ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebra C H :=
  foxBoundaryMap (fun x : X => zcGroupLike C H (φ x) - 1)


omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- The source-shaped completed Fox boundary map is the expected finite Euler sum. -/
theorem freeProCZCCompletedFoxBoundary_apply
    (φ : X → H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    freeProCZCCompletedFoxBoundary C φ v =
      ∑ x : X, v x * (zcGroupLike C H (φ x) - 1) :=
  rfl

variable [DecidableEq X]


omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- The source-shaped completed Fox boundary map sends the standard basis vector at `x` to
`[φ x] - 1`. -/
@[simp]
theorem freeProCZCCompletedFoxBoundary_single
    (φ : X → H) (x : X) :
    freeProCZCCompletedFoxBoundary C φ
        (Pi.single x (1 : ZCCompletedGroupAlgebra C H)) =
      zcGroupLike C H (φ x) - 1 := by
  simp only [freeProCZCCompletedFoxBoundary, foxBoundaryMap_single]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] in
/-- The source-shaped completed Fox boundary map is continuous for finite generating sets. -/
theorem continuous_freeProCZCCompletedFoxBoundary (φ : X → H) :
    Continuous (freeProCZCCompletedFoxBoundary C φ) :=
  continuous_foxBoundaryMap _

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- The source-shaped completed Fox boundary has image equal to the submodule generated by the
augmentation generators `[φ x] - 1`. -/
theorem freeProCZCCompletedFoxBoundary_range
    (φ : X → H) :
    (freeProCZCCompletedFoxBoundary C φ).range =
      Submodule.span (ZCCompletedGroupAlgebra C H)
        (Set.range fun x : X => zcGroupLike C H (φ x) - 1) := by
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    rw [freeProCZCCompletedFoxBoundary_apply]
    exact Submodule.sum_mem _ fun x _ =>
      Submodule.smul_mem _ (v x)
        (Submodule.subset_span (Set.mem_range_self x))
  · refine Submodule.span_le.2 ?_
    rintro y ⟨x, rfl⟩
    exact ⟨Pi.single x (1 : ZCCompletedGroupAlgebra C H), by simp only [freeProCZCCompletedFoxBoundary_single]⟩

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- If the chosen finite source hits every element of `H`, the source-shaped completed Fox
boundary has image equal to the algebraic standard-generator ideal. -/
theorem freeProCZCCompletedFoxBoundary_range_eq_standardAugmentationIdeal_of_surjective
    (φ : X → H) (hφ : Function.Surjective φ) :
    (freeProCZCCompletedFoxBoundary C φ).range =
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C H :
        Submodule (ZCCompletedGroupAlgebra C H) (ZCCompletedGroupAlgebra C H)) := by
  rw [freeProCZCCompletedFoxBoundary_range,
    zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨φ x, rfl⟩
  · rintro ⟨h, rfl⟩
    rcases hφ h with ⟨x, rfl⟩
    exact ⟨x, rfl⟩

end CompletedSourceBoundary

section SemidirectTopology

variable (C : ProCGroups.FiniteGroupClass.{v})
variable [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
variable (X : Type u) [DecidableEq X]
variable (H : Type v) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The standard topology on `Z_C[[H]]^X ⋊ H`, induced from the product of coordinates and `H`.
-/
instance instTopologicalSpaceZCCompletedFoxSemidirect :
    TopologicalSpace (ZCCompletedFoxSemidirect C X H) :=
  TopologicalSpace.induced
    (fun a : ZCCompletedFoxSemidirect C X H => (a.left, a.right)) inferInstance

/-- The completed Fox semidirect target is homeomorphic to its product of components. -/
def zcCompletedFoxSemidirectHomeomorphProd :
    ZCCompletedFoxSemidirect C X H ≃ₜ (ZCFreeFoxCoordinates C (X := X) (H := H) × H) where
  toEquiv :=
    { toFun := fun a => (a.left, a.right)
      invFun := fun p => { left := p.1, right := p.2 }
      left_inv := by
        intro a
        cases a
        rfl
      right_inv := by
        intro p
        cases p
        rfl }
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact continuous_id

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] in
/-- The component-pair map from the semidirect target is continuous. -/
theorem continuous_zcCompletedFoxSemidirect_toProd :
    Continuous (fun a : ZCCompletedFoxSemidirect C X H => (a.left, a.right)) :=
  continuous_induced_dom

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] in
/-- The Fox-coordinate projection from the semidirect target is continuous. -/
theorem continuous_zcCompletedFoxSemidirect_left :
    Continuous (fun a : ZCCompletedFoxSemidirect C X H => a.left) :=
  continuous_fst.comp (continuous_zcCompletedFoxSemidirect_toProd C X H)

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] in
/-- The group projection from the semidirect target is continuous. -/
theorem continuous_zcCompletedFoxSemidirect_right :
    Continuous (fun a : ZCCompletedFoxSemidirect C X H => a.right) :=
  continuous_snd.comp (continuous_zcCompletedFoxSemidirect_toProd C X H)

/-- Compactness of the completed Fox semidirect target when the group component is compact. -/
instance instCompactSpaceZCCompletedFoxSemidirect [CompactSpace H] :
    CompactSpace (ZCCompletedFoxSemidirect C X H) := by
  exact (zcCompletedFoxSemidirectHomeomorphProd C X H).symm.compactSpace

/-- Hausdorffness of the completed Fox semidirect target when the group component is Hausdorff. -/
instance instT2SpaceZCCompletedFoxSemidirect [T2Space H] :
    T2Space (ZCCompletedFoxSemidirect C X H) := by
  exact (zcCompletedFoxSemidirectHomeomorphProd C X H).symm.t2Space

/-- Total disconnectedness of the completed Fox semidirect target when the group component is
totally disconnected. -/
instance instTotallyDisconnectedSpaceZCCompletedFoxSemidirect [TotallyDisconnectedSpace H] :
    TotallyDisconnectedSpace (ZCCompletedFoxSemidirect C X H) := by
  exact (zcCompletedFoxSemidirectHomeomorphProd C X H).symm.totallyDisconnectedSpace

/-- The completed Fox semidirect target is a topological group with its standard product
topology. -/
instance instIsTopologicalGroupZCCompletedFoxSemidirect :
    IsTopologicalGroup (ZCCompletedFoxSemidirect C X H) where
  continuous_mul := by
    letI : ContinuousMul H := (inferInstanceAs (IsTopologicalGroup H)).toContinuousMul
    rw [continuous_induced_rng]
    have hleft : Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
        ZCCompletedFoxSemidirect C X H => (p.1 * p.2).left) := by
      refine continuous_pi fun x => ?_
      have hleftA : Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
          ZCCompletedFoxSemidirect C X H => p.1.left x) :=
        (continuous_apply x).comp
          ((continuous_zcCompletedFoxSemidirect_left C X H).comp continuous_fst)
      have hrightA : Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
          ZCCompletedFoxSemidirect C X H => p.2.left x) :=
        (continuous_apply x).comp
          ((continuous_zcCompletedFoxSemidirect_left C X H).comp continuous_snd)
      have hgroup : Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
          ZCCompletedFoxSemidirect C X H => zcGroupLike C H p.1.right) :=
        (continuous_zcGroupLike (C := C) (G := H)).comp
          ((continuous_zcCompletedFoxSemidirect_right C X H).comp continuous_fst)
      change Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
          ZCCompletedFoxSemidirect C X H =>
        p.1.left x + zcGroupLike C H p.1.right * p.2.left x)
      exact hleftA.add (hgroup.mul hrightA)
    have hright : Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
        ZCCompletedFoxSemidirect C X H => (p.1 * p.2).right) := by
      exact ((continuous_zcCompletedFoxSemidirect_right C X H).comp continuous_fst).mul
        ((continuous_zcCompletedFoxSemidirect_right C X H).comp continuous_snd)
    exact hleft.prodMk hright
  continuous_inv := by
    letI : ContinuousInv H := (inferInstanceAs (IsTopologicalGroup H)).toContinuousInv
    rw [continuous_induced_rng]
    have hleft : Continuous (fun a : ZCCompletedFoxSemidirect C X H => a⁻¹.left) := by
      refine continuous_pi fun x => ?_
      have hleftA : Continuous (fun a : ZCCompletedFoxSemidirect C X H => a.left x) :=
        (continuous_apply x).comp (continuous_zcCompletedFoxSemidirect_left C X H)
      have hgroup : Continuous (fun a : ZCCompletedFoxSemidirect C X H =>
          zcGroupLike C H a.right⁻¹) :=
        (continuous_zcGroupLike (C := C) (G := H)).comp
          ((continuous_zcCompletedFoxSemidirect_right C X H).inv)
      change Continuous (fun a : ZCCompletedFoxSemidirect C X H =>
        -(zcGroupLike C H a.right⁻¹ * a.left x))
      exact (hgroup.mul hleftA).neg
    have hright : Continuous (fun a : ZCCompletedFoxSemidirect C X H => a⁻¹.right) := by
      exact (continuous_zcCompletedFoxSemidirect_right C X H).inv
    exact hleft.prodMk hright

omit [DecidableEq X] in
/-- The completed Fox semidirect target is profinite when the group component is profinite. -/
theorem isProfiniteGroup_zcCompletedFoxSemidirect
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] :
    ProCGroups.IsProfiniteGroup (ZCCompletedFoxSemidirect C X H) := by
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- The completed Fox semidirect target is an all-finite pro-`C` group when the group component is
profinite. -/
instance instAllFiniteProCGroupZCCompletedFoxSemidirect
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] :
    ProCGroups.ProC.ProCGroup ProCGroups.ProC.allFiniteProC
      (ZCCompletedFoxSemidirect C X H) :=
  ProCGroups.ProC.allFiniteProCGroup_of_profinite
    (isProfiniteGroup_zcCompletedFoxSemidirect C X H)

omit [DecidableEq X] in
/-- The completed Fox semidirect target is an all-finite pro-`C` group when the group component is
profinite.  This theorem form is convenient when an explicit target proof is needed. -/
theorem allFiniteProC_zcCompletedFoxSemidirect
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] :
    ProCGroups.ProC.allFiniteProC (G := ZCCompletedFoxSemidirect C X H) :=
  (inferInstanceAs
    (ProCGroups.ProC.ProCGroup ProCGroups.ProC.allFiniteProC
      (ZCCompletedFoxSemidirect C X H))).isProC

end SemidirectTopology

section CompletedGroupAlgebraProC

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- One finite stage `(Z/nZ)[H/U]`, written multiplicatively from its additive group, belongs
to `C`.  The proof identifies it with the finite product of the allowed cyclic coefficient group
over the finite quotient `H/U`. -/
theorem finiteGroupClass_multiplicative_modNCompletedGroupAlgebraStageInClass_mem
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hProd : ProCGroups.FiniteGroupClass.FiniteProductClosed C)
    (i : ProCIntegerIndex C) (U : CompletedGroupAlgebraIndexInClass H C) :
    C (Multiplicative (ModNCompletedGroupAlgebraStageInClass i.modulus H C U)) := by
  classical
  letI : Fact (0 < i.modulus) := ⟨i.positive⟩
  let Q := CompletedGroupAlgebraQuotientInClass H C U
  letI : Finite Q := ProCGroups.FiniteGroupClass.finite (C := C) (OrderDual.ofDual U).2
  letI : Fintype Q := Fintype.ofFinite Q
  let e :
      Multiplicative (ModNCompletedGroupAlgebraStageInClass i.modulus H C U) ≃*
        (Q → ULift.{u} (Multiplicative (ModNCompletedCoeff i.modulus))) :=
    { toFun := fun a q =>
        ULift.up (Multiplicative.ofAdd ((Finsupp.equivFunOnFinite a.toAdd) q))
      invFun := fun f =>
        Multiplicative.ofAdd
          (Finsupp.equivFunOnFinite.symm fun q => (f q).down.toAdd)
      left_inv := by
        intro a
        apply Multiplicative.ext
        exact Finsupp.equivFunOnFinite.left_inv a.toAdd
      right_inv := by
        intro f
        funext q
        have hcoeff :
            (Finsupp.equivFunOnFinite
              (Finsupp.equivFunOnFinite.symm fun q => (f q).down.toAdd)) q =
              (f q).down.toAdd := by
          exact congrFun
            (Finsupp.equivFunOnFinite.right_inv
              (fun q => (f q).down.toAdd)) q
        apply ULift.ext
        apply Multiplicative.ext
        exact hcoeff
      map_mul' := by
        intro a b
        funext q
        apply ULift.ext
        apply Multiplicative.ext
        rfl }
  have hPi :
      C (Q → ULift.{u} (Multiplicative (ModNCompletedCoeff i.modulus))) := by
    exact hProd (ι := Q)
      (G := fun _ => ULift.{u} (Multiplicative (ModNCompletedCoeff i.modulus)))
      (fun _ => by
        simpa [ModNCompletedCoeff, ProCIntegerStage] using i.cyclic_mem)
  exact hIso ⟨e.symm⟩ hPi

/-- The group-valued inverse system underlying the additive group of `Z_C[[H]]`, written
multiplicatively. -/
def zcCompletedGroupAlgebraMultiplicativeSystem :
    ProCGroups.InverseSystems.InverseSystem (I := ZCCompletedGroupAlgebraIndex C H) where
  X := fun i => Multiplicative (ZCCompletedGroupAlgebraStage C H i)
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    (zcCompletedGroupAlgebraTransition C H hij).toAddMonoidHom.toMultiplicative
  continuous_map := by
    intro i j hij
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    apply Multiplicative.ext
    change zcCompletedGroupAlgebraTransition C H (le_rfl : i ≤ i) x.toAdd = x.toAdd
    simp only [zcCompletedGroupAlgebraTransition_id, RingHom.id_apply]
  map_comp := by
    intro i j k hij hjk
    funext x
    apply Multiplicative.ext
    change
      zcCompletedGroupAlgebraTransition C H hij
          (zcCompletedGroupAlgebraTransition C H hjk x.toAdd) =
        zcCompletedGroupAlgebraTransition C H (hij.trans hjk) x.toAdd
    exact congrArg (fun f : ZCCompletedGroupAlgebraStage C H k →+*
        ZCCompletedGroupAlgebraStage C H i => f x.toAdd)
      (zcCompletedGroupAlgebraTransition_comp C H hij hjk)

instance instGroupZCCompletedGroupAlgebraMultiplicativeSystemStage
    (i : ZCCompletedGroupAlgebraIndex C H) :
    Group ((zcCompletedGroupAlgebraMultiplicativeSystem C H).X i) := by
  dsimp [zcCompletedGroupAlgebraMultiplicativeSystem]
  infer_instance

instance instIsTopologicalGroupZCCompletedGroupAlgebraMultiplicativeSystemStage
    (i : ZCCompletedGroupAlgebraIndex C H) :
    IsTopologicalGroup ((zcCompletedGroupAlgebraMultiplicativeSystem C H).X i) := by
  dsimp [zcCompletedGroupAlgebraMultiplicativeSystem]
  infer_instance

/-- The multiplicative additive stages of `Z_C[[H]]` form a group-valued inverse system. -/
instance instIsGroupSystemZCCompletedGroupAlgebraMultiplicativeSystem :
    ProCGroups.InverseSystems.IsGroupSystem
      (zcCompletedGroupAlgebraMultiplicativeSystem C H) where
  map_one := by
    intro i j hij
    simp only [zcCompletedGroupAlgebraMultiplicativeSystem, RingHom.toAddMonoidHom_eq_coe,
  AddMonoidHom.coe_toMultiplicative, AddMonoidHom.coe_coe, Function.comp_apply, toAdd_one, map_zero, ofAdd_zero]
  map_mul := by
    intro i j hij x y
    simp only [zcCompletedGroupAlgebraMultiplicativeSystem, RingHom.toAddMonoidHom_eq_coe,
  AddMonoidHom.coe_toMultiplicative, AddMonoidHom.coe_coe, Function.comp_apply, toAdd_mul, map_add, ofAdd_add]
  map_inv := by
    intro i j hij x
    simp only [zcCompletedGroupAlgebraMultiplicativeSystem, RingHom.toAddMonoidHom_eq_coe,
  AddMonoidHom.coe_toMultiplicative, AddMonoidHom.coe_coe, Function.comp_apply, toAdd_inv, map_neg, ofAdd_neg]

/-- The multiplicative inverse limit of the finite completed group-algebra stages is the
additive group underlying `Z_C[[H]]`, written multiplicatively. -/
def zcCompletedGroupAlgebraMultiplicativeLimitEquiv :
    (zcCompletedGroupAlgebraMultiplicativeSystem C H).inverseLimit ≃ₜ*
      Multiplicative (ZCCompletedGroupAlgebra C H) := by
  let S := zcCompletedGroupAlgebraMultiplicativeSystem C H
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C H, Group (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraMultiplicativeSystem]
    infer_instance
  letI : ProCGroups.InverseSystems.IsGroupSystem S := by
    dsimp [S]
    infer_instance
  refine
    { toMulEquiv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · refine
      { toFun := fun x =>
          Multiplicative.ofAdd
            (⟨fun i => (S.projection i x).toAdd, by
              intro i j hij
              exact congrArg Multiplicative.toAdd (S.projection_compatible x i j hij)⟩ :
              ZCCompletedGroupAlgebra C H)
        invFun := fun x =>
          (⟨fun i =>
              Multiplicative.ofAdd
                (zcCompletedGroupAlgebraProjection C H i x.toAdd), by
            intro i j hij
            apply Multiplicative.ext
            exact x.toAdd.2 i j hij⟩ :
            S.inverseLimit)
        left_inv := by
          intro x
          apply S.ext
          intro i
          rfl
        right_inv := by
          intro x
          apply Multiplicative.ext
          ext i
          rfl
        map_mul' := by
          intro x y
          apply Multiplicative.ext
          ext i
          rfl }
  · refine continuous_ofAdd.comp ?_
    have hambient : Continuous fun x : S.inverseLimit =>
        (fun i : ZCCompletedGroupAlgebraIndex C H => (S.projection i x).toAdd :
          ∀ i : ZCCompletedGroupAlgebraIndex C H, ZCCompletedGroupAlgebraStage C H i) := by
      exact continuous_pi fun i => continuous_toAdd.comp (S.continuous_projection i)
    exact Continuous.subtype_mk hambient (fun x => by
      intro i j hij
      exact congrArg Multiplicative.toAdd (S.projection_compatible x i j hij))
  · have hambient : Continuous fun x : Multiplicative (ZCCompletedGroupAlgebra C H) =>
        (fun i : ZCCompletedGroupAlgebraIndex C H =>
          Multiplicative.ofAdd (zcCompletedGroupAlgebraProjection C H i x.toAdd) :
          ∀ i : ZCCompletedGroupAlgebraIndex C H, S.X i) := by
      exact continuous_pi fun i =>
        continuous_ofAdd.comp
          ((continuous_apply i).comp (continuous_subtype_val.comp continuous_toAdd))
    exact Continuous.subtype_mk hambient (fun x => by
      intro i j hij
      apply Multiplicative.ext
      exact x.toAdd.2 i j hij)

omit [IsTopologicalGroup H] in
/-- The two-parameter completed group-algebra index is directed when `C` is a formation. -/
theorem directed_zcCompletedGroupAlgebraIndex_of_formation
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    Directed (· ≤ ·)
      (id : ZCCompletedGroupAlgebraIndex C H → ZCCompletedGroupAlgebraIndex C H) := by
  intro i j
  rcases ProCIntegerIndex.directed_of_formation (C := C) hForm i.1 j.1 with
    ⟨kcoeff, hki_coeff, hkj_coeff⟩
  rcases ProCGroups.ProC.directed_openNormalSubgroupInClass
      (C := C) (G := H) hForm i.2 j.2 with
    ⟨kquot, hki_quot, hkj_quot⟩
  exact ⟨(kcoeff, kquot), ⟨hki_coeff, hki_quot⟩, ⟨hkj_coeff, hkj_quot⟩⟩

/-- The additive group underlying `Z_C[[H]]`, written multiplicatively, is pro-`C`. -/
theorem isProCGroup_multiplicative_zcCompletedGroupAlgebra
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    ProCGroups.ProC.IsProCGroup C (Multiplicative (ZCCompletedGroupAlgebra C H)) := by
  letI : Fact (ProCGroups.FiniteGroupClass.FiniteOnly C) :=
    ⟨ProCGroups.FiniteGroupClass.finiteOnly C⟩
  letI : ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C :=
    hForm.containsTrivialQuotients
  letI : Nonempty (ProCIntegerIndex C) :=
    ⟨ProCIntegerIndex.terminal hForm.containsTrivialQuotients⟩
  letI : Nonempty (CompletedGroupAlgebraIndexInClass H C) :=
    ⟨_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndexInClass (G := H) C⟩
  letI : Nonempty (ZCCompletedGroupAlgebraIndex C H) := inferInstance
  let S := zcCompletedGroupAlgebraMultiplicativeSystem C H
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C H, Group (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraMultiplicativeSystem]
    infer_instance
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C H, IsTopologicalGroup (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraMultiplicativeSystem]
    infer_instance
  letI : ProCGroups.InverseSystems.IsGroupSystem S := by
    dsimp [S]
    infer_instance
  have hS : ProCGroups.ProC.IsProCGroup C S.inverseLimit := by
    exact ProCGroups.ProC.inverseLimit (S := S)
      hForm.isomClosed hForm.quotientClosed
      (directed_zcCompletedGroupAlgebraIndex_of_formation C H hForm)
      (fun i => by
        dsimp [S, zcCompletedGroupAlgebraMultiplicativeSystem]
        letI : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
        letI : Finite (ZCCompletedGroupAlgebraStage C H i) :=
          finite_modNCompletedGroupAlgebraStageInClass
            (n := i.1.modulus) (G := H) C
            (ProCGroups.FiniteGroupClass.finiteOnly C) i.2
        letI : Finite (Multiplicative (ZCCompletedGroupAlgebraStage C H i)) :=
          @Finite.of_equiv _ _ (inferInstance : Finite (ZCCompletedGroupAlgebraStage C H i))
            Multiplicative.toAdd
        letI : DiscreteTopology (Multiplicative (ZCCompletedGroupAlgebraStage C H i)) := ⟨rfl⟩
        exact ProCGroups.ProC.IsProCGroup.of_finite_discrete (C := C)
          (G := Multiplicative (ZCCompletedGroupAlgebraStage C H i))
          hForm.quotientClosed
          (finiteGroupClass_multiplicative_modNCompletedGroupAlgebraStageInClass_mem
            C H hForm.isomClosed hForm.finiteProductClosed i.1 i.2))
  exact ProCGroups.ProC.IsProCGroup.ofContinuousMulEquiv (C := C)
    hForm.isomClosed hForm.quotientClosed hS
    (zcCompletedGroupAlgebraMultiplicativeLimitEquiv C H)

variable (X : Type u)

/-- Coordinatewise, the multiplicative version of an additive function group is the product of
the multiplicative coordinate groups. -/
def multiplicativePiContinuousMulEquiv
    (A : Type u) [AddCommGroup A] [TopologicalSpace A] :
    Multiplicative (X → A) ≃ₜ* (X → Multiplicative A) where
  toMulEquiv :=
    { toFun := fun f x => Multiplicative.ofAdd (f.toAdd x)
      invFun := fun f => Multiplicative.ofAdd fun x => (f x).toAdd
      left_inv := by
        intro f
        rfl
      right_inv := by
        intro f
        rfl
      map_mul' := by
        intro f g
        rfl }
  continuous_toFun := by
    exact continuous_pi fun x =>
      continuous_ofAdd.comp ((continuous_apply x).comp continuous_toAdd)
  continuous_invFun := by
    exact continuous_ofAdd.comp
      (continuous_pi fun x => continuous_toAdd.comp (continuous_apply x))

/-- The additive Fox-coordinate group `Z_C[[H]]^X`, written multiplicatively, is pro-`C`. -/
theorem isProCGroup_multiplicative_zcFreeFoxCoordinates
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    ProCGroups.ProC.IsProCGroup C
      (Multiplicative (ZCFreeFoxCoordinates C (X := X) (H := H))) := by
  letI : Fact (ProCGroups.FiniteGroupClass.FiniteOnly C) :=
    ⟨ProCGroups.FiniteGroupClass.finiteOnly C⟩
  have hPi :
      ProCGroups.ProC.IsProCGroup C
        (X → Multiplicative (ZCCompletedGroupAlgebra C H)) :=
    ProCGroups.ProC.IsProCGroup.pi
      (C := C) (α := X)
      (β := fun _ => Multiplicative (ZCCompletedGroupAlgebra C H))
      hForm
      (fun _ => isProCGroup_multiplicative_zcCompletedGroupAlgebra
        (C := C) (H := H) hForm)
  exact ProCGroups.ProC.IsProCGroup.ofContinuousMulEquiv (C := C)
    hForm.isomClosed hForm.quotientClosed hPi
    (multiplicativePiContinuousMulEquiv (X := X)
      (A := ZCCompletedGroupAlgebra C H)).symm

end CompletedGroupAlgebraProC

section SemidirectProC

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (X H : Type u) [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The kernel of the right projection `Z_C[[H]]^X ⋊ H -> H` is the additive coordinate group,
written multiplicatively. -/
def zcCompletedFoxSemidirectRightKernelEquivCoordinates :
    ((ZCCompletedFoxSemidirect.rightMonoidHom C X H).ker :
        Subgroup (ZCCompletedFoxSemidirect C X H)) ≃ₜ*
      Multiplicative (ZCFreeFoxCoordinates C (X := X) (H := H)) where
  toMulEquiv :=
    { toFun := fun a => Multiplicative.ofAdd a.1.left
      invFun := fun v =>
        ⟨{ left := v.toAdd, right := 1 }, by
          simp only [ZCCompletedFoxSemidirect.rightMonoidHom, MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk]⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply ZCCompletedFoxSemidirect.ext
        · rfl
        · change (1 : H) = a.1.right
          exact a.2.symm
      right_inv := by
        intro v
        rfl
      map_mul' := by
        intro a b
        apply Multiplicative.ext
        have ha : a.1.right = 1 := by
          exact a.2
        simp only [Subgroup.coe_mul, ZCCompletedFoxSemidirect.mul_left, ha, map_one, one_smul, ofAdd_add, toAdd_mul,
  toAdd_ofAdd]}
  continuous_toFun := by
    exact continuous_ofAdd.comp
      ((continuous_zcCompletedFoxSemidirect_left C X H).comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ (fun v => by
      simp only [ZCCompletedFoxSemidirect.rightMonoidHom, MonoidHom.mem_ker, MonoidHom.coe_mk, OneHom.coe_mk])
    rw [continuous_induced_rng]
    exact continuous_toAdd.prodMk continuous_const

omit [DecidableEq X] in
/-- The right-projection kernel in the completed Fox semidirect product is pro-`C`. -/
theorem isProCGroup_zcCompletedFoxSemidirect_rightKernel
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    ProCGroups.ProC.IsProCGroup C
      ((ZCCompletedFoxSemidirect.rightMonoidHom C X H).ker :
        Subgroup (ZCCompletedFoxSemidirect C X H)) := by
  letI : Fact (ProCGroups.FiniteGroupClass.FiniteOnly C) :=
    ⟨ProCGroups.FiniteGroupClass.finiteOnly C⟩
  have hcoords :
      ProCGroups.ProC.IsProCGroup C
        (Multiplicative (ZCFreeFoxCoordinates C (X := X) (H := H))) :=
    isProCGroup_multiplicative_zcFreeFoxCoordinates (C := C) (X := X) (H := H) hForm
  exact ProCGroups.ProC.IsProCGroup.ofContinuousMulEquiv (C := C)
    hForm.isomClosed hForm.quotientClosed hcoords
    (zcCompletedFoxSemidirectRightKernelEquivCoordinates C X H).symm

omit [DecidableEq X] in
/-- The completed Fox semidirect target `Z_C[[H]]^X ⋊ H` is pro-`C` when `H` is pro-`C`. -/
theorem isProCGroup_zcCompletedFoxSemidirect_of_isProCGroup
    (hMel : ProCGroups.FiniteGroupClass.MelnikovFormation C)
    (hH : ProCGroups.ProC.IsProCGroup C H) :
    ProCGroups.ProC.IsProCGroup C (ZCCompletedFoxSemidirect C X H) := by
  letI : Fact (ProCGroups.FiniteGroupClass.FiniteOnly C) :=
    ⟨ProCGroups.FiniteGroupClass.finiteOnly C⟩
  letI : CompactSpace H := ProCGroups.ProC.IsProCGroup.compactSpace hH
  letI : T2Space H := ProCGroups.ProC.IsProCGroup.t2Space hH
  letI : TotallyDisconnectedSpace H :=
    ProCGroups.ProC.IsProCGroup.totallyDisconnectedSpace hH
  let E := ZCCompletedFoxSemidirect C X H
  let f : E →ₜ* H :=
    { toMonoidHom := ZCCompletedFoxSemidirect.rightMonoidHom C X H
      continuous_toFun := continuous_zcCompletedFoxSemidirect_right C X H }
  let K : Subgroup E := f.toMonoidHom.ker
  have hE : ProCGroups.IsProfiniteGroup E :=
    isProfiniteGroup_zcCompletedFoxSemidirect C X H
  have hK : ProCGroups.ProC.IsProCGroup C K := by
    dsimp [K, f, E]
    exact isProCGroup_zcCompletedFoxSemidirect_rightKernel
      (C := C) (X := X) (H := H) hMel.formation
  have hQ : ProCGroups.ProC.IsProCGroup C (E ⧸ K) := by
    letI : CompactSpace E := ProCGroups.IsProfiniteGroup.compactSpace hE
    letI : T2Space E := ProCGroups.IsProfiniteGroup.t2Space hE
    have hf_surj : Function.Surjective f := by
      intro h
      exact ⟨{ left := 0, right := h }, rfl⟩
    let eQuotRange : (E ⧸ K) ≃ₜ* f.toMonoidHom.range := by
      simpa [K] using ContinuousMonoidHom.quotientKerContinuousMulEquivRange f
    let eRangeH : f.toMonoidHom.range ≃ₜ* H :=
      { toMulEquiv :=
          { toFun := fun x => x.1
            invFun := fun h => ⟨h, hf_surj h⟩
            left_inv := by
              intro x
              exact Subtype.ext rfl
            right_inv := by
              intro h
              rfl
            map_mul' := by
              intro x y
              rfl }
        continuous_toFun := continuous_subtype_val
        continuous_invFun := Continuous.subtype_mk continuous_id (fun h => hf_surj h) }
    exact ProCGroups.ProC.IsProCGroup.ofContinuousMulEquiv (C := C)
      hMel.formation.isomClosed hMel.formation.quotientClosed hH
      (eRangeH.symm.trans eQuotRange.symm)
  exact ProCGroups.ProC.IsProCGroup.extension (C := C)
    hMel.formation.isomClosed hMel.formation.quotientClosed hMel.extensionClosed
    hE K hK hQ

omit [DecidableEq X] in
/-- Bundled `ProCGroup` form for the completed Fox semidirect target. -/
theorem proCGroup_zcCompletedFoxSemidirect
    (ProC : ProCGroups.ProC.ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.DeterminedByFiniteQuotients]
    [ProCGroups.ProC.ProCGroup ProC H] :
    ProCGroups.ProC.ProCGroup ProC
      (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :=
  ProCGroups.ProC.ProCGroup.of_isProCGroup ProC
    (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (isProCGroup_zcCompletedFoxSemidirect_of_isProCGroup
      (C := ProC.finiteQuotientClass) (X := X) (H := H)
      ProC.finiteQuotientMelnikovFormation
      (inferInstanceAs (ProCGroups.ProC.ProCGroup ProC H)).isProCGroup)

end SemidirectProC

section ClosedGeneratedSemidirectTopology

variable (X H : Type u) [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The closed target generated by the Fox graph generators is an all-finite pro-`C` group when
the ambient completed Fox semidirect target is profinite. -/
theorem allFiniteProC_freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H] (φ : X → H) :
    ProCGroups.ProC.allFiniteProC
      (G :=
        (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
          (ProC := ProCGroups.ProC.allFiniteProC) φ : Subgroup
            (ZCCompletedFoxSemidirect
              ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H))) := by
  exact (ProCGroups.ProC.allFiniteProCGroup_of_profinite
    (ProCGroups.IsProfiniteGroup.of_closedSubgroup
      (G := ZCCompletedFoxSemidirect
        ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
      (isProfiniteGroup_zcCompletedFoxSemidirect
        ProCGroups.ProC.allFiniteProC.finiteQuotientClass X H)
      (freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProCGroups.ProC.allFiniteProC) φ))).isProC

end ClosedGeneratedSemidirectTopology

end

end FoxDifferential
