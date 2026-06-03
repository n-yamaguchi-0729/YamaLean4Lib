import FenchelNielsenZomorrodian.Discrete.Core.Signature
import Mathlib.GroupTheory.Solvable
import ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients
import ProCGroups.Presentations.SchreierTietze.Restricted

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Profinite/FGroup.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite Fenchel groups

Defines profinite Fenchel signatures, generators, inertia, presentations, derived-series notation, torsion-free open subgroups, and quotient-derived-length predicates.
-/

namespace FenchelNielsen

universe u v

open scoped BigOperators
open ProCGroups.FiniteStepSolvableQuotients
open ProCGroups.ProC

namespace ContinuousMonoidHom

variable {F G A : Type u}
variable [Group F] [Group G] [Group A]
variable [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace A]

/-- Descend a continuous homomorphism along a continuous surjection, using a kernel inclusion.

This is the presentation quotient bridge used for profinite `F`-groups: a continuous homomorphism
out of the free profinite source descends to the presented group once it kills the presentation
kernel.
-/
noncomputable def liftOfSurjective
    [CompactSpace F] [T2Space G]
    (π : F →ₜ* G) (hπ : Function.Surjective π)
    (φ : F →ₜ* A) (hker : π.toMonoidHom.ker ≤ φ.toMonoidHom.ker) :
    G →ₜ* A := by
  let ψ : G →* A :=
    (π.toMonoidHom.liftOfSurjective hπ) ⟨φ.toMonoidHom, hker⟩
  have hψcomp : ψ.comp π.toMonoidHom = φ.toMonoidHom := by
    ext x
    simp only [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.liftOfSurjective, MonoidHom.coe_coe,
  MonoidHom.liftOfRightInverse_comp, ψ]
  have hcomp_continuous : Continuous fun x : F => ψ (π x) := by
    convert φ.continuous_toFun using 1
    funext x
    exact MonoidHom.ext_iff.mp hψcomp x
  exact
    { toMonoidHom := ψ
      continuous_toFun :=
        (IsQuotientMap.of_surjective_continuous
          hπ π.continuous_toFun).continuous_iff.2 hcomp_continuous }

@[simp] theorem liftOfSurjective_apply
    [CompactSpace F] [T2Space G]
    (π : F →ₜ* G) (hπ : Function.Surjective π)
    (φ : F →ₜ* A) (hker : π.toMonoidHom.ker ≤ φ.toMonoidHom.ker)
    (x : F) :
    liftOfSurjective π hπ φ hker (π x) = φ x := by
  change
    ((π.toMonoidHom.liftOfSurjective hπ) ⟨φ.toMonoidHom, hker⟩)
        (π.toMonoidHom x) = φ.toMonoidHom x
  exact
    MonoidHom.liftOfRightInverse_comp_apply
      (f := π.toMonoidHom) (f_inv := Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨φ.toMonoidHom, hker⟩ x

@[simp] theorem liftOfSurjective_comp
    [CompactSpace F] [T2Space G]
    (π : F →ₜ* G) (hπ : Function.Surjective π)
    (φ : F →ₜ* A) (hker : π.toMonoidHom.ker ≤ φ.toMonoidHom.ker) :
    (liftOfSurjective π hπ φ hker).toMonoidHom.comp π.toMonoidHom =
      φ.toMonoidHom := by
  ext x
  simp only [ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply,
  liftOfSurjective_apply]

end ContinuousMonoidHom

/-- The closed derived series of a profinite group, starting from the whole group. -/
abbrev profiniteDerivedSeries
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (m : ℕ) : Subgroup G :=
  ProCGroups.FiniteStepSolvableQuotients.topDerivedTop G m

theorem profiniteDerivedSeries_one_eq_bot_of_commGroup
    (G : Type u) [CommGroup G] [TopologicalSpace G] [T1Space G]
    [IsTopologicalGroup G] :
    profiniteDerivedSeries G 1 = ⊥ := by
  change
    (⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆).topologicalClosure =
      (⊥ : Subgroup G)
  have hcomm :
      ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = (⊥ : Subgroup G) := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _hx
    rw [Subgroup.mem_centralizer_iff]
    intro y _hy
    exact mul_comm y x
  rw [hcomm]
  apply le_antisymm
  · exact
      Subgroup.topologicalClosure_minimal
        (s := (⊥ : Subgroup G)) bot_le (by
          change IsClosed ({1} : Set G)
          exact isClosed_singleton)
  · exact bot_le

theorem profiniteDerivedSeries_eq_derivedSeries_of_discrete
    (G : Type u) [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [IsTopologicalGroup G] :
    ∀ m : ℕ, profiniteDerivedSeries G m = derivedSeries G m := by
  intro m
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      change
        (⁅profiniteDerivedSeries G m, profiniteDerivedSeries G m⁆).topologicalClosure =
          derivedSeries G (m + 1)
      rw [ih, derivedSeries_succ]
      apply le_antisymm
      · exact
          Subgroup.topologicalClosure_minimal
            (s := ⁅derivedSeries G m, derivedSeries G m⁆) le_rfl
            (isClosed_discrete _)
      · exact
          Subgroup.le_topologicalClosure
            (s := ⁅derivedSeries G m, derivedSeries G m⁆)

/-- The Fenchel-Nielsen generator set for a profinite `F`-group presentation. -/
def profiniteFenchelGeneratorSet
    {G : Type u} {σ : FenchelSignature}
    (surfaceA surfaceB : Fin σ.orbitGenus → G)
    (cusp : Fin σ.numCusps → G)
    (inertia : Fin σ.numPeriods → G) : Set G :=
  Set.range surfaceA ∪ Set.range surfaceB ∪ Set.range cusp ∪ Set.range inertia

/-- The single Fenchel-Nielsen surface relation `∏[αᵢ, βᵢ] * ∏γⱼ * ∏δₗ = 1`. -/
def profiniteFenchelTotalRelation
    {G : Type u} [Group G] {σ : FenchelSignature}
    (surfaceA surfaceB : Fin σ.orbitGenus → G)
    (cusp : Fin σ.numCusps → G)
    (inertia : Fin σ.numPeriods → G) : G :=
  ((List.finRange σ.orbitGenus).map fun i => ⁅surfaceA i, surfaceB i⁆).prod *
    ((List.finRange σ.numCusps).map fun j => cusp j).prod *
      ((List.finRange σ.numPeriods).map fun k => inertia k).prod

/-- Formal indices for the Fenchel-Nielsen profinite `F`-group generators. -/
inductive ProfiniteFenchelGenerator (σ : FenchelSignature)
  | surfaceA : Fin σ.orbitGenus → ProfiniteFenchelGenerator σ
  | surfaceB : Fin σ.orbitGenus → ProfiniteFenchelGenerator σ
  | cusp : Fin σ.numCusps → ProfiniteFenchelGenerator σ
  | inertia : Fin σ.numPeriods → ProfiniteFenchelGenerator σ

instance instTopologicalSpaceProfiniteFenchelGenerator (σ : FenchelSignature) :
    TopologicalSpace (ProfiniteFenchelGenerator σ) :=
  ⊥

instance instDiscreteTopologyProfiniteFenchelGenerator (σ : FenchelSignature) :
    DiscreteTopology (ProfiniteFenchelGenerator σ) :=
  ⟨rfl⟩

/-- A universe-lifted Fenchel-Nielsen generator index, suitable as a free pro-`C` basis. -/
abbrev ProfiniteFenchelGeneratorIndex (σ : FenchelSignature) : Type v :=
  ULift.{v, 0} (ProfiniteFenchelGenerator σ)

instance instTopologicalSpaceProfiniteFenchelGeneratorIndex (σ : FenchelSignature) :
    TopologicalSpace (ProfiniteFenchelGeneratorIndex.{v} σ) :=
  ⊥

instance instDiscreteTopologyProfiniteFenchelGeneratorIndex (σ : FenchelSignature) :
    DiscreteTopology (ProfiniteFenchelGeneratorIndex.{v} σ) :=
  ⟨rfl⟩

/-- The Fenchel-Nielsen relator set: the total surface relation and all inertia-period relations. -/
def profiniteFenchelRelatorSet
    {F : Type u} [Group F] (σ : FenchelSignature)
    (basis : ProfiniteFenchelGeneratorIndex.{u} σ → F) : Set F :=
  {profiniteFenchelTotalRelation
      (fun i => basis (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
      (fun i => basis (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
      (fun j => basis (ULift.up (ProfiniteFenchelGenerator.cusp j)))
      (fun k => basis (ULift.up (ProfiniteFenchelGenerator.inertia k)))} ∪
    Set.range fun k : Fin σ.numPeriods =>
      basis (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^ σ.periods k

def ProfiniteFenchelGenerator.eval
    {G : Type u} {σ : FenchelSignature}
    (surfaceA surfaceB : Fin σ.orbitGenus → G)
    (cusp : Fin σ.numCusps → G)
    (inertia : Fin σ.numPeriods → G) :
    ProfiniteFenchelGenerator σ → G
  | .surfaceA i => surfaceA i
  | .surfaceB i => surfaceB i
  | .cusp j => cusp j
  | .inertia k => inertia k

structure ProfiniteFGroup where
  carrier : Type u
  [group : Group carrier]
  [topologicalSpace : TopologicalSpace carrier]
  [isTopologicalGroup : IsTopologicalGroup carrier]
  presentationSource : Type u
  [presentationSourceGroup : Group presentationSource]
  [presentationSourceTopologicalSpace : TopologicalSpace presentationSource]
  [presentationSourceIsTopologicalGroup : IsTopologicalGroup presentationSource]
  isProfinite : ProCGroups.IsProfiniteGroup carrier
  topologicallyFinitelyGenerated :
    ProCGroups.FiniteGeneration.TopologicallyFinitelyGenerated carrier
  signature : FenchelSignature
  firstDerivedSignature : FenchelSignature
  surfaceA : Fin signature.orbitGenus → carrier
  surfaceB : Fin signature.orbitGenus → carrier
  cusp : Fin signature.numCusps → carrier
  inertia : Fin signature.numPeriods → carrier
  presentation_relation :
    profiniteFenchelTotalRelation surfaceA surfaceB cusp inertia = 1
  presentation_generates :
    ProCGroups.Generation.TopologicallyGenerates
      (G := carrier)
      (profiniteFenchelGeneratorSet surfaceA surfaceB cusp inertia)
  presentationBasis : ProfiniteFenchelGeneratorIndex.{u} signature → presentationSource
  presentationRelators : Set presentationSource
  presentationRelators_eq :
    presentationRelators =
      profiniteFenchelRelatorSet signature presentationBasis
  presentation :
    ProCGroups.Presentations.IsFreePresentationOfClass
      (ProCGroups.FiniteGroupClass.allFinite :
        ProCGroups.FiniteGroupClass.{u})
      (X := ProfiniteFenchelGeneratorIndex.{u} signature)
      (F := presentationSource) (G := carrier)
      presentationBasis presentationRelators
  presentation_π_surfaceA :
    ∀ i : Fin signature.orbitGenus,
      ProCGroups.Presentations.IsFreePresentationOf.π presentation
        (presentationBasis
          (ULift.up (ProfiniteFenchelGenerator.surfaceA i))) = surfaceA i
  presentation_π_surfaceB :
    ∀ i : Fin signature.orbitGenus,
      ProCGroups.Presentations.IsFreePresentationOf.π presentation
        (presentationBasis
          (ULift.up (ProfiniteFenchelGenerator.surfaceB i))) = surfaceB i
  presentation_π_cusp :
    ∀ j : Fin signature.numCusps,
      ProCGroups.Presentations.IsFreePresentationOf.π presentation
        (presentationBasis
          (ULift.up (ProfiniteFenchelGenerator.cusp j))) = cusp j
  presentation_π_inertia :
    ∀ k : Fin signature.numPeriods,
      ProCGroups.Presentations.IsFreePresentationOf.π presentation
        (presentationBasis
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) = inertia k
  inertia_order : ∀ i, orderOf (inertia i) = signature.periods i

attribute [instance] ProfiniteFGroup.group
attribute [instance] ProfiniteFGroup.topologicalSpace
attribute [instance] ProfiniteFGroup.isTopologicalGroup
attribute [instance] ProfiniteFGroup.presentationSourceGroup
attribute [instance] ProfiniteFGroup.presentationSourceTopologicalSpace
attribute [instance] ProfiniteFGroup.presentationSourceIsTopologicalGroup

namespace ProfiniteFGroup

/-- A profinite Fenchel group has only finitely many open subgroups of each fixed index.

This is the standard finite-generation consequence used by characteristic-closure arguments.
Keeping it as a named lemma avoids rebuilding the finite-generation proof in the public
Fenchel-Nielsen theorems. -/
theorem finiteOpenSubgroupsOfIndex (Δ : ProfiniteFGroup.{u}) :
    ProCGroups.FiniteGeneration.HasFiniteOpenSubgroupsOfIndex Δ.carrier := by
  letI : CompactSpace Δ.carrier :=
    ProCGroups.IsProfiniteGroup.compactSpace Δ.isProfinite
  exact
    ProCGroups.FiniteGeneration.hasFiniteOpenSubgroupsOfIndex_of_topologicallyFinitelyGenerated
      (G := Δ.carrier) Δ.topologicallyFinitelyGenerated

noncomputable def presentationMap (Δ : ProfiniteFGroup.{u}) :
    Δ.presentationSource →ₜ* Δ.carrier :=
  ProCGroups.Presentations.IsFreePresentationOf.π Δ.presentation

theorem presentationMap_surjective (Δ : ProfiniteFGroup.{u}) :
    Function.Surjective Δ.presentationMap :=
  ProCGroups.Presentations.IsFreePresentationOf.π_surjective Δ.presentation

theorem presentationMap_ker_eq_closedNormalClosure
    (Δ : ProfiniteFGroup.{u}) :
    Δ.presentationMap.toMonoidHom.ker =
      ProCGroups.Presentations.closedNormalClosure Δ.presentationRelators :=
  ProCGroups.Presentations.IsFreePresentationOf.kernel_eq_closedNormalClosure
    Δ.presentation

theorem presentationMap_eq_one_of_mem_relators
    (Δ : ProfiniteFGroup.{u}) {x : Δ.presentationSource}
    (hx : x ∈ Δ.presentationRelators) :
    Δ.presentationMap x = 1 := by
  have hxClosed :
      x ∈ ProCGroups.Presentations.closedNormalClosure
        Δ.presentationRelators :=
    ProCGroups.Presentations.subset_closedNormalClosure
      (F := Δ.presentationSource) Δ.presentationRelators hx
  have hxKer : x ∈ Δ.presentationMap.toMonoidHom.ker := by
    rw [presentationMap_ker_eq_closedNormalClosure Δ]
    exact hxClosed
  exact hxKer

@[simp] theorem presentationMap_surfaceA (Δ : ProfiniteFGroup.{u})
    (i : Fin Δ.signature.orbitGenus) :
    Δ.presentationMap
        (Δ.presentationBasis
          (ULift.up (ProfiniteFenchelGenerator.surfaceA i))) =
      Δ.surfaceA i :=
  Δ.presentation_π_surfaceA i

@[simp] theorem presentationMap_surfaceB (Δ : ProfiniteFGroup.{u})
    (i : Fin Δ.signature.orbitGenus) :
    Δ.presentationMap
        (Δ.presentationBasis
          (ULift.up (ProfiniteFenchelGenerator.surfaceB i))) =
      Δ.surfaceB i :=
  Δ.presentation_π_surfaceB i

@[simp] theorem presentationMap_cusp (Δ : ProfiniteFGroup.{u})
    (j : Fin Δ.signature.numCusps) :
    Δ.presentationMap
        (Δ.presentationBasis
          (ULift.up (ProfiniteFenchelGenerator.cusp j))) =
      Δ.cusp j :=
  Δ.presentation_π_cusp j

@[simp] theorem presentationMap_inertia (Δ : ProfiniteFGroup.{u})
    (k : Fin Δ.signature.numPeriods) :
    Δ.presentationMap
        (Δ.presentationBasis
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) =
      Δ.inertia k :=
  Δ.presentation_π_inertia k

theorem presentationMap_totalRelator_eq_one
    (Δ : ProfiniteFGroup.{u}) :
    Δ.presentationMap
        (profiniteFenchelTotalRelation
          (fun i => Δ.presentationBasis
            (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
          (fun i => Δ.presentationBasis
            (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
          (fun j => Δ.presentationBasis
            (ULift.up (ProfiniteFenchelGenerator.cusp j)))
          (fun k => Δ.presentationBasis
            (ULift.up (ProfiniteFenchelGenerator.inertia k)))) = 1 :=
  presentationMap_eq_one_of_mem_relators Δ (by
    rw [Δ.presentationRelators_eq]
    exact Or.inl rfl)

theorem presentationMap_periodRelator_eq_one
    (Δ : ProfiniteFGroup.{u}) (k : Fin Δ.signature.numPeriods) :
    Δ.presentationMap
        (Δ.presentationBasis
          (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^
          Δ.signature.periods k) = 1 :=
  presentationMap_eq_one_of_mem_relators Δ (by
    rw [Δ.presentationRelators_eq]
    exact Or.inr ⟨k, rfl⟩)

noncomputable def presentationLift
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [T1Space A]
    (φ : Δ.presentationSource →ₜ* A)
    (hφ :
      Δ.presentationRelators ⊆ φ.toMonoidHom.ker) :
    Δ.carrier →ₜ* A := by
  have hSourceProfinite :
      ProCGroups.IsProfiniteGroup Δ.presentationSource :=
    ProCGroups.ProC.isProfiniteGroup_of_finiteGroupClassProCPredicate
      (ProCGroups.FiniteGroupClass.allFinite :
        ProCGroups.FiniteGroupClass.{u})
      Δ.presentation.1.isProC
  letI : CompactSpace Δ.presentationSource :=
    ProCGroups.IsProfiniteGroup.compactSpace hSourceProfinite
  letI : T2Space Δ.carrier :=
    ProCGroups.IsProfiniteGroup.t2Space Δ.isProfinite
  have hClosedKer :
      IsClosed ((φ.toMonoidHom.ker : Subgroup Δ.presentationSource) :
        Set Δ.presentationSource) := by
    change IsClosed (φ ⁻¹' ({1} : Set A))
    exact isClosed_singleton.preimage φ.continuous_toFun
  have hClosedNormal :
      ProCGroups.Presentations.closedNormalClosure Δ.presentationRelators ≤
        φ.toMonoidHom.ker :=
    ProCGroups.Presentations.closedNormalClosure_le_closed_normal
      (F := Δ.presentationSource) hClosedKer hφ
  have hker : Δ.presentationMap.toMonoidHom.ker ≤ φ.toMonoidHom.ker := by
    rw [presentationMap_ker_eq_closedNormalClosure Δ]
    exact hClosedNormal
  exact
    ContinuousMonoidHom.liftOfSurjective
      Δ.presentationMap (presentationMap_surjective Δ) φ hker

@[simp] theorem presentationLift_comp_presentationMap
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [T1Space A]
    (φ : Δ.presentationSource →ₜ* A)
    (hφ :
      Δ.presentationRelators ⊆ φ.toMonoidHom.ker) :
    (Δ.presentationLift φ hφ).toMonoidHom.comp
        Δ.presentationMap.toMonoidHom =
      φ.toMonoidHom := by
  ext x
  dsimp [presentationLift]
  simp only [ContinuousMonoidHom.liftOfSurjective_apply]

@[simp] theorem presentationLift_surfaceA
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [T1Space A]
    (φ : Δ.presentationSource →ₜ* A)
    (hφ :
      Δ.presentationRelators ⊆ φ.toMonoidHom.ker)
    (i : Fin Δ.signature.orbitGenus) :
    Δ.presentationLift φ hφ (Δ.surfaceA i) =
      φ (Δ.presentationBasis
        (ULift.up (ProfiniteFenchelGenerator.surfaceA i))) := by
  rw [← presentationMap_surfaceA Δ i]
  exact
    MonoidHom.ext_iff.mp
      (presentationLift_comp_presentationMap Δ φ hφ)
      (Δ.presentationBasis
        (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))

@[simp] theorem presentationLift_surfaceB
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [T1Space A]
    (φ : Δ.presentationSource →ₜ* A)
    (hφ :
      Δ.presentationRelators ⊆ φ.toMonoidHom.ker)
    (i : Fin Δ.signature.orbitGenus) :
    Δ.presentationLift φ hφ (Δ.surfaceB i) =
      φ (Δ.presentationBasis
        (ULift.up (ProfiniteFenchelGenerator.surfaceB i))) := by
  rw [← presentationMap_surfaceB Δ i]
  exact
    MonoidHom.ext_iff.mp
      (presentationLift_comp_presentationMap Δ φ hφ)
      (Δ.presentationBasis
        (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))

@[simp] theorem presentationLift_cusp
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [T1Space A]
    (φ : Δ.presentationSource →ₜ* A)
    (hφ :
      Δ.presentationRelators ⊆ φ.toMonoidHom.ker)
    (j : Fin Δ.signature.numCusps) :
    Δ.presentationLift φ hφ (Δ.cusp j) =
      φ (Δ.presentationBasis
        (ULift.up (ProfiniteFenchelGenerator.cusp j))) := by
  rw [← presentationMap_cusp Δ j]
  exact
    MonoidHom.ext_iff.mp
      (presentationLift_comp_presentationMap Δ φ hφ)
      (Δ.presentationBasis
        (ULift.up (ProfiniteFenchelGenerator.cusp j)))

@[simp 900] theorem presentationLift_inertia
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [T1Space A]
    (φ : Δ.presentationSource →ₜ* A)
    (hφ :
      Δ.presentationRelators ⊆ φ.toMonoidHom.ker)
    (k : Fin Δ.signature.numPeriods) :
    Δ.presentationLift φ hφ (Δ.inertia k) =
      φ (Δ.presentationBasis
        (ULift.up (ProfiniteFenchelGenerator.inertia k))) := by
  rw [← presentationMap_inertia Δ k]
  exact
    MonoidHom.ext_iff.mp
      (presentationLift_comp_presentationMap Δ φ hφ)
      (Δ.presentationBasis
        (ULift.up (ProfiniteFenchelGenerator.inertia k)))

/-- Lift an arbitrary assignment of the Fenchel-Nielsen presentation generators to a finite discrete group
to the free profinite presentation source. -/
noncomputable def presentationSourceLiftToFinite
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (χ : ProfiniteFenchelGeneratorIndex.{u} Δ.signature → A) :
    Δ.presentationSource →ₜ* A := by
  letI : IsTopologicalGroup A := inferInstance
  have hCG :
      (ProCGroups.FiniteGroupClass.allFinite :
        ProCGroups.FiniteGroupClass.{u}).pred A := by
    change Finite A
    infer_instance
  have hA :
      (ProCGroups.ProC.finiteGroupClassProCPredicate
        (ProCGroups.FiniteGroupClass.allFinite :
          ProCGroups.FiniteGroupClass.{u})).holds (G := A) := by
    exact
      ProCGroups.ProC.IsProCGroup.of_finite_discrete
        (C := (ProCGroups.FiniteGroupClass.allFinite :
          ProCGroups.FiniteGroupClass.{u}))
        ProCGroups.FiniteGroupClass.allFinite_quotientClosed hCG
  have hχ : Continuous χ := continuous_of_discreteTopology
  exact
    { toMonoidHom := Δ.presentation.1.lift hA χ hχ
      continuous_toFun := (Δ.presentation.1.lift_spec hA χ hχ).1 }

@[simp 900] theorem presentationSourceLiftToFinite_basis
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (χ : ProfiniteFenchelGeneratorIndex.{u} Δ.signature → A)
    (x : ProfiniteFenchelGeneratorIndex.{u} Δ.signature) :
    Δ.presentationSourceLiftToFinite χ (Δ.presentationBasis x) = χ x := by
  letI : IsTopologicalGroup A := inferInstance
  have hCG :
      (ProCGroups.FiniteGroupClass.allFinite :
        ProCGroups.FiniteGroupClass.{u}).pred A := by
    change Finite A
    infer_instance
  have hA :
      (ProCGroups.ProC.finiteGroupClassProCPredicate
        (ProCGroups.FiniteGroupClass.allFinite :
          ProCGroups.FiniteGroupClass.{u})).holds (G := A) := by
    exact
      ProCGroups.ProC.IsProCGroup.of_finite_discrete
        (C := (ProCGroups.FiniteGroupClass.allFinite :
          ProCGroups.FiniteGroupClass.{u}))
        ProCGroups.FiniteGroupClass.allFinite_quotientClosed hCG
  have hχ : Continuous χ := continuous_of_discreteTopology
  change (Δ.presentation.1.lift hA χ hχ) (Δ.presentationBasis x) = χ x
  exact (Δ.presentation.1.lift_spec hA χ hχ).2 x

theorem presentationSourceLiftToFinite_totalRelator
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (χ : ProfiniteFenchelGeneratorIndex.{u} Δ.signature → A) :
    Δ.presentationSourceLiftToFinite χ
        (profiniteFenchelTotalRelation
          (fun i => Δ.presentationBasis
            (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
          (fun i => Δ.presentationBasis
            (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
          (fun j => Δ.presentationBasis
            (ULift.up (ProfiniteFenchelGenerator.cusp j)))
          (fun k => Δ.presentationBasis
            (ULift.up (ProfiniteFenchelGenerator.inertia k)))) =
      profiniteFenchelTotalRelation
        (fun i => χ (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
        (fun i => χ (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
        (fun j => χ (ULift.up (ProfiniteFenchelGenerator.cusp j)))
        (fun k => χ (ULift.up (ProfiniteFenchelGenerator.inertia k))) := by
  simp only [profiniteFenchelTotalRelation, map_mul, map_list_prod, List.map_map, Function.comp_def,
  map_commutatorElement, presentationSourceLiftToFinite_basis]

theorem presentationSourceLiftToFinite_periodRelator
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (χ : ProfiniteFenchelGeneratorIndex.{u} Δ.signature → A)
    (k : Fin Δ.signature.numPeriods) :
    Δ.presentationSourceLiftToFinite χ
        (Δ.presentationBasis
          (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^
          Δ.signature.periods k) =
      χ (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^
        Δ.signature.periods k := by
  simp only [map_pow, presentationSourceLiftToFinite_basis]

theorem presentationSourceLiftToFinite_relators_subset_ker
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (χ : ProfiniteFenchelGeneratorIndex.{u} Δ.signature → A)
    (hTotal :
      profiniteFenchelTotalRelation
          (fun i => χ (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
          (fun i => χ (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
          (fun j => χ (ULift.up (ProfiniteFenchelGenerator.cusp j)))
          (fun k => χ (ULift.up (ProfiniteFenchelGenerator.inertia k))) = 1)
    (hPeriod :
      ∀ k : Fin Δ.signature.numPeriods,
        χ (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^
          Δ.signature.periods k = 1) :
    Δ.presentationRelators ⊆
      (Δ.presentationSourceLiftToFinite χ).toMonoidHom.ker := by
  intro x hx
  rw [Δ.presentationRelators_eq] at hx
  rcases hx with hxTotal | ⟨k, rfl⟩
  · rw [Set.mem_singleton_iff] at hxTotal
    subst x
    simpa [presentationSourceLiftToFinite_totalRelator] using hTotal
  · simpa [presentationSourceLiftToFinite_periodRelator] using hPeriod k

/-- Descend a finite-generator assignment to the presented profinite `F`-group once the
presentation relators vanish under the induced free-source map. -/
noncomputable def presentationLiftToFinite
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (χ : ProfiniteFenchelGeneratorIndex.{u} Δ.signature → A)
    (hχ :
      Δ.presentationRelators ⊆
        (Δ.presentationSourceLiftToFinite χ).toMonoidHom.ker) :
    Δ.carrier →ₜ* A :=
  Δ.presentationLift (Δ.presentationSourceLiftToFinite χ) hχ

/-- A finite target assignment satisfying exactly the Fenchel-Nielsen total and period relations descends to
the profinite `F`-group. -/
noncomputable def presentationLiftToFiniteOfRelations
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (χ : ProfiniteFenchelGeneratorIndex.{u} Δ.signature → A)
    (hTotal :
      profiniteFenchelTotalRelation
          (fun i => χ (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
          (fun i => χ (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
          (fun j => χ (ULift.up (ProfiniteFenchelGenerator.cusp j)))
          (fun k => χ (ULift.up (ProfiniteFenchelGenerator.inertia k))) = 1)
    (hPeriod :
      ∀ k : Fin Δ.signature.numPeriods,
        χ (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^
          Δ.signature.periods k = 1) :
    Δ.carrier →ₜ* A :=
  Δ.presentationLiftToFinite χ
    (presentationSourceLiftToFinite_relators_subset_ker Δ χ hTotal hPeriod)

@[simp] theorem presentationLiftToFinite_surfaceA
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (χ : ProfiniteFenchelGeneratorIndex.{u} Δ.signature → A)
    (hχ :
      Δ.presentationRelators ⊆
        (Δ.presentationSourceLiftToFinite χ).toMonoidHom.ker)
    (i : Fin Δ.signature.orbitGenus) :
    Δ.presentationLiftToFinite χ hχ (Δ.surfaceA i) =
      χ (ULift.up (ProfiniteFenchelGenerator.surfaceA i)) := by
  simp only [presentationLiftToFinite, presentationLift_surfaceA, presentationSourceLiftToFinite_basis]

@[simp] theorem presentationLiftToFinite_surfaceB
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (χ : ProfiniteFenchelGeneratorIndex.{u} Δ.signature → A)
    (hχ :
      Δ.presentationRelators ⊆
        (Δ.presentationSourceLiftToFinite χ).toMonoidHom.ker)
    (i : Fin Δ.signature.orbitGenus) :
    Δ.presentationLiftToFinite χ hχ (Δ.surfaceB i) =
      χ (ULift.up (ProfiniteFenchelGenerator.surfaceB i)) := by
  simp only [presentationLiftToFinite, presentationLift_surfaceB, presentationSourceLiftToFinite_basis]

@[simp] theorem presentationLiftToFinite_cusp
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (χ : ProfiniteFenchelGeneratorIndex.{u} Δ.signature → A)
    (hχ :
      Δ.presentationRelators ⊆
        (Δ.presentationSourceLiftToFinite χ).toMonoidHom.ker)
    (j : Fin Δ.signature.numCusps) :
    Δ.presentationLiftToFinite χ hχ (Δ.cusp j) =
      χ (ULift.up (ProfiniteFenchelGenerator.cusp j)) := by
  simp only [presentationLiftToFinite, presentationLift_cusp, presentationSourceLiftToFinite_basis]

@[simp] theorem presentationLiftToFinite_inertia
    (Δ : ProfiniteFGroup.{u})
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    (χ : ProfiniteFenchelGeneratorIndex.{u} Δ.signature → A)
    (hχ :
      Δ.presentationRelators ⊆
        (Δ.presentationSourceLiftToFinite χ).toMonoidHom.ker)
    (k : Fin Δ.signature.numPeriods) :
    Δ.presentationLiftToFinite χ hχ (Δ.inertia k) =
      χ (ULift.up (ProfiniteFenchelGenerator.inertia k)) := by
  simp only [presentationLiftToFinite, presentationLift_inertia, presentationSourceLiftToFinite_basis]

def IsHyperbolic (Δ : ProfiniteFGroup) : Prop :=
  Δ.signature.IsHyperbolic

def IsPerfect (Δ : ProfiniteFGroup) : Prop :=
  profiniteDerivedSeries Δ.carrier 1 = ⊤

def IsNonPerfect (Δ : ProfiniteFGroup) : Prop :=
  ¬ Δ.IsPerfect

def PairwiseCoprimePeriods (Δ : ProfiniteFGroup) : Prop :=
  ∀ i j : Fin Δ.signature.numPeriods,
    i ≠ j → Nat.Coprime (Δ.signature.periods i) (Δ.signature.periods j)

def CharPerfectNumericalCondition (Δ : ProfiniteFGroup) : Prop :=
  Δ.signature.orbitGenus = 0 ∧
    Δ.signature.numCusps = 0 ∧
      Δ.PairwiseCoprimePeriods

end ProfiniteFGroup

def ProfiniteOpenNormalQuotientHasDerivedLengthAtMost
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) (m : ℕ) : Prop :=
  profiniteDerivedSeries (G ⧸ (U : Subgroup G)) m = ⊥

def ProfiniteOpenNormalSubgroupTorsionFree
    (G : Type u) [Group G] [TopologicalSpace G]
    (U : OpenNormalSubgroup G) : Prop :=
  ∀ x : G, x ∈ (U : Subgroup G) → IsOfFinOrder x → x = 1

def ProfiniteOpenCharacteristicSubgroup
    (G : Type u) [Group G] [TopologicalSpace G] : Type u :=
  { U : OpenNormalSubgroup G //
    ProCGroups.FiniteGeneration.IsTopologicallyCharacteristic (G := G) (U : Subgroup G) }

def ProfiniteOpenCharacteristicSubgroup.toOpenNormalSubgroup
    {G : Type u} [Group G] [TopologicalSpace G]
    (U : ProfiniteOpenCharacteristicSubgroup G) :
    OpenNormalSubgroup G :=
  U.1

def ProfiniteOpenCharacteristicQuotientHasDerivedLengthAtMost
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : ProfiniteOpenCharacteristicSubgroup G) (m : ℕ) : Prop :=
  ProfiniteOpenNormalQuotientHasDerivedLengthAtMost G U.toOpenNormalSubgroup m

def HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ) : Prop :=
  ∃ U : OpenNormalSubgroup G,
    ProfiniteOpenNormalSubgroupTorsionFree G U ∧
      ProfiniteOpenNormalQuotientHasDerivedLengthAtMost G U m

def HasTorsionFreeOpenCharacteristicSubgroupQuotientDerivedLengthAtMost
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m : ℕ) : Prop :=
  ∃ U : ProfiniteOpenCharacteristicSubgroup G,
    ProfiniteOpenNormalSubgroupTorsionFree G U.toOpenNormalSubgroup ∧
      ProfiniteOpenCharacteristicQuotientHasDerivedLengthAtMost G U m

theorem ProfiniteOpenNormalQuotientHasDerivedLengthAtMost.of_topDerived_le
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) {m : ℕ}
    (hU : profiniteDerivedSeries G m ≤ (U : Subgroup G)) :
    ProfiniteOpenNormalQuotientHasDerivedLengthAtMost G U m := by
  let q : G →ₜ* G ⧸ (U : Subgroup G) := OpenNormalSubgroup.quotientProj U
  have hclosed_comm :
      ∀ n : ℕ,
        IsClosed
          (((closedCommutator
              (topDerivedTop G n) (topDerivedTop G n)).map
                (q : G →* G ⧸ (U : Subgroup G)) :
              Subgroup (G ⧸ (U : Subgroup G))) :
            Set (G ⧸ (U : Subgroup G))) := by
    intro n
    exact isClosed_discrete _
  have hmap :
      (topDerivedTop G m).map (q : G →* G ⧸ (U : Subgroup G)) =
        topDerivedTop (G ⧸ (U : Subgroup G)) m := by
    exact
      topDerived_map_eq_of_surj (f := q)
        (OpenNormalSubgroup.quotientProj_surjective U) hclosed_comm m
  rw [ProfiniteOpenNormalQuotientHasDerivedLengthAtMost, profiniteDerivedSeries,
    ← hmap]
  apply le_bot_iff.mp
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  change QuotientGroup.mk' (U : Subgroup G) x = 1
  exact (QuotientGroup.eq_one_iff (N := (U : Subgroup G)) x).2 (hU hx)

theorem ProfiniteOpenNormalQuotientHasDerivedLengthAtMost.topDerived_le
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenNormalSubgroup G) {m : ℕ}
    (hU : ProfiniteOpenNormalQuotientHasDerivedLengthAtMost G U m) :
    profiniteDerivedSeries G m ≤ (U : Subgroup G) := by
  let q : G →ₜ* G ⧸ (U : Subgroup G) := OpenNormalSubgroup.quotientProj U
  have hle := topDerivedTop_le_comap (f := q) (m := m)
  intro x hx
  have hxq :
      q x ∈ topDerivedTop (G ⧸ (U : Subgroup G)) m :=
    hle hx
  have hderbot :
      topDerivedTop (G ⧸ (U : Subgroup G)) m = ⊥ := by
    simpa [ProfiniteOpenNormalQuotientHasDerivedLengthAtMost,
      profiniteDerivedSeries] using hU
  have hxqbot :
      q x ∈ (⊥ : Subgroup (G ⧸ (U : Subgroup G))) := by
    simpa [hderbot] using hxq
  have hq1 : q x = 1 := Subgroup.mem_bot.mp hxqbot
  simpa [q] using
    (OpenNormalSubgroup.quotientProj_eq_one_iff (U := U) (x := x)).1 hq1

theorem profiniteOpenNormalQuotientHasDerivedLengthAtMost_iff_topDerived_le
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {U : OpenNormalSubgroup G} {m : ℕ} :
    ProfiniteOpenNormalQuotientHasDerivedLengthAtMost G U m ↔
      profiniteDerivedSeries G m ≤ (U : Subgroup G) := by
  constructor
  · exact ProfiniteOpenNormalQuotientHasDerivedLengthAtMost.topDerived_le U
  · exact ProfiniteOpenNormalQuotientHasDerivedLengthAtMost.of_topDerived_le U

theorem ProfiniteOpenNormalQuotientHasDerivedLengthAtMost.mono
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {U : OpenNormalSubgroup G} {m n : ℕ}
    (hmn : m ≤ n)
    (hU : ProfiniteOpenNormalQuotientHasDerivedLengthAtMost G U m) :
    ProfiniteOpenNormalQuotientHasDerivedLengthAtMost G U n := by
  rw [profiniteOpenNormalQuotientHasDerivedLengthAtMost_iff_topDerived_le] at hU ⊢
  intro x hx
  exact hU ((topDerivedTop_antitone hmn) hx)

theorem HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost.mono
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {m n : ℕ} (hmn : m ≤ n)
    (h :
      HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost G m) :
    HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost G n := by
  rcases h with ⟨U, htf, hquot⟩
  exact ⟨U, htf,
    ProfiniteOpenNormalQuotientHasDerivedLengthAtMost.mono hmn hquot⟩

theorem HasTorsionFreeOpenCharacteristicSubgroupQuotientDerivedLengthAtMost.mono
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {m n : ℕ} (hmn : m ≤ n)
    (h :
      HasTorsionFreeOpenCharacteristicSubgroupQuotientDerivedLengthAtMost
        G m) :
    HasTorsionFreeOpenCharacteristicSubgroupQuotientDerivedLengthAtMost
      G n := by
  rcases h with ⟨U, htf, hquot⟩
  exact ⟨U, htf,
    ProfiniteOpenNormalQuotientHasDerivedLengthAtMost.mono hmn hquot⟩

theorem hasTorsionFreeOpenNormal_of_characteristic
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {m : ℕ}
    (h :
      HasTorsionFreeOpenCharacteristicSubgroupQuotientDerivedLengthAtMost
        G m) :
    HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost G m := by
  rcases h with ⟨U, htf, hquot⟩
  exact ⟨U.toOpenNormalSubgroup, htf, hquot⟩

end FenchelNielsen
