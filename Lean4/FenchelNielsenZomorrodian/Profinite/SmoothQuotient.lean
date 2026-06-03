import FenchelNielsenZomorrodian.Profinite.TorsionFrontier

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Profinite/SmoothQuotient.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite smooth quotients of profinite Fenchel groups

Packages finite quotient maps whose inertia images have exactly the prescribed period and derives
torsion-free kernels with bounded derived length.
-/

namespace FenchelNielsen

universe u v

open ProCGroups.FiniteStepSolvableQuotients
open ProCGroups.ProC

namespace ProfiniteFGroup

/-- A finite smooth quotient of a profinite `F`-group.

The datum is the profinite analogue of the finite smooth quotient data used on the discrete side:
the target is finite and discrete, the quotient has derived length at most `m`, and each inertia
generator maps to an element of exactly the prescribed period.
-/
structure ProfiniteSmoothQuotientData
    (Δ : ProfiniteFGroup.{u}) (m : ℕ) where
  Q : Type u
  [group : Group Q]
  [topologicalSpace : TopologicalSpace Q]
  [discreteTopology : DiscreteTopology Q]
  [isTopologicalGroup : IsTopologicalGroup Q]
  [finite : Finite Q]
  φ : Δ.carrier →ₜ* Q
  derived_length : profiniteDerivedSeries Q m = ⊥
  inertia_exact :
    ∀ i : Fin Δ.signature.numPeriods,
      orderOf (φ (Δ.inertia i)) = Δ.signature.periods i

attribute [instance] ProfiniteSmoothQuotientData.group
attribute [instance] ProfiniteSmoothQuotientData.topologicalSpace
attribute [instance] ProfiniteSmoothQuotientData.discreteTopology
attribute [instance] ProfiniteSmoothQuotientData.isTopologicalGroup
attribute [instance] ProfiniteSmoothQuotientData.finite

namespace ProfiniteSmoothQuotientData

/-- The open normal kernel attached to a finite smooth quotient. -/
def kernelOpenNormal {Δ : ProfiniteFGroup.{u}} {m : ℕ}
    (D : ProfiniteSmoothQuotientData Δ m) :
    OpenNormalSubgroup Δ.carrier :=
  OpenNormalSubgroup.ker D.φ

/-- Membership in the kernel open normal subgroup is equality to `1` after applying `φ`. -/
@[simp] theorem mem_kernelOpenNormal
    {Δ : ProfiniteFGroup.{u}} {m : ℕ}
    {D : ProfiniteSmoothQuotientData Δ m} {x : Δ.carrier} :
    x ∈ (D.kernelOpenNormal : Subgroup Δ.carrier) ↔ D.φ x = 1 := by
  rfl

/-- The `m`-th profinite derived subgroup is contained in the kernel of the quotient map. -/
theorem topDerived_le_kernel
    {Δ : ProfiniteFGroup.{u}} {m : ℕ}
    (D : ProfiniteSmoothQuotientData Δ m) :
    profiniteDerivedSeries Δ.carrier m ≤
      (D.kernelOpenNormal : Subgroup Δ.carrier) := by
  intro x hx
  have hxImage :
      D.φ x ∈ profiniteDerivedSeries D.Q m :=
    topDerivedTop_le_comap (f := D.φ) (m := m) hx
  have hxBot : D.φ x ∈ (⊥ : Subgroup D.Q) := by
    simpa [D.derived_length] using hxImage
  exact Subgroup.mem_bot.mp hxBot

/-- The quotient by the kernel has derived length at most the quotient datum bound. -/
theorem kernel_quotient_has_derivedLengthAtMost
    {Δ : ProfiniteFGroup.{u}} {m : ℕ}
    (D : ProfiniteSmoothQuotientData Δ m) :
    ProfiniteOpenNormalQuotientHasDerivedLengthAtMost
      Δ.carrier D.kernelOpenNormal m :=
  ProfiniteOpenNormalQuotientHasDerivedLengthAtMost.of_topDerived_le
    D.kernelOpenNormal D.topDerived_le_kernel

/-- The smooth quotient kernel avoids all nontrivial inertia powers. -/
theorem kernel_avoidsNontrivialInertia
    {Δ : ProfiniteFGroup.{u}} {m : ℕ}
    (D : ProfiniteSmoothQuotientData Δ m) :
    Δ.avoidsNontrivialInertia D.kernelOpenNormal := by
  intro i n hn
  have hφpow : D.φ (Δ.inertia i ^ n) = 1 := by
    simpa using (mem_kernelOpenNormal (D := D)).1 hn
  have hImagePow : D.φ (Δ.inertia i) ^ n = 1 := by
    simpa [MonoidHom.map_zpow] using hφpow
  have hdivImage : (orderOf (D.φ (Δ.inertia i)) : ℤ) ∣ n :=
    orderOf_dvd_iff_zpow_eq_one.mpr hImagePow
  have hdivSource : (orderOf (Δ.inertia i) : ℤ) ∣ n := by
    rw [Δ.inertia_order i, ← D.inertia_exact i]
    exact hdivImage
  exact orderOf_dvd_iff_zpow_eq_one.mp hdivSource

/-- The smooth quotient kernel is torsion-free. -/
theorem kernel_torsionFree
    {Δ : ProfiniteFGroup.{u}} {m : ℕ}
    (D : ProfiniteSmoothQuotientData Δ m) :
    ProfiniteOpenNormalSubgroupTorsionFree
      Δ.carrier D.kernelOpenNormal :=
  torsionFree_of_avoidsNontrivialInertia
    Δ D.kernelOpenNormal D.kernel_avoidsNontrivialInertia

/-- A smooth quotient datum gives a torsion-free open normal subgroup with bounded quotient. -/
theorem has_torsionFreeOpenNormal_quotient_derivedLengthAtMost
    {Δ : ProfiniteFGroup.{u}} {m : ℕ}
    (D : ProfiniteSmoothQuotientData Δ m) :
    HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost
      Δ.carrier m :=
  ⟨D.kernelOpenNormal, D.kernel_torsionFree,
    D.kernel_quotient_has_derivedLengthAtMost⟩

/-- The quotient derived-length bound is monotone in the target bound. -/
theorem has_torsionFreeOpenNormal_quotient_derivedLength_le
    {Δ : ProfiniteFGroup.{u}} {m n : ℕ}
    (D : ProfiniteSmoothQuotientData Δ m) (hmn : m ≤ n) :
    HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost
      Δ.carrier n :=
  HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost.mono
    hmn D.has_torsionFreeOpenNormal_quotient_derivedLengthAtMost

/-- Build profinite smooth quotient data from a finite target assignment satisfying the
Fenchel-Nielsen presentation relations. -/
noncomputable def ofPresentationLiftToFiniteOfRelations
    (Δ : ProfiniteFGroup.{u}) {m : ℕ}
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalGroup A] [Finite A]
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
          Δ.signature.periods k = 1)
    (hDerived : profiniteDerivedSeries A m = ⊥)
    (hInertiaExact :
      ∀ i : Fin Δ.signature.numPeriods,
        orderOf (χ (ULift.up (ProfiniteFenchelGenerator.inertia i))) =
          Δ.signature.periods i) :
    ProfiniteSmoothQuotientData Δ m where
  Q := A
  φ := Δ.presentationLiftToFiniteOfRelations χ hTotal hPeriod
  derived_length := hDerived
  inertia_exact := by
    intro i
    simpa [presentationLiftToFiniteOfRelations] using hInertiaExact i

/-- Build profinite smooth quotient data from a finite discrete target whose abstract derived
series has the requested length. -/
noncomputable def ofPresentationLiftToFiniteOfRelationsOfDerivedSeries
    (Δ : ProfiniteFGroup.{u}) {m : ℕ}
    {A : Type u} [Group A] [TopologicalSpace A] [DiscreteTopology A]
    [IsTopologicalGroup A] [Finite A]
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
          Δ.signature.periods k = 1)
    (hDerived : derivedSeries A m = ⊥)
    (hInertiaExact :
      ∀ i : Fin Δ.signature.numPeriods,
        orderOf (χ (ULift.up (ProfiniteFenchelGenerator.inertia i))) =
          Δ.signature.periods i) :
    ProfiniteSmoothQuotientData Δ m :=
  ofPresentationLiftToFiniteOfRelations
    Δ χ hTotal hPeriod
    (by
      rw [profiniteDerivedSeries_eq_derivedSeries_of_discrete]
      exact hDerived)
    hInertiaExact

end ProfiniteSmoothQuotientData

end ProfiniteFGroup

end FenchelNielsen
