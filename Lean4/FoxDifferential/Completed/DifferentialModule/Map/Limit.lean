import FoxDifferential.Completed.DifferentialModule.Map.Stage

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/DifferentialModule/Map/Limit.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed differential modules

The completed differential module is organized separately from coefficient algebras; its universal and quotient maps are used by completed crossed differentials.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Definition of primePowerCompletedGroupAlgebraMap. -/
def primePowerCompletedGroupAlgebraMap
    (ψ : ContinuousMonoidHom G H) :
    PrimePowerCompletedGroupAlgebra ℓ G →+* PrimePowerCompletedGroupAlgebra ℓ H where
  toFun x := ⟨fun i =>
      primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
          (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x), by
    intro i j hij
    let hsource :
        (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) ≤
          (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2) :=
      ⟨hij.1, completedGroupAlgebraComapIndex_mono (G := G) (H := H) ψ hij.2⟩
    have hx := x.2
      (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)
      (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2)
      hsource
    change
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hsource
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
            (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2) x) =
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
          (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x at hx
    have hcompat := congrFun
      (congrArg DFunLike.coe
        (primePowerCompletedGroupAlgebraMapStage_compatible
          (ℓ := ℓ) (G := G) (H := H) ψ hij))
      (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
        (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2) x)
    rw [RingHom.comp_apply, RingHom.comp_apply] at hcompat
    rw [hx] at hcompat
    simpa [primePowerCompletedGroupAlgebraSystem] using hcompat⟩
  map_one' := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ H).ext
    intro i
    simp only [primePowerCompletedGroupAlgebraMapStage, InverseSystems.InverseSystem.projection_apply,
  coe_one_primePowerCompletedGroupAlgebra, Pi.one_apply, MonoidAlgebra.mapDomainRingHom_apply,
  MonoidAlgebra.mapDomain_one]
  map_mul' := by
    intro x y
    apply (primePowerCompletedGroupAlgebraSystem ℓ H).ext
    intro i
    simp only [InverseSystems.InverseSystem.projection_apply, coe_mul_primePowerCompletedGroupAlgebra,
  Pi.mul_apply, map_mul]
  map_zero' := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ H).ext
    intro i
    simp only [primePowerCompletedGroupAlgebraMapStage, InverseSystems.InverseSystem.projection_apply,
  coe_zero_primePowerCompletedGroupAlgebra, Pi.zero_apply, MonoidAlgebra.mapDomainRingHom_apply,
  Finsupp.mapDomain_zero]
  map_add' := by
    intro x y
    apply (primePowerCompletedGroupAlgebraSystem ℓ H).ext
    intro i
    simp only [InverseSystems.InverseSystem.projection_apply, coe_add_primePowerCompletedGroupAlgebra,
  Pi.add_apply, map_add]

/-- 素冪係数で定めた 有限段階射影が関手的写像が有限段階射影と両立することを述べる。 -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_map
    (ψ : ContinuousMonoidHom G H) (i : PrimePowerCompletedGroupAlgebraIndex H)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := H) i
        (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ x) =
      primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G)
          (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x) := rfl


/-- The completed group-algebra map induced by a continuous homomorphism is continuous for the
inverse-limit topologies. -/
theorem continuous_primePowerCompletedGroupAlgebraMap
    (ψ : ContinuousMonoidHom G H) :
    Continuous (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ) := by
  let S := primePowerCompletedGroupAlgebraSystem ℓ H
  let T := primePowerCompletedGroupAlgebraSystem ℓ G
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex H, TopologicalSpace (S.X i) :=
    fun i => S.topologicalSpace i
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, TopologicalSpace (T.X i) :=
    fun i => T.topologicalSpace i
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) (fun x =>
    (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ x).2)
  let sourceIndex : PrimePowerCompletedGroupAlgebraIndex G :=
    (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)
  letI : TopologicalSpace (PrimePowerCompletedGroupAlgebraStage ℓ G sourceIndex) :=
    T.topologicalSpace sourceIndex
  letI : DiscreteTopology (PrimePowerCompletedGroupAlgebraStage ℓ G sourceIndex) := ⟨rfl⟩
  letI : TopologicalSpace (PrimePowerCompletedGroupAlgebraStage ℓ H i) :=
    S.topologicalSpace i
  have hstage :
      Continuous
        (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i) :=
    continuous_of_discreteTopology
  change Continuous (fun x : PrimePowerCompletedGroupAlgebra ℓ G =>
    primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
      (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) sourceIndex x))
  exact hstage.comp (T.continuous_projection sourceIndex)

end

end FoxDifferential
