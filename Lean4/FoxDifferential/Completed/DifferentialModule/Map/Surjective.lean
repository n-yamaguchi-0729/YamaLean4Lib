import FoxDifferential.Completed.DifferentialModule.Map.Limit

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/DifferentialModule/Map/Surjective.lean
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

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- If `ψ : G → H` is surjective, then the induced map of prime-power completed group algebras
is surjective.  The proof uses finite-stage surjectivity and inverse-limit closed-image gluing;
it deliberately stays inside completed group algebras, where the finite projections are genuine
inverse-limit projections. -/
theorem primePowerCompletedGroupAlgebraMap_surjective
    (ψ : ContinuousMonoidHom G H) (hψ : Function.Surjective ψ) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ) := by
  classical
  let S := primePowerCompletedGroupAlgebraSystem ℓ H
  let T := primePowerCompletedGroupAlgebraSystem ℓ G
  let f : PrimePowerCompletedGroupAlgebra ℓ G → PrimePowerCompletedGroupAlgebra ℓ H :=
    primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
  letI : Nonempty (PrimePowerCompletedGroupAlgebraIndex H) :=
    ⟨(0, _root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex H)⟩
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex H, TopologicalSpace (S.X i) :=
    fun i => S.topologicalSpace i
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex H, DiscreteTopology (S.X i) :=
    fun _ => ⟨rfl⟩
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex H, CompactSpace (S.X i) :=
    fun i => by
      letI : Finite (S.X i) := by
        dsimp [S, primePowerCompletedGroupAlgebraSystem]
        infer_instance
      letI : Fintype (S.X i) := Fintype.ofFinite _
      infer_instance
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex H, T2Space (S.X i) :=
    fun _ => inferInstance
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, TopologicalSpace (T.X i) :=
    fun i => T.topologicalSpace i
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, DiscreteTopology (T.X i) :=
    fun _ => ⟨rfl⟩
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, CompactSpace (T.X i) :=
    fun i => by
      letI : Finite (T.X i) := by
        dsimp [T, primePowerCompletedGroupAlgebraSystem]
        infer_instance
      letI : Fintype (T.X i) := Fintype.ofFinite _
      infer_instance
  letI : ∀ i : PrimePowerCompletedGroupAlgebraIndex G, T2Space (T.X i) :=
    fun _ => inferInstance
  letI : CompactSpace (PrimePowerCompletedGroupAlgebra ℓ G) :=
    inferInstance
  letI : T2Space (PrimePowerCompletedGroupAlgebra ℓ H) :=
    S.t2Space_inverseLimit
  have hf_continuous : Continuous f :=
    continuous_primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
  have hclosed : IsClosed (Set.range f) :=
    (isCompact_range hf_continuous).isClosed
  have hprojection_images :
      ∀ i : PrimePowerCompletedGroupAlgebraIndex H,
        S.projection i '' Set.range f =
          S.projection i '' (Set.univ : Set (PrimePowerCompletedGroupAlgebra ℓ H)) := by
    intro i
    apply Set.Subset.antisymm
    · rintro z ⟨y, _hy, rfl⟩
      exact ⟨y, trivial, rfl⟩
    · rintro z ⟨y, _hy, rfl⟩
      rcases primePowerCompletedGroupAlgebraMapStage_surjective
          (ℓ := ℓ) (G := G) (H := H) ψ hψ i (S.projection i y) with
        ⟨c, hc⟩
      let sourceIndex : PrimePowerCompletedGroupAlgebraIndex G :=
        (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)
      rcases primePowerCompletedGroupAlgebraProjection_surjective
          (ℓ := ℓ) (G := G) sourceIndex c with
        ⟨x, hx⟩
      refine ⟨f x, ⟨x, rfl⟩, ?_⟩
      change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := H) i
          (primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ x) =
        S.projection i y
      rw [primePowerCompletedGroupAlgebraProjection_map]
      change primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) sourceIndex x) =
        S.projection i y
      rw [hx, hc]
  have hclosure :
      closure (Set.range f) =
        (Set.univ : Set (PrimePowerCompletedGroupAlgebra ℓ H)) := by
    have hclosure' :
        closure (Set.range f) =
          closure (Set.univ : Set (PrimePowerCompletedGroupAlgebra ℓ H)) :=
        S.closure_eq_of_projection_images_eq_of_subsets
          (directed_primePowerCompletedGroupAlgebraIndex (G := H))
        (Set.range f)
        (Set.univ : Set (PrimePowerCompletedGroupAlgebra ℓ H))
        hprojection_images
    simpa using hclosure'
  intro y
  have hy_closure : y ∈ closure (Set.range f) := by
    rw [hclosure]
    simp only [Set.mem_univ]
  have hy_range : y ∈ Set.range f := by
    rwa [hclosed.closure_eq] at hy_closure
  rcases hy_range with ⟨x, hx⟩
  exact ⟨x, hx⟩

/-- A choice of a lift along a surjective completed group-algebra map.

This is intentionally kept at the completed group-algebra level: it uses the already-proved
surjectivity of `Λ_G -> Λ_H`, and does not touch the displayed differential premodule topology. -/
def primePowerCompletedGroupAlgebraMapLiftOfSurjective
    (ψ : ContinuousMonoidHom G H) (hψ : Function.Surjective ψ)
    (a : PrimePowerCompletedGroupAlgebra ℓ H) :
    PrimePowerCompletedGroupAlgebra ℓ G :=
  Classical.choose
    (primePowerCompletedGroupAlgebraMap_surjective
      (ℓ := ℓ) (G := G) (H := H) ψ hψ a)

/-- The chosen lift maps back to the target coefficient. -/
@[simp]
theorem primePowerCompletedGroupAlgebraMap_liftOfSurjective
    (ψ : ContinuousMonoidHom G H) (hψ : Function.Surjective ψ)
    (a : PrimePowerCompletedGroupAlgebra ℓ H) :
    primePowerCompletedGroupAlgebraMap (ℓ := ℓ) (G := G) (H := H) ψ
        (primePowerCompletedGroupAlgebraMapLiftOfSurjective
          (ℓ := ℓ) (G := G) (H := H) ψ hψ a) = a :=
  Classical.choose_spec
    (primePowerCompletedGroupAlgebraMap_surjective
      (ℓ := ℓ) (G := G) (H := H) ψ hψ a)

end

end FoxDifferential
