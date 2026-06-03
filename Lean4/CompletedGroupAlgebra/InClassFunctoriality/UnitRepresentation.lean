import CompletedGroupAlgebra.InClassFunctoriality.Comparison

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/InClassFunctoriality/UnitRepresentation.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Functoriality of completed group algebras

The completed group algebra is presented as an inverse limit of finite group algebras, together with canonical augmentation, augmentation ideal, finite-stage maps, functoriality, and profinite module universal properties.
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
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The concrete class-indexed unit representation evaluates to the corresponding completed group-like element. -/
@[simp]
theorem completedGroupAlgebraUnitRepresentationInClassConcrete_val
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (g : G) :
    ((completedGroupAlgebraUnitRepresentation R G (CompletedGroupAlgebraInClass C hC R G)
        (toCompletedGroupAlgebraInClassRingHom C hC R G) g :
        (CompletedGroupAlgebraInClass C hC R G)ˣ) : CompletedGroupAlgebraInClass C hC R G) =
      completedGroupAlgebraOfInClass C hC R G g :=
  rfl

/-- The `C`-indexed canonical unit representation is continuous after forgetting to
`[[R G]]_C`. -/
theorem continuous_completedGroupAlgebraUnitRepresentationInClassConcrete_val
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    Continuous fun g : G =>
      ((completedGroupAlgebraUnitRepresentation R G (CompletedGroupAlgebraInClass C hC R G)
        (toCompletedGroupAlgebraInClassRingHom C hC R G) g :
        (CompletedGroupAlgebraInClass C hC R G)ˣ) : CompletedGroupAlgebraInClass C hC R G) := by
  simpa using continuous_completedGroupAlgebraOfInClass (R := R) (G := G) C hC

/-- The dense abstract map lands in the span of class-indexed completed group-like elements. -/
theorem toCompletedGroupAlgebraInClassRingHom_mem_span_completedGroupAlgebraOfInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraInClassRingHom C hC R G x ∈
      Submodule.span R (Set.range (completedGroupAlgebraOfInClass C hC R G)) := by
  classical
  induction x using Finsupp.induction with
  | zero =>
      rw [show toCompletedGroupAlgebraInClassRingHom C hC R G (0 : MonoidAlgebra R G) =
          (0 : CompletedGroupAlgebraInClass C hC R G) by
        exact map_zero (toCompletedGroupAlgebraInClassRingHom C hC R G)]
      exact Submodule.zero_mem _
  | single_add g r x _ _ ih =>
      rw [map_add]
      refine Submodule.add_mem _ ?_ ih
      have hsingle :
          toCompletedGroupAlgebraInClassRingHom C hC R G (MonoidAlgebra.single g r) =
            r • completedGroupAlgebraOfInClass C hC R G g := by
        rw [show MonoidAlgebra.single g r =
            r • MonoidAlgebra.of R G g by
          simp only [MonoidAlgebra.of, MonoidHom.coe_mk, OneHom.coe_mk, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]]
        change toCompletedGroupAlgebraInClass C hC R G (r • MonoidAlgebra.of R G g) =
          r • completedGroupAlgebraOfInClass C hC R G g
        rw [toCompletedGroupAlgebraInClass_smul]
        rfl
      rw [hsingle]
      exact Submodule.smul_mem _ r (Submodule.subset_span ⟨g, rfl⟩)

/-- The `C`-indexed completed group-like elements topologically generate `[[R G]]_C` as an
`R`-module, for pro-`C` groups and formation classes. -/
theorem completedGroupAlgebraOfInClass_dense_span
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    closure (Submodule.span R (Set.range (completedGroupAlgebraOfInClass C hC R G)) :
      Set (CompletedGroupAlgebraInClass C hC R G)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro y
  have hy :
      y ∈ closure (Set.range (toCompletedGroupAlgebraInClassRingHom C hC R G)) := by
    have hdense : DenseRange (toCompletedGroupAlgebraInClassRingHom C hC R G) := by
      change DenseRange (toCompletedGroupAlgebraInClass C hC R G)
      exact denseRange_toCompletedGroupAlgebraInClass (R := R) (G := G) C hC hForm hG
    rw [hdense.closure_range]
    exact Set.mem_univ y
  exact closure_mono (by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    exact toCompletedGroupAlgebraInClassRingHom_mem_span_completedGroupAlgebraOfInClass
      (R := R) (G := G) C hC x) hy

/-- A continuous module over the `C`-indexed completed group algebra inherits the natural
continuous `G`-module structure via the group-like units. -/
theorem completedGroupAlgebraInClass_module_induces_continuous_gmodule
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (A : Type (max u v)) [AddCommGroup A] [TopologicalSpace A]
    [Module (CompletedGroupAlgebraInClass C hC R G) A]
    [ContinuousSMul (CompletedGroupAlgebraInClass C hC R G) A] :
    letI : DistribMulAction G A :=
      unitRepresentationDistribMulAction G (CompletedGroupAlgebraInClass C hC R G) A
        (completedGroupAlgebraUnitRepresentation R G (CompletedGroupAlgebraInClass C hC R G) (toCompletedGroupAlgebraInClassRingHom C hC R G))
    ContinuousSMul G A := by
  exact unitRepresentation_continuousSMul G (CompletedGroupAlgebraInClass C hC R G) A
    (completedGroupAlgebraUnitRepresentation R G (CompletedGroupAlgebraInClass C hC R G) (toCompletedGroupAlgebraInClassRingHom C hC R G))
    (continuous_completedGroupAlgebraUnitRepresentationInClassConcrete_val (R := R) (G := G) C hC)

end

end CompletedGroupAlgebra
