import CompletedGroupAlgebra.AllFiniteFunctoriality.Map

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/AllFiniteFunctoriality/InClassNaturality.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# In-class comparison naturality for all-finite functoriality
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Continuous ring homomorphisms from the all-finite completed group algebra to a `C`-indexed
completed group algebra are determined by their values on the dense abstract group algebra. -/
theorem completedGroupAlgebraRingHomToInClass_ext_of_comp_toCompleted
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G)
    {f g : Carrier R G →+* CompletedGroupAlgebraInClass C hC R H}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : f.comp (toCompletedGroupAlgebraRingHom R G) =
      g.comp (toCompletedGroupAlgebraRingHom R G)) :
    f = g := by
  letI : T2Space (CompletedGroupAlgebraInClass C hC R H) :=
    completedGroupAlgebraInClass_t2Space (R := R) (G := H) C hC hR
  have hdense : DenseRange (toCompletedGroupAlgebraRingHom R G) :=
    denseRange_toCompletedGroupAlgebraRingHom (R := R) (G := G) hG
  have hcomp : (f : Carrier R G → CompletedGroupAlgebraInClass C hC R H) ∘
        (toCompletedGroupAlgebraRingHom R G) =
      (g : Carrier R G → CompletedGroupAlgebraInClass C hC R H) ∘
        (toCompletedGroupAlgebraRingHom R G) := by
    funext x
    exact congrFun (congrArg DFunLike.coe hfg) x
  have hfun : (f : Carrier R G → CompletedGroupAlgebraInClass C hC R H) = g :=
    DenseRange.equalizer hdense hf hg hcomp
  exact RingHom.ext fun x => congrFun hfun x

/-- Naturality of the comparison from the all-finite completed group algebra to the `C`-indexed
completed group algebra in the group variable. -/
theorem completedGroupAlgebraToInClassRingHom_naturality
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G)
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ).comp
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC) =
      (completedGroupAlgebraToInClassRingHom (R := R) (G := H) C hC).comp
        (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ) := by
  apply completedGroupAlgebraRingHomToInClass_ext_of_comp_toCompleted
    (R := R) (G := G) (H := H) C hC hR hG
  · exact (continuous_completedGroupAlgebraMapInClass (R := R) (G := G) (H := H)
      C hC hHer φ hφ).comp
        (continuous_completedGroupAlgebraToInClass (R := R) (G := G) C hC)
  · exact (continuous_completedGroupAlgebraToInClass (R := R) (G := H) C hC).comp
      (continuous_completedGroupAlgebraMap (R := R) (G := G) (H := H) hG φ hφ)
  · apply RingHom.ext
    intro x
    have htoG := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraToInClass_comp_toCompletedGroupAlgebra
          (R := R) (G := G) C hC))
      x
    have hmapC := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMapInClass_comp_toCompletedGroupAlgebraInClass
          (R := R) (G := G) (H := H) C hC hHer φ hφ))
      x
    have hmapAll := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraMap_comp_toCompletedGroupAlgebra
          (R := R) (G := G) (H := H) hG φ hφ))
      x
    have htoH := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraToInClass_comp_toCompletedGroupAlgebra
          (R := R) (G := H) C hC))
      (MonoidAlgebra.mapDomainRingHom R φ x)
    calc
      ((((completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ).comp
          (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC)).comp
          (toCompletedGroupAlgebraRingHom R G)) x) =
        completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
          ((completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC)
            (toCompletedGroupAlgebraRingHom R G x)) := rfl
      _ =
        completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
          (toCompletedGroupAlgebraInClassRingHom C hC R G x) := by
          exact congrArg (completedGroupAlgebraMapInClass (G := G) (H := H)
            C hC hHer R φ hφ) (by
              exact htoG)
      _ =
        toCompletedGroupAlgebraInClassRingHom C hC R H
          (MonoidAlgebra.mapDomainRingHom R φ x) := by
          simpa [RingHom.comp_apply] using hmapC
      _ =
        completedGroupAlgebraToInClassRingHom (R := R) (G := H) C hC
          (toCompletedGroupAlgebraRingHom R H (MonoidAlgebra.mapDomainRingHom R φ x)) := by
          have htoH' :
              completedGroupAlgebraToInClassRingHom (R := R) (G := H) C hC
                  (toCompletedGroupAlgebraRingHom R H
                    (MonoidAlgebra.mapDomainRingHom R φ x)) =
                toCompletedGroupAlgebraInClassRingHom C hC R H
                  (MonoidAlgebra.mapDomainRingHom R φ x) := by
            exact htoH
          exact htoH'.symm
      _ =
        completedGroupAlgebraToInClassRingHom (R := R) (G := H) C hC
          (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ
            (toCompletedGroupAlgebraRingHom R G x)) := by
          have hmapAll' :
              completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ
                  (toCompletedGroupAlgebraRingHom R G x) =
                toCompletedGroupAlgebraRingHom R H (MonoidAlgebra.mapDomainRingHom R φ x) := by
            exact hmapAll
          exact congrArg (completedGroupAlgebraToInClassRingHom (R := R) (G := H) C hC)
            hmapAll'.symm
      _ =
        ((((completedGroupAlgebraToInClassRingHom (R := R) (G := H) C hC).comp
          (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ)).comp
          (toCompletedGroupAlgebraRingHom R G)) x) := rfl

/-- Algebra-hom form of the naturality of the comparison from the all-finite completed group
algebra to the `C`-indexed completed group algebra. -/
theorem completedGroupAlgebraToInClassAlgHom_naturality
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hR : IsProfiniteRing R) (hG : ProCGroups.IsProfiniteGroup G)
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraMapAlgHomInClass (G := G) (H := H) C hC hHer R φ hφ).comp
        (completedGroupAlgebraToInClassAlgHom (R := R) (G := G) C hC) =
      (completedGroupAlgebraToInClassAlgHom (R := R) (G := H) C hC).comp
        (completedGroupAlgebraMapAlgHom (G := G) (H := H) R hG φ hφ) := by
  apply AlgHom.ext
  intro x
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraToInClassRingHom_naturality
        (R := R) (G := G) (H := H) C hC hHer hR hG φ hφ))
    x
  simpa using h

/-- Naturality of the inverse comparison from the `C`-indexed completed group algebra back to the
all-finite completed group algebra, for pro-`C` groups. -/
theorem completedGroupAlgebraFromInClassRingHom_naturality
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G) (hH : IsProCGroup C H)
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraMap (G := G) (H := H) R hG.1 φ hφ).comp
        (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG) =
      (completedGroupAlgebraFromInClassRingHom (R := R) (G := H) C hC hForm hH).comp
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ) := by
  apply RingHom.ext
  intro x
  rcases completedGroupAlgebraToInClass_surjective (R := R) (G := G) C hC hForm hG x with
    ⟨y, rfl⟩
  have hnat := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraToInClassRingHom_naturality
        (R := R) (G := G) (H := H) C hC hHer hR hG.1 φ hφ))
    y
  calc
    ((completedGroupAlgebraMap (G := G) (H := H) R hG.1 φ hφ).comp
        (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG))
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC y)
        =
      completedGroupAlgebraMap (G := G) (H := H) R hG.1 φ hφ
        (completedGroupAlgebraFromInClass (R := R) (G := G) C hC hForm hG
          (completedGroupAlgebraToInClass (R := R) (G := G) C hC y)) := rfl
    _ =
      completedGroupAlgebraMap (G := G) (H := H) R hG.1 φ hφ y := by
        rw [completedGroupAlgebraFromInClass_toInClass]
    _ =
      completedGroupAlgebraFromInClass (R := R) (G := H) C hC hForm hH
        (completedGroupAlgebraToInClass (R := R) (G := H) C hC
          (completedGroupAlgebraMap (G := G) (H := H) R hG.1 φ hφ y)) := by
        rw [completedGroupAlgebraFromInClass_toInClass]
    _ =
      completedGroupAlgebraFromInClass (R := R) (G := H) C hC hForm hH
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
          (completedGroupAlgebraToInClass (R := R) (G := G) C hC y)) := by
        exact congrArg (completedGroupAlgebraFromInClass (R := R) (G := H) C hC hForm hH)
          hnat.symm
    _ =
      ((completedGroupAlgebraFromInClassRingHom (R := R) (G := H) C hC hForm hH).comp
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ))
        (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC y) := rfl

/-- Algebra-hom form of the naturality of the inverse comparison from the `C`-indexed completed
group algebra back to the all-finite completed group algebra. -/
theorem completedGroupAlgebraFromInClassAlgHom_naturality
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G) (hH : IsProCGroup C H)
    (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraMapAlgHom (G := G) (H := H) R hG.1 φ hφ).comp
        (completedGroupAlgebraFromInClassAlgHom (R := R) (G := G) C hC hForm hG) =
      (completedGroupAlgebraFromInClassAlgHom (R := R) (G := H) C hC hForm hH).comp
        (completedGroupAlgebraMapAlgHomInClass (G := G) (H := H) C hC hHer R φ hφ) := by
  apply AlgHom.ext
  intro x
  have h := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraFromInClassRingHom_naturality
        (R := R) (G := G) (H := H) C hC hHer hForm hR hG hH φ hφ))
    x
  simpa using h

/-- The ring equivalence from all-finite to in-class completions is natural in the group. -/
@[simp]
theorem completedGroupAlgebraInClassRingEquiv_naturality
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G) (hH : IsProCGroup C H)
    (φ : G →* H) (hφ : Continuous φ) (x : Carrier R G) :
    completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ
        (completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hC hForm hG x) =
      completedGroupAlgebraInClassRingEquiv (R := R) (G := H) C hC hForm hH
        (completedGroupAlgebraMap (G := G) (H := H) R hG.1 φ hφ x) := by
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraToInClassRingHom_naturality
        (R := R) (G := G) (H := H) C hC hHer hR hG.1 φ hφ))
    x
  simpa [RingHom.comp_apply] using h

/-- The inverse ring equivalence from in-class to all-finite completions is natural in the group. -/
@[simp]
theorem completedGroupAlgebraInClassRingEquiv_symm_naturality
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G) (hH : IsProCGroup C H)
    (φ : G →* H) (hφ : Continuous φ) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraMap (G := G) (H := H) R hG.1 φ hφ
        ((completedGroupAlgebraInClassRingEquiv (R := R) (G := G) C hC hForm hG).symm x) =
      (completedGroupAlgebraInClassRingEquiv (R := R) (G := H) C hC hForm hH).symm
        (completedGroupAlgebraMapInClass (G := G) (H := H) C hC hHer R φ hφ x) := by
  have h := congrFun
      (congrArg DFunLike.coe
      (completedGroupAlgebraFromInClassRingHom_naturality
        (R := R) (G := G) (H := H) C hC hHer hForm hR hG hH φ hφ))
    x
  simpa [RingHom.comp_apply] using h

/-- The algebra equivalence from all-finite to in-class completions is natural in the group. -/
@[simp]
theorem completedGroupAlgebraInClassAlgEquiv_naturality
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G) (hH : IsProCGroup C H)
    (φ : G →* H) (hφ : Continuous φ) (x : Carrier R G) :
    completedGroupAlgebraMapAlgHomInClass (G := G) (H := H) C hC hHer R φ hφ
        (completedGroupAlgebraInClassAlgEquiv (R := R) (G := G) C hC hForm hG x) =
      completedGroupAlgebraInClassAlgEquiv (R := R) (G := H) C hC hForm hH
        (completedGroupAlgebraMapAlgHom (G := G) (H := H) R hG.1 φ hφ x) := by
  have h := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraToInClassAlgHom_naturality
        (R := R) (G := G) (H := H) C hC hHer hR hG.1 φ hφ))
    x
  simpa using h

/-- The inverse algebra equivalence from in-class to all-finite completions is natural in the group. -/
@[simp]
theorem completedGroupAlgebraInClassAlgEquiv_symm_naturality
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hR : IsProfiniteRing R) (hG : IsProCGroup C G) (hH : IsProCGroup C H)
    (φ : G →* H) (hφ : Continuous φ) (x : CompletedGroupAlgebraInClass C hC R G) :
    completedGroupAlgebraMapAlgHom (G := G) (H := H) R hG.1 φ hφ
        ((completedGroupAlgebraInClassAlgEquiv (R := R) (G := G) C hC hForm hG).symm x) =
      (completedGroupAlgebraInClassAlgEquiv (R := R) (G := H) C hC hForm hH).symm
        (completedGroupAlgebraMapAlgHomInClass (G := G) (H := H) C hC hHer R φ hφ x) := by
  have h := congrFun
      (congrArg DFunLike.coe
      (completedGroupAlgebraFromInClassAlgHom_naturality
        (R := R) (G := G) (H := H) C hC hHer hForm hR hG hH φ hφ))
    x
  simpa using h

end

end CompletedGroupAlgebra
