import CompletedGroupAlgebra.AllFiniteAugmentation.StageAugmentation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/AllFiniteAugmentation/CanonicalAugmentation.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed group algebras

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

/-- The value of the completed augmentation, read at a finite stage. -/
def completedGroupAlgebraAugmentationAt (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    Carrier R G → R :=
  fun x => completedGroupAlgebraStageAugmentation R G U (completedGroupAlgebraProjection R G U x)

/-- The coordinate defining the completed augmentation is independent of the chosen sufficiently terminal index. -/
@[simp]
theorem completedGroupAlgebraAugmentationAt_eq_of_le
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) (x : Carrier R G) :
    completedGroupAlgebraAugmentationAt R G U x =
      completedGroupAlgebraAugmentationAt R G V x := by
  unfold completedGroupAlgebraAugmentationAt
  have hcomp := congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageAugmentation_compatible (R := R) (G := G)
        (U := U) (V := V) hUV))
    (completedGroupAlgebraProjection R G V x)
  calc
    completedGroupAlgebraStageAugmentation R G U (completedGroupAlgebraProjection R G U x)
        =
      completedGroupAlgebraStageAugmentation R G U
        (completedGroupAlgebraTransition R G hUV (completedGroupAlgebraProjection R G V x)) := by
          rw [← completedGroupAlgebraProjection_compatible (R := R) (G := G) x hUV]
    _ = completedGroupAlgebraStageAugmentation R G V
        (completedGroupAlgebraProjection R G V x) := hcomp

/-- The canonical augmentation on `[[R G]]`, obtained from the compatible finite-stage
augmentations. This is the fixed-coefficient analogue of the map used in RZ §6.3. -/
def completedGroupAlgebraCanonicalAugmentation (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    Carrier R G →+* R where
  toFun := completedGroupAlgebraAugmentationAt R G (terminalCompletedGroupAlgebraIndex G)
  map_zero' := by
    unfold completedGroupAlgebraAugmentationAt
    simp only [InverseSystem.projection_apply, coe_zero_completedGroupAlgebra, Pi.zero_apply, map_zero]
  map_one' := by
    unfold completedGroupAlgebraAugmentationAt
    simp only [InverseSystem.projection_apply, coe_one_completedGroupAlgebra, Pi.one_apply, map_one]
  map_add' x y := by
    unfold completedGroupAlgebraAugmentationAt
    simp only [InverseSystem.projection_apply, coe_add_completedGroupAlgebra, Pi.add_apply, map_add]
  map_mul' x y := by
    unfold completedGroupAlgebraAugmentationAt
    simp only [InverseSystem.projection_apply, coe_mul_completedGroupAlgebra, Pi.mul_apply, map_mul]

/-- The canonical completed augmentation is computed at any finite stage. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_eq_at
    (U : CompletedGroupAlgebraIndex G) (x : Carrier R G) :
    completedGroupAlgebraCanonicalAugmentation R G x =
      completedGroupAlgebraAugmentationAt R G U x :=
  completedGroupAlgebraAugmentationAt_eq_of_le (R := R) (G := G)
    (U := terminalCompletedGroupAlgebraIndex G) (V := U)
    (terminalCompletedGroupAlgebraIndex_le (G := G) U) x

/-- The completed projection followed by finite-stage augmentation is the canonical augmentation. -/
@[simp]
theorem completedGroupAlgebraStageAugmentation_comp_projectionRingHom
    (U : CompletedGroupAlgebraIndex G) :
    (completedGroupAlgebraStageAugmentation R G U).comp
        (completedGroupAlgebraProjectionRingHom R G U) =
      completedGroupAlgebraCanonicalAugmentation R G := by
  apply RingHom.ext
  intro x
  exact (completedGroupAlgebraCanonicalAugmentation_eq_at (R := R) (G := G) U x).symm

/-- The canonical augmentation extends the abstract group-algebra augmentation through the dense map. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_toCompletedGroupAlgebra
    (x : MonoidAlgebra R G) :
    completedGroupAlgebraCanonicalAugmentation R G (toCompletedGroupAlgebra R G x) =
      groupAlgebraAugmentation R G x := by
  change completedGroupAlgebraStageAugmentation R G (terminalCompletedGroupAlgebraIndex G)
      (completedGroupAlgebraProjection R G (terminalCompletedGroupAlgebraIndex G)
        (toCompletedGroupAlgebra R G x)) = groupAlgebraAugmentation R G x
  rw [completedGroupAlgebraProjection_toCompletedGroupAlgebra]
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageAugmentation_comp_stageMap (R := R) (G := G)
        (terminalCompletedGroupAlgebraIndex G)))
    x

/-- The canonical augmentation composed with the dense map is the abstract augmentation. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_comp_toCompletedGroupAlgebra :
    (completedGroupAlgebraCanonicalAugmentation R G).comp
        (toCompletedGroupAlgebraRingHom R G) =
      groupAlgebraAugmentation R G := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraCanonicalAugmentation_toCompletedGroupAlgebra (R := R) (G := G) x

/-- Canonical augmentation is natural in the coefficient ring. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_comp_coeffMap
    (S : Type w) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) :
    (completedGroupAlgebraCanonicalAugmentation S G).comp
        (completedGroupAlgebraCoeffMap (R := R) (G := G) S f) =
      f.comp (completedGroupAlgebraCanonicalAugmentation R G) := by
  apply RingHom.ext
  intro x
  change
    completedGroupAlgebraStageAugmentation S G (terminalCompletedGroupAlgebraIndex G)
        (completedGroupAlgebraProjection S G (terminalCompletedGroupAlgebraIndex G)
          (completedGroupAlgebraCoeffMap (R := R) (G := G) S f x)) =
      f (completedGroupAlgebraStageAugmentation R G (terminalCompletedGroupAlgebraIndex G)
        (completedGroupAlgebraProjection R G (terminalCompletedGroupAlgebraIndex G) x))
  rw [completedGroupAlgebraProjection_coeffMap]
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageAugmentation_comp_stageCoeffMap
        (R := R) (G := G) S f (terminalCompletedGroupAlgebraIndex G)))
    (completedGroupAlgebraProjection R G (terminalCompletedGroupAlgebraIndex G) x)

/-- Canonical augmentation is natural with respect to functorial completed group-algebra maps. -/
@[simp 900]
theorem completedGroupAlgebraCanonicalAugmentation_map
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ)
    (x : Carrier R G) :
    completedGroupAlgebraCanonicalAugmentation R H
        (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ x) =
      completedGroupAlgebraCanonicalAugmentation R G x := by
  let V : CompletedGroupAlgebraIndex H := terminalCompletedGroupAlgebraIndex H
  calc
    completedGroupAlgebraCanonicalAugmentation R H
        (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ x)
        =
      completedGroupAlgebraAugmentationAt R H V
        (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ x) := by
          exact completedGroupAlgebraCanonicalAugmentation_eq_at (R := R) (G := H) V
            (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ x)
    _ =
      completedGroupAlgebraStageAugmentation R H V
        (completedGroupAlgebraFunctorialStageMap (G := G) (H := H) (R := R) hG φ hφ V
          (completedGroupAlgebraProjection R G
            (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) x)) := by
          rw [completedGroupAlgebraAugmentationAt, completedGroupAlgebraProjection_map]
    _ =
      completedGroupAlgebraStageAugmentation R G
        (completedGroupAlgebraComapIndex (G := G) hG φ hφ V)
        (completedGroupAlgebraProjection R G
          (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) x) := by
          have hstage := congrFun
            (congrArg DFunLike.coe
              (completedGroupAlgebraStageAugmentation_comp_functorialStageMap
                (R := R) (G := G) (H := H) hG φ hφ V))
            (completedGroupAlgebraProjection R G
              (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) x)
          exact hstage
    _ =
      completedGroupAlgebraCanonicalAugmentation R G x := by
          exact (completedGroupAlgebraCanonicalAugmentation_eq_at (R := R) (G := G)
            (completedGroupAlgebraComapIndex (G := G) hG φ hφ V) x).symm

/-- Canonical augmentation after a functorial completed map agrees with canonical augmentation. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_comp_map
    (hG : ProCGroups.IsProfiniteGroup G) (φ : G →* H) (hφ : Continuous φ) :
    (completedGroupAlgebraCanonicalAugmentation R H).comp
        (completedGroupAlgebraMap (G := G) (H := H) R hG φ hφ) =
      completedGroupAlgebraCanonicalAugmentation R G := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraCanonicalAugmentation_map (R := R) (G := G) (H := H) hG φ hφ x

/-- The canonical augmentation sends every completed group-like element to one. -/
@[simp]
theorem completedGroupAlgebraCanonicalAugmentation_of (g : G) :
    completedGroupAlgebraCanonicalAugmentation R G (completedGroupAlgebraOf R G g) = 1 := by
  rw [completedGroupAlgebraOf,
    completedGroupAlgebraCanonicalAugmentation_toCompletedGroupAlgebra]
  simp only [MonoidAlgebra.of_apply, groupAlgebraAugmentation_single]

/-- The canonical completed augmentation is surjective. -/
theorem completedGroupAlgebraCanonicalAugmentation_surjective :
    Function.Surjective (completedGroupAlgebraCanonicalAugmentation R G) := by
  intro r
  refine ⟨toCompletedGroupAlgebra R G (algebraMap R (MonoidAlgebra R G) r), ?_⟩
  rw [completedGroupAlgebraCanonicalAugmentation_toCompletedGroupAlgebra]
  simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq,
  groupAlgebraAugmentation_single]

/-- The canonical completed augmentation is continuous. -/
theorem continuous_completedGroupAlgebraCanonicalAugmentation :
    Continuous (completedGroupAlgebraCanonicalAugmentation R G) := by
  let U := terminalCompletedGroupAlgebraIndex G
  letI : TopologicalSpace (CompletedGroupAlgebraStage R G U) :=
    (completedGroupAlgebraSystem R G).topologicalSpace U
  change Continuous fun x : Carrier R G =>
    completedGroupAlgebraStageAugmentation R G U (completedGroupAlgebraProjection R G U x)
  exact (finiteGroupAlgebra_augmentation_continuous R (CompletedGroupAlgebraQuotient G U)).comp
    ((completedGroupAlgebraSystem R G).continuous_projection U)

end

end CompletedGroupAlgebra
