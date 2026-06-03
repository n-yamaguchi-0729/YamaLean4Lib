import FoxDifferential.Completed.DifferentialModule.Map.Comap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/DifferentialModule/Map/Stage.lean
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

/-- Definition of primePowerCompletedGroupAlgebraMapStage. -/
def primePowerCompletedGroupAlgebraMapStage
    (ψ : ContinuousMonoidHom G H) (i : PrimePowerCompletedGroupAlgebraIndex H) :
    PrimePowerCompletedGroupAlgebraStage ℓ G
        (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) →+*
      PrimePowerCompletedGroupAlgebraStage ℓ H i :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff (ℓ ^ i.1))
    (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ i.2)

/-- Evaluation formula for primePowerCompletedGroupAlgebraMapStage_of. -/
@[simp]
theorem primePowerCompletedGroupAlgebraMapStage_of
    (ψ : ContinuousMonoidHom G H) (i : PrimePowerCompletedGroupAlgebraIndex H)
    (q : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G
      (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)) :
    primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1)) _ q) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1)) _
        (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ i.2 q) := by
  simp only [primePowerCompletedGroupAlgebraMapStage, MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk,
  OneHom.coe_mk, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]


/-- The finite-stage component of the completed group-algebra map sends arbitrary group-ring
basis coefficients by the pulled-back quotient map. -/
theorem primePowerCompletedGroupAlgebraMapStage_single
    (ψ : ContinuousMonoidHom G H) (i : PrimePowerCompletedGroupAlgebraIndex H)
    (q : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G
      (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2))
    (a : ModNCompletedCoeff (ℓ ^ i.1)) :
    primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ i.2 q) a := by
  simp only [primePowerCompletedGroupAlgebraMapStage, MonoidAlgebra.single,
  MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]

/-- If `ψ : G → H` is surjective, then every finite-stage group-algebra component of the
completed map is surjective. -/
theorem primePowerCompletedGroupAlgebraMapStage_surjective
    (ψ : ContinuousMonoidHom G H) (hψ : Function.Surjective ψ)
    (i : PrimePowerCompletedGroupAlgebraIndex H) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i) := by
  intro x
  induction x using Finsupp.induction with
  | zero =>
      exact ⟨0, by simp only [map_zero]⟩
  | single_add q a x _ _ ih =>
      rcases completedGroupAlgebraComapQuotientMap_surjective
          (G := G) (H := H) ψ hψ i.2 q with
        ⟨q', hq'⟩
      rcases ih with ⟨y, hy⟩
      refine ⟨(MonoidAlgebra.single q' a :
          PrimePowerCompletedGroupAlgebraStage ℓ G
            (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)) + y, ?_⟩
      change primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
          ((MonoidAlgebra.single q' a :
              PrimePowerCompletedGroupAlgebraStage ℓ G
                (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)) + y) =
        (show PrimePowerCompletedGroupAlgebraStage ℓ H i from MonoidAlgebra.single q a) +
          (show PrimePowerCompletedGroupAlgebraStage ℓ H i from x)
      calc
        primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
            ((MonoidAlgebra.single q' a :
                PrimePowerCompletedGroupAlgebraStage ℓ G
                  (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)) + y)
          =
            (show PrimePowerCompletedGroupAlgebraStage ℓ H i from
              MonoidAlgebra.single
                (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ i.2 q') a) +
            (show PrimePowerCompletedGroupAlgebraStage ℓ H i from
              primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i y) := by
              rw [map_add, primePowerCompletedGroupAlgebraMapStage_single]
        _ =
            (show PrimePowerCompletedGroupAlgebraStage ℓ H i from MonoidAlgebra.single q a) +
            (show PrimePowerCompletedGroupAlgebraStage ℓ H i from x) := by
              rw [hq', hy]

/-- The finite-stage component of a completed group-algebra map preserves augmentation. -/
theorem primePowerCompletedGroupAlgebraMapStage_augmentation
    (ψ : ContinuousMonoidHom G H) (i : PrimePowerCompletedGroupAlgebraIndex H)
    (x : PrimePowerCompletedGroupAlgebraStage ℓ G
      (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)) :
    modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) H i.2
        (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i x) =
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G
        (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) x := by
  let leftMap :
      PrimePowerCompletedGroupAlgebraStage ℓ G
          (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) →+*
        ModNCompletedCoeff (ℓ ^ i.1) :=
    (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) H i.2).comp
      (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i)
  let rightMap :
      PrimePowerCompletedGroupAlgebraStage ℓ G
          (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) →+*
        ModNCompletedCoeff (ℓ ^ i.1) :=
    modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G
      (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)
  change leftMap x = rightMap x
  have hmaps : leftMap = rightMap := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      rcases ZMod.intCast_surjective r with ⟨t, rfl⟩
      simp only [modNCompletedGroupAlgebraStageAugmentation, primePowerCompletedGroupAlgebraMapStage,
  MonoidAlgebra.mapDomainRingHom, RingHom.coe_comp, RingHom.coe_coe, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
  Function.comp_apply, Finsupp.mapDomain_single, map_one, MonoidAlgebra.lift_single, smul_eq_mul,
  mul_one, leftMap, rightMap]
    · intro q
      change leftMap
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1))
            (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G
              (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)) q) =
        rightMap
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1))
            (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G
              (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)) q)
      dsimp [leftMap, rightMap]
      have hmap :=
        primePowerCompletedGroupAlgebraMapStage_of
          (ℓ := ℓ) (G := G) (H := H) ψ i q
      rw [show
          modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G
              (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2)
              (MonoidAlgebra.single q (1 : ModNCompletedCoeff (ℓ ^ i.1))) = 1 by
        simpa [MonoidAlgebra.of, MonoidAlgebra.single] using
          (modNCompletedGroupAlgebraStageAugmentation_of
            (n := ℓ ^ i.1) (G := G)
            (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) q)]
      calc
        modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) H i.2
            (primePowerCompletedGroupAlgebraMapStage
              (ℓ := ℓ) (G := G) (H := H) ψ i (MonoidAlgebra.single q 1))
          =
            modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) H i.2
              (MonoidAlgebra.single
                (completedGroupAlgebraComapQuotientMap
                  (G := G) (H := H) ψ i.2 q) 1) := by
              simpa [MonoidAlgebra.of, MonoidAlgebra.single] using
                congrArg (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) H i.2) hmap
        _ = 1 := by
          simpa [MonoidAlgebra.of, MonoidAlgebra.single] using
            (modNCompletedGroupAlgebraStageAugmentation_of
              (n := ℓ ^ i.1) (G := H) i.2
              (completedGroupAlgebraComapQuotientMap
                (G := G) (H := H) ψ i.2 q))
  rw [hmaps]

/-- Compatibility lemma primePowerCompletedGroupAlgebraMapStage_compatible. -/
theorem primePowerCompletedGroupAlgebraMapStage_compatible
    (ψ : ContinuousMonoidHom G H) {i j : PrimePowerCompletedGroupAlgebraIndex H} (hij : i ≤ j) :
    (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := H) hij).comp
        (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ j) =
      (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i).comp
        (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G)
          (show
            (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) ≤
              (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2) from
            ⟨hij.1, completedGroupAlgebraComapIndex_mono (G := G) (H := H) ψ hij.2⟩)) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := H) hij).comp
          (primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ j)) x =
        ((primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i).comp
          (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G)
            (show
              (i.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2) ≤
                (j.1, completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2) from
              ⟨hij.1,
                completedGroupAlgebraComapIndex_mono (G := G) (H := H) ψ hij.2⟩))) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, RingHom.comp_apply,
      primePowerCompletedGroupAlgebraMapStage_of,
      primePowerCompletedGroupAlgebraTransition_of,
      primePowerCompletedGroupAlgebraTransition_of]
    change
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1))
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2)
          ((OpenNormalSubgroupInClass.map
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := H)
            (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2)
            (completedGroupAlgebraComapQuotientMap (G := G) (H := H) ψ j.2 q)) =
        primePowerCompletedGroupAlgebraMapStage (ℓ := ℓ) (G := G) (H := H) ψ i
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1))
            (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G
              (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2))
            ((OpenNormalSubgroupInClass.map
              (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
              (U := OrderDual.ofDual
                (completedGroupAlgebraComapIndex (G := G) (H := H) ψ i.2))
              (V := OrderDual.ofDual
                (completedGroupAlgebraComapIndex (G := G) (H := H) ψ j.2))
              (completedGroupAlgebraComapIndex_mono (G := G) (H := H) ψ hij.2)) q))
    rw [primePowerCompletedGroupAlgebraMapStage_of]
    exact congrArg (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ i.1))
      (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2))
      (congrFun
        (congrArg DFunLike.coe
          (completedGroupAlgebraComapQuotientMap_compatible
            (G := G) (H := H) ψ hij.2)) q)
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [primePowerCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraStageCoeffMap,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, primePowerCompletedGroupAlgebraMapStage, map_intCast,
  RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, MonoidAlgebra.mapDomainRingHom_apply]

end

end FoxDifferential
