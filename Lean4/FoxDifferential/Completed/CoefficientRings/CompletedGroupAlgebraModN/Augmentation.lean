import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.System.CompletionMap

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraModN/Augmentation.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed coefficient algebras

Coefficient algebras, residue stages, and completed group-algebra maps are kept as the scalar layer for completed Fox calculus.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u


variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The augmentation on one residue-coefficient finite stage. -/
def modNCompletedGroupAlgebraStageAugmentation (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    ModNCompletedGroupAlgebraStage n G U →+* ModNCompletedCoeff n :=
  MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n)
    (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U)
    (1 : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U →* ModNCompletedCoeff n)

omit [Fact (0 < n)] in
/-- Evaluation formula for modNCompletedGroupAlgebraStageAugmentation_of. -/
@[simp]
theorem modNCompletedGroupAlgebraStageAugmentation_of
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (q : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient G U) :
    modNCompletedGroupAlgebraStageAugmentation n G U
        (MonoidAlgebra.of (ModNCompletedCoeff n) _ q) = 1 := by
  classical
  simp only [modNCompletedGroupAlgebraStageAugmentation, MonoidAlgebra.of, MonoidAlgebra.single,
  MonoidHom.coe_mk, OneHom.coe_mk, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul,
  mul_one]

omit [Fact (0 < n)] in
/-- Compatibility lemma modNCompletedGroupAlgebraStageAugmentation_compatible. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentation_compatible
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (modNCompletedGroupAlgebraStageAugmentation n G U).comp
        (modNCompletedGroupAlgebraTransition n G hUV) =
      modNCompletedGroupAlgebraStageAugmentation n G V := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
          (modNCompletedGroupAlgebraTransition n G hUV)) x =
        modNCompletedGroupAlgebraStageAugmentation n G V x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, modNCompletedGroupAlgebraTransition_of]
    simp only [modNCompletedGroupAlgebraStageAugmentation, MonoidAlgebra.single, RingHom.coe_coe,
  MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one, MonoidAlgebra.of, MonoidHom.coe_mk,
  OneHom.coe_mk]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    have hcoeff :
        ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
            (modNCompletedGroupAlgebraTransition n G hUV))
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupAlgebraStage n G V) a) =
          (modNCompletedGroupAlgebraStageAugmentation n G V)
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupAlgebraStage n G V) a) := by
      simp only [modNCompletedGroupAlgebraStageAugmentation, modNCompletedGroupAlgebraTransition,
  MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq,
  RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one, RingHom.coe_coe,
  MonoidAlgebra.lift_single, smul_eq_mul, mul_one]
    rw [hcoeff]

omit [Fact (0 < n)] in
/-- Composition lemma modNCompletedGroupAlgebraStageAugmentation_comp_stageMap. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentation_comp_stageMap
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    (modNCompletedGroupAlgebraStageAugmentation n G U).comp
        (modNCompletedGroupAlgebraStageMap n G U) =
      MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
        (1 : G →* ModNCompletedCoeff n) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
          (modNCompletedGroupAlgebraStageMap n G U)) x =
        (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
          (1 : G →* ModNCompletedCoeff n)) x)
    x ?_ ?_ ?_
  · intro g
    rw [RingHom.comp_apply, modNCompletedGroupAlgebraStageMap_of]
    simp only [modNCompletedGroupAlgebraStageAugmentation, MonoidAlgebra.of_apply,
      RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul,
      mul_one]
  · intro x y hx hy
    simp only [hx, hy, map_add]
  · intro a x hx
    have hcoeff :
        ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
            (modNCompletedGroupAlgebraStageMap n G U))
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) = a := by
      simp only [modNCompletedGroupAlgebraStageAugmentation, modNCompletedGroupAlgebraStageMap,
  MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq,
  RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one, RingHom.coe_coe,
  MonoidAlgebra.lift_single, smul_eq_mul, mul_one]
    have hcoeff' :
        ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
            (modNCompletedGroupAlgebraStageMap n G U))
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) =
          (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
            (1 : G →* ModNCompletedCoeff n))
            (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) := by
      rw [hcoeff]
      simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq,
  MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]
    rw [Algebra.smul_def]
    calc
      ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
          (modNCompletedGroupAlgebraStageMap n G U))
          ((algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) * x)
        =
          ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
              (modNCompletedGroupAlgebraStageMap n G U))
              (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) *
            ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
              (modNCompletedGroupAlgebraStageMap n G U)) x := by
            rw [RingHom.map_mul]
      _ =
          ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
              (modNCompletedGroupAlgebraStageMap n G U))
              (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) *
            (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
              (1 : G →* ModNCompletedCoeff n)) x := by
            rw [hx]
      _ =
          (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
              (1 : G →* ModNCompletedCoeff n))
              (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) *
            (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
              (1 : G →* ModNCompletedCoeff n)) x := by
            rw [hcoeff']
      _ =
          (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
            (1 : G →* ModNCompletedCoeff n))
            ((algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) * x) := by
            exact
              (map_mul
                (MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
                  (1 : G →* ModNCompletedCoeff n))
                (algebraMap (ModNCompletedCoeff n) (ModNCompletedGroupRing n G) a) x).symm

/-- The augmentation value of a residue-coefficient completed point, read at one finite stage. -/
def modNCompletedGroupAlgebraAugmentationAt (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    ModNCompletedGroupAlgebra n G → ModNCompletedCoeff n :=
  fun x => modNCompletedGroupAlgebraStageAugmentation n G U
    (modNCompletedGroupAlgebraProjection n G U x)

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp 900]
theorem modNCompletedGroupAlgebraAugmentationAt_eq_of_le
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) (x : ModNCompletedGroupAlgebra n G) :
    modNCompletedGroupAlgebraAugmentationAt n G U x =
      modNCompletedGroupAlgebraAugmentationAt n G V x := by
  unfold modNCompletedGroupAlgebraAugmentationAt
  have hcomp := congrFun
    (congrArg DFunLike.coe
      (modNCompletedGroupAlgebraStageAugmentation_compatible
        (n := n) (G := G) (U := U) (V := V) hUV))
    (modNCompletedGroupAlgebraProjection n G V x)
  calc
    modNCompletedGroupAlgebraStageAugmentation n G U
        (modNCompletedGroupAlgebraProjection n G U x)
      =
    modNCompletedGroupAlgebraStageAugmentation n G U
      (modNCompletedGroupAlgebraTransition n G hUV
        (modNCompletedGroupAlgebraProjection n G V x)) := by
          simpa [modNCompletedGroupAlgebraProjection] using
            congrArg (modNCompletedGroupAlgebraStageAugmentation n G U)
              ((modNCompletedGroupAlgebraSystem n G).projection_compatible x U V hUV).symm
    _ = modNCompletedGroupAlgebraStageAugmentation n G V
          (modNCompletedGroupAlgebraProjection n G V x) := by
          exact hcomp

/-- The canonical augmentation on the residue-coefficient completed group algebra. -/
def modNCompletedGroupAlgebraAugmentation :
    ModNCompletedGroupAlgebra n G → ModNCompletedCoeff n :=
  modNCompletedGroupAlgebraAugmentationAt n G (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G)

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem modNCompletedGroupAlgebraAugmentation_eq_at
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (x : ModNCompletedGroupAlgebra n G) :
    modNCompletedGroupAlgebraAugmentation n G x =
      modNCompletedGroupAlgebraAugmentationAt n G U x := by
  exact modNCompletedGroupAlgebraAugmentationAt_eq_of_le
    (n := n) (G := G)
    (U := _root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G) (V := U)
    (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex_le (G := G) U) x

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた augmentation または augmentation ideal への標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem modNCompletedGroupAlgebraAugmentation_toCompleted
    (x : ModNCompletedGroupRing n G) :
    modNCompletedGroupAlgebraAugmentation n G (toModNCompletedGroupAlgebra n G x) =
      MonoidAlgebra.lift (ModNCompletedCoeff n) (ModNCompletedCoeff n) G
        (1 : G →* ModNCompletedCoeff n) x := by
  unfold modNCompletedGroupAlgebraAugmentation modNCompletedGroupAlgebraAugmentationAt
  rw [modNCompletedGroupAlgebraProjection_toCompleted]
  exact congrFun
    (congrArg DFunLike.coe
      (modNCompletedGroupAlgebraStageAugmentation_comp_stageMap
        (n := n) (G := G) (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G)))
    x

end

end FoxDifferential
