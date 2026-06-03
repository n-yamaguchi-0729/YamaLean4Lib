import CompletedGroupAlgebra.Basic.AllFinite.Additive

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Basic/AllFinite/Ring.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Ring and algebra structure

This module builds the ring and algebra structure on the all-finite completed group algebra by coordinatewise operations on finite stages.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

instance instOneCompletedGroupAlgebra : One (Carrier R G) where
  one := ⟨fun U => (1 : CompletedGroupAlgebraStage R G U), by
    intro U V hUV
    change completedGroupAlgebraTransition R G hUV
      (1 : CompletedGroupAlgebraStage R G V) = 1
    exact map_one (completedGroupAlgebraTransition R G hUV)⟩

instance instMulCompletedGroupAlgebra : Mul (Carrier R G) where
  mul x y := ⟨fun U =>
      (show CompletedGroupAlgebraStage R G U from x.1 U) *
        (show CompletedGroupAlgebraStage R G U from y.1 U), by
    intro U V hUV
    calc
      completedGroupAlgebraTransition R G hUV
          ((show CompletedGroupAlgebraStage R G V from x.1 V) *
            (show CompletedGroupAlgebraStage R G V from y.1 V))
          =
        completedGroupAlgebraTransition R G hUV
            (show CompletedGroupAlgebraStage R G V from x.1 V) *
          completedGroupAlgebraTransition R G hUV
            (show CompletedGroupAlgebraStage R G V from y.1 V) := by
            rw [map_mul]
      _ = (show CompletedGroupAlgebraStage R G U from x.1 U) *
            (show CompletedGroupAlgebraStage R G U from y.1 U) := by
            exact congrArg₂ HMul.hMul (x.2 U V hUV) (y.2 U V hUV)⟩

instance instNatCastCompletedGroupAlgebra : NatCast (Carrier R G) where
  natCast n := ⟨fun U => (n : CompletedGroupAlgebraStage R G U), by
    intro U V hUV
    change completedGroupAlgebraTransition R G hUV
      (n : CompletedGroupAlgebraStage R G V) = n
    exact map_natCast (completedGroupAlgebraTransition R G hUV) n⟩

instance instIntCastCompletedGroupAlgebra : IntCast (Carrier R G) where
  intCast n := ⟨fun U => (n : CompletedGroupAlgebraStage R G U), by
    intro U V hUV
    change completedGroupAlgebraTransition R G hUV
      (n : CompletedGroupAlgebraStage R G V) = n
    exact map_intCast (completedGroupAlgebraTransition R G hUV) n⟩

instance instRingCompletedGroupAlgebraStage
    (U : CompletedGroupAlgebraIndex G) :
    Ring ((completedGroupAlgebraSystem R G).X U) := by
  dsimp [completedGroupAlgebraSystem, CompletedGroupAlgebraStage]
  infer_instance

instance instRingCompletedGroupAlgebraFamily :
    Ring ((U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) :=
  inferInstance

instance instPowCompletedGroupAlgebra : Pow (Carrier R G) ℕ where
  pow x n := ⟨fun U => (show CompletedGroupAlgebraStage R G U from x.1 U) ^ n, by
    intro U V hUV
    change completedGroupAlgebraTransition R G hUV
        ((show CompletedGroupAlgebraStage R G V from x.1 V) ^ n) =
      (show CompletedGroupAlgebraStage R G U from x.1 U) ^ n
    rw [map_pow]
    exact congrArg (fun t => t ^ n) (x.2 U V hUV)⟩

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_one_completedGroupAlgebra :
    ((1 : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) = 1 := by
  funext U
  rfl

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_mul_completedGroupAlgebra (x y : Carrier R G) :
    ((x * y : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) =
      x * y := by
  funext U
  rfl

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_natCast_completedGroupAlgebra (n : ℕ) :
    ((n : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) =
      n := by
  funext U
  rfl

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_intCast_completedGroupAlgebra (n : ℤ) :
    ((n : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) =
      n := by
  funext U
  rfl

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_pow_completedGroupAlgebra (x : Carrier R G) (n : ℕ) :
    ((x ^ n : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) =
      x ^ n := by
  funext U
  rfl

instance instRingCompletedGroupAlgebra : Ring (Carrier R G) :=
  Function.Injective.ring
    (fun x : Carrier R G =>
      (x : (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U))
    Subtype.val_injective
    (coe_zero_completedGroupAlgebra (R := R) (G := G))
    (coe_one_completedGroupAlgebra (R := R) (G := G))
    (coe_add_completedGroupAlgebra (R := R) (G := G))
    (coe_mul_completedGroupAlgebra (R := R) (G := G))
    (coe_neg_completedGroupAlgebra (R := R) (G := G))
    (coe_sub_completedGroupAlgebra (R := R) (G := G))
    (fun n x => coe_nsmul_completedGroupAlgebra (R := R) (G := G) n x)
    (fun n x => coe_zsmul_completedGroupAlgebra (R := R) (G := G) n x)
    (fun x n => coe_pow_completedGroupAlgebra (R := R) (G := G) x n)
    (by intro n; exact coe_natCast_completedGroupAlgebra (R := R) (G := G) n)
    (by intro n; exact coe_intCast_completedGroupAlgebra (R := R) (G := G) n)

/-- Change coefficients on the all-finite completed group algebra stagewise. -/
def completedGroupAlgebraCoeffMap
    (S : Type w) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) :
    Carrier R G →+* Carrier S G where
  toFun x := ⟨fun U => completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U (x.1 U), by
    intro U V hUV
    have hcompat := congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraStageCoeffMap_compatible
          (R := R) (G := G) S f hUV))
      (x.1 V)
    calc
      completedGroupAlgebraTransition S G hUV
          (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f V (x.1 V))
          =
        completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U
          (completedGroupAlgebraTransition R G hUV (x.1 V)) := hcompat.symm
      _ =
        completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U (x.1 U) := by
          exact congrArg (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U)
            (x.2 U V hUV)⟩
  map_zero' := by
    apply Subtype.ext
    funext U
    exact map_zero (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U)
  map_one' := by
    apply Subtype.ext
    funext U
    exact map_one (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U)
  map_add' x y := by
    apply Subtype.ext
    funext U
    exact map_add (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U) (x.1 U) (y.1 U)
  map_mul' x y := by
    apply Subtype.ext
    funext U
    exact map_mul (completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U) (x.1 U) (y.1 U)

@[simp]
theorem completedGroupAlgebraProjection_coeffMap
    (S : Type w) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (f : R →+* S) (U : CompletedGroupAlgebraIndex G)
    (x : Carrier R G) :
    completedGroupAlgebraProjection S G U
        (completedGroupAlgebraCoeffMap (R := R) (G := G) S f x) =
      completedGroupAlgebraStageCoeffMap (R := R) (G := G) S f U
        (completedGroupAlgebraProjection R G U x) :=
  rfl

/-- The finite-stage projection preserves zero. -/
@[simp]
theorem completedGroupAlgebraProjection_zero (U : CompletedGroupAlgebraIndex G) :
    completedGroupAlgebraProjection R G U (0 : Carrier R G) = 0 := rfl

/-- The finite-stage projection preserves add. -/
@[simp]
theorem completedGroupAlgebraProjection_add (U : CompletedGroupAlgebraIndex G)
    (x y : Carrier R G) :
    completedGroupAlgebraProjection R G U (x + y) =
      completedGroupAlgebraProjection R G U x + completedGroupAlgebraProjection R G U y := rfl

/-- The finite-stage projection preserves smul. -/
@[simp]
theorem completedGroupAlgebraProjection_smul (U : CompletedGroupAlgebraIndex G)
    (r : R) (x : Carrier R G) :
    completedGroupAlgebraProjection R G U (r • x) =
      r • completedGroupAlgebraProjection R G U x := rfl

/-- The finite-stage projection preserves one. -/
@[simp]
theorem completedGroupAlgebraProjection_one (U : CompletedGroupAlgebraIndex G) :
    completedGroupAlgebraProjection R G U (1 : Carrier R G) = 1 := rfl

/-- The finite-stage projection preserves mul. -/
@[simp]
theorem completedGroupAlgebraProjection_mul (U : CompletedGroupAlgebraIndex G)
    (x y : Carrier R G) :
    completedGroupAlgebraProjection R G U (x * y) =
      completedGroupAlgebraProjection R G U x * completedGroupAlgebraProjection R G U y := rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Transition maps preserve coefficient algebra-map elements. -/
theorem completedGroupAlgebraTransition_algebraMap
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) (r : R) :
    completedGroupAlgebraTransition R G hUV
        (algebraMap R (CompletedGroupAlgebraStage R G V) r) =
      algebraMap R (CompletedGroupAlgebraStage R G U) r := by
  simp only [completedGroupAlgebraTransition, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one]

/-- The coefficient-ring map into the completed group algebra. -/
def completedGroupAlgebraAlgebraMap (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : R →+* Carrier R G where
  toFun r := ⟨fun U => algebraMap R (CompletedGroupAlgebraStage R G U) r, by
    intro U V hUV
    exact completedGroupAlgebraTransition_algebraMap (R := R) (G := G) hUV r⟩
  map_zero' := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change algebraMap R (CompletedGroupAlgebraStage R G U) (0 : R) = 0
    exact map_zero (algebraMap R (CompletedGroupAlgebraStage R G U))
  map_one' := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change algebraMap R (CompletedGroupAlgebraStage R G U) (1 : R) = 1
    exact map_one (algebraMap R (CompletedGroupAlgebraStage R G U))
  map_add' r s := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change algebraMap R (CompletedGroupAlgebraStage R G U) (r + s) =
      algebraMap R (CompletedGroupAlgebraStage R G U) r +
        algebraMap R (CompletedGroupAlgebraStage R G U) s
    exact map_add (algebraMap R (CompletedGroupAlgebraStage R G U)) r s
  map_mul' r s := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change algebraMap R (CompletedGroupAlgebraStage R G U) (r * s) =
      algebraMap R (CompletedGroupAlgebraStage R G U) r *
        algebraMap R (CompletedGroupAlgebraStage R G U) s
    exact map_mul (algebraMap R (CompletedGroupAlgebraStage R G U)) r s

instance instAlgebraCompletedGroupAlgebra : Algebra R (Carrier R G) where
  algebraMap := completedGroupAlgebraAlgebraMap R G
  commutes' := by
    intro r x
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change algebraMap R (CompletedGroupAlgebraStage R G U) r *
        completedGroupAlgebraProjection R G U x =
      completedGroupAlgebraProjection R G U x *
        algebraMap R (CompletedGroupAlgebraStage R G U) r
    exact Algebra.commutes r (completedGroupAlgebraProjection R G U x)
  smul_def' := by
    intro r x
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change completedGroupAlgebraProjection R G U (r • x) =
      completedGroupAlgebraProjection R G U (completedGroupAlgebraAlgebraMap R G r * x)
    rw [completedGroupAlgebraProjection_smul, completedGroupAlgebraProjection_mul]
    change r • completedGroupAlgebraProjection R G U x =
      algebraMap R (CompletedGroupAlgebraStage R G U) r *
        completedGroupAlgebraProjection R G U x
    rw [Algebra.smul_def]

end

end CompletedGroupAlgebra
