import CompletedGroupAlgebra.Basic.AllFinite.Stage

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/Basic/AllFinite/Additive.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Additive and module structure

This module constructs the additive and module structures on the all-finite completed group algebra by transporting the finite-stage structures through the inverse limit.
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

/-- The completed group algebra carrier `[[R G]] = lim_U R[G/U]`, as in RZ §5.3. -/
abbrev Carrier (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Type (max u v) :=
  (completedGroupAlgebraSystem R G).inverseLimit

/-- Projection from `[[R G]]` to one finite-stage group algebra `R[G/U]`. -/
abbrev completedGroupAlgebraProjection (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndex G) :
    Carrier R G → CompletedGroupAlgebraStage R G U :=
  (completedGroupAlgebraSystem R G).projection U

instance instZeroCompletedGroupAlgebra : Zero (Carrier R G) where
  zero := ⟨fun U => (0 : CompletedGroupAlgebraStage R G U), by
    intro U V hUV
    change completedGroupAlgebraTransition R G hUV
      (0 : CompletedGroupAlgebraStage R G V) = 0
    exact map_zero (completedGroupAlgebraTransition R G hUV)⟩

instance instAddCompletedGroupAlgebra : Add (Carrier R G) where
  add x y := ⟨fun U =>
      (show CompletedGroupAlgebraStage R G U from x.1 U) +
        (show CompletedGroupAlgebraStage R G U from y.1 U), by
    intro U V hUV
    calc
      completedGroupAlgebraTransition R G hUV
          ((show CompletedGroupAlgebraStage R G V from x.1 V) +
            (show CompletedGroupAlgebraStage R G V from y.1 V))
          =
        completedGroupAlgebraTransition R G hUV
            (show CompletedGroupAlgebraStage R G V from x.1 V) +
          completedGroupAlgebraTransition R G hUV
            (show CompletedGroupAlgebraStage R G V from y.1 V) := by
            rw [map_add]
      _ = (show CompletedGroupAlgebraStage R G U from x.1 U) +
            (show CompletedGroupAlgebraStage R G U from y.1 U) := by
            exact congrArg₂ HAdd.hAdd (x.2 U V hUV) (y.2 U V hUV)⟩

instance instAddZeroClassCompletedGroupAlgebra : AddZeroClass (Carrier R G) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext U
    change (0 : CompletedGroupAlgebraStage R G U) +
        (show CompletedGroupAlgebraStage R G U from x.1 U) =
      (show CompletedGroupAlgebraStage R G U from x.1 U)
    simp only [zero_add]
  add_zero x := by
    apply Subtype.ext
    funext U
    change (show CompletedGroupAlgebraStage R G U from x.1 U) +
        (0 : CompletedGroupAlgebraStage R G U) =
      (show CompletedGroupAlgebraStage R G U from x.1 U)
    simp only [add_zero]

instance instNegCompletedGroupAlgebra : Neg (Carrier R G) where
  neg x := ⟨fun U => -(show CompletedGroupAlgebraStage R G U from x.1 U), by
    intro U V hUV
    change completedGroupAlgebraTransition R G hUV
        (-(show CompletedGroupAlgebraStage R G V from x.1 V)) =
      -(show CompletedGroupAlgebraStage R G U from x.1 U)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 U V hUV)⟩

instance instSubCompletedGroupAlgebra : Sub (Carrier R G) where
  sub x y := ⟨fun U =>
      (show CompletedGroupAlgebraStage R G U from x.1 U) -
        (show CompletedGroupAlgebraStage R G U from y.1 U), by
    intro U V hUV
    change completedGroupAlgebraTransition R G hUV
        ((show CompletedGroupAlgebraStage R G V from x.1 V) -
          (show CompletedGroupAlgebraStage R G V from y.1 V)) =
      (show CompletedGroupAlgebraStage R G U from x.1 U) -
        (show CompletedGroupAlgebraStage R G U from y.1 U)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 U V hUV) (y.2 U V hUV)⟩

instance instSMulNatCompletedGroupAlgebra : SMul ℕ (Carrier R G) where
  smul n x := ⟨fun U => n • (show CompletedGroupAlgebraStage R G U from x.1 U), by
    intro U V hUV
    change completedGroupAlgebraTransition R G hUV
        (n • (show CompletedGroupAlgebraStage R G V from x.1 V)) =
      n • (show CompletedGroupAlgebraStage R G U from x.1 U)
    rw [map_nsmul]
    exact congrArg (n • ·) (x.2 U V hUV)⟩

instance instSMulIntCompletedGroupAlgebra : SMul ℤ (Carrier R G) where
  smul n x := ⟨fun U => n • (show CompletedGroupAlgebraStage R G U from x.1 U), by
    intro U V hUV
    change completedGroupAlgebraTransition R G hUV
        (n • (show CompletedGroupAlgebraStage R G V from x.1 V)) =
      n • (show CompletedGroupAlgebraStage R G U from x.1 U)
    rw [map_zsmul]
    exact congrArg (n • ·) (x.2 U V hUV)⟩

instance instAddCommGroupCompletedGroupAlgebraStage
    (U : CompletedGroupAlgebraIndex G) :
    AddCommGroup ((completedGroupAlgebraSystem R G).X U) := by
  dsimp [completedGroupAlgebraSystem, CompletedGroupAlgebraStage]
  infer_instance

instance instAddCommGroupCompletedGroupAlgebraFamily :
    AddCommGroup
      ((U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) :=
  inferInstance

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_zero_completedGroupAlgebra :
    ((0 : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) = 0 := by
  funext U
  rfl

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_add_completedGroupAlgebra (x y : Carrier R G) :
    ((x + y : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) =
      x + y := by
  funext U
  rfl

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_neg_completedGroupAlgebra (x : Carrier R G) :
    ((-x : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) =
      -x := by
  funext U
  rfl

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_sub_completedGroupAlgebra (x y : Carrier R G) :
    ((x - y : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) =
      x - y := by
  funext U
  rfl

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_nsmul_completedGroupAlgebra (n : ℕ) (x : Carrier R G) :
    ((n • x : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) =
      n • x := by
  funext U
  rfl

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_zsmul_completedGroupAlgebra (n : ℤ) (x : Carrier R G) :
    ((n • x : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) =
      n • x := by
  funext U
  rfl

instance instAddCommGroupCompletedGroupAlgebra : AddCommGroup (Carrier R G) :=
  Function.Injective.addCommGroup
    (fun x : Carrier R G =>
      (x : (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U))
    Subtype.val_injective
    (coe_zero_completedGroupAlgebra (R := R) (G := G))
    (coe_add_completedGroupAlgebra (R := R) (G := G))
    (coe_neg_completedGroupAlgebra (R := R) (G := G))
    (coe_sub_completedGroupAlgebra (R := R) (G := G))
    (fun x n => coe_nsmul_completedGroupAlgebra (R := R) (G := G) n x)
    (fun x n => coe_zsmul_completedGroupAlgebra (R := R) (G := G) n x)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Transition maps commute with coefficient scalar multiplication. -/
theorem completedGroupAlgebraTransition_smul
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V)
    (r : R) (x : CompletedGroupAlgebraStage R G V) :
    completedGroupAlgebraTransition R G hUV (r • x) =
      r • completedGroupAlgebraTransition R G hUV x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  simp only [completedGroupAlgebraTransition, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one]

instance instSMulCoeffCompletedGroupAlgebra : SMul R (Carrier R G) where
  smul r x := ⟨fun U => r • (show CompletedGroupAlgebraStage R G U from x.1 U), by
    intro U V hUV
    change completedGroupAlgebraTransition R G hUV
        (r • (show CompletedGroupAlgebraStage R G V from x.1 V)) =
      r • (show CompletedGroupAlgebraStage R G U from x.1 U)
    rw [completedGroupAlgebraTransition_smul]
    exact congrArg (r • ·) (x.2 U V hUV)⟩

/-- Coordinatewise coercion formula for the inverse-limit completed group algebra. -/
@[simp]
theorem coe_smul_completedGroupAlgebra (r : R) (x : Carrier R G) :
    ((r • x : Carrier R G) :
      (U : CompletedGroupAlgebraIndex G) → (completedGroupAlgebraSystem R G).X U) =
      fun U => r • (show CompletedGroupAlgebraStage R G U from x.1 U) := by
  funext U
  rfl

/-- The coordinatewise additive monoid homomorphism from the completed group algebra. -/
def completedGroupAlgebraValAddMonoidHom :
    Carrier R G →+
      ((U : CompletedGroupAlgebraIndex G) → CompletedGroupAlgebraStage R G U) where
  toFun x := fun U => (show CompletedGroupAlgebraStage R G U from x.1 U)
  map_zero' := by
    funext U
    rfl
  map_add' x y := by
    funext U
    rfl

instance instModuleCoeffCompletedGroupAlgebra : Module R (Carrier R G) :=
  Function.Injective.module R
    (completedGroupAlgebraValAddMonoidHom (R := R) (G := G))
    (fun x y h => by
      apply Subtype.ext
      funext U
      exact congrFun h U)
    (fun r x => by
      funext U
      change (show CompletedGroupAlgebraStage R G U from (r • x).1 U) =
        r • (show CompletedGroupAlgebraStage R G U from x.1 U)
      rfl)

end

end CompletedGroupAlgebra
