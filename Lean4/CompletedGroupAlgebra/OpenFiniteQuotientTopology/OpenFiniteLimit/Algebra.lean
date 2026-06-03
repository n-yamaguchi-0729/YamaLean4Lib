import CompletedGroupAlgebra.OpenFiniteQuotientTopology.OpenFiniteLimit.System

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/OpenFiniteQuotientTopology/OpenFiniteLimit/Algebra.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Algebra on the open finite quotient limit
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v

variable (R : Type u) [CommRing R] [TopologicalSpace R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance instZeroCompletedGroupAlgebraOpenFiniteQuotientLimit :
    Zero (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  zero := ⟨fun K => (0 : CompletedGroupAlgebraOpenFiniteQuotientStage R G K), by
    intro K L hKL
    change completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
      (0 : CompletedGroupAlgebraOpenFiniteQuotientStage R G L) = 0
    exact map_zero (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL)⟩

instance instAddCompletedGroupAlgebraOpenFiniteQuotientLimit :
    Add (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  add x y := ⟨fun K =>
      (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K) +
        (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from y.1 K), by
    intro K L hKL
    calc
      completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
          ((show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from x.1 L) +
            (show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from y.1 L))
          =
        completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
            (show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from x.1 L) +
          completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
            (show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from y.1 L) := by
            rw [map_add]
      _ = (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K) +
            (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from y.1 K) := by
            exact congrArg₂ HAdd.hAdd (x.2 K L hKL) (y.2 K L hKL)⟩

instance instNegCompletedGroupAlgebraOpenFiniteQuotientLimit :
    Neg (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  neg x := ⟨fun K => -(show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K), by
    intro K L hKL
    change completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
        (-(show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from x.1 L)) =
      -(show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 K L hKL)⟩

instance instSubCompletedGroupAlgebraOpenFiniteQuotientLimit :
    Sub (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  sub x y := ⟨fun K =>
      (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K) -
        (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from y.1 K), by
    intro K L hKL
    change completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
        ((show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from x.1 L) -
          (show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from y.1 L)) =
      (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K) -
        (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from y.1 K)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 K L hKL) (y.2 K L hKL)⟩

instance instSMulNatCompletedGroupAlgebraOpenFiniteQuotientLimit :
    SMul ℕ (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  smul n x := ⟨fun K => n • (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K), by
    intro K L hKL
    change completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
        (n • (show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from x.1 L)) =
      n • (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K)
    rw [map_nsmul]
    exact congrArg (n • ·) (x.2 K L hKL)⟩

instance instSMulIntCompletedGroupAlgebraOpenFiniteQuotientLimit :
    SMul ℤ (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  smul n x := ⟨fun K => n • (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K), by
    intro K L hKL
    change completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
        (n • (show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from x.1 L)) =
      n • (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K)
    rw [map_zsmul]
    exact congrArg (n • ·) (x.2 K L hKL)⟩

instance instAddCommGroupCompletedGroupAlgebraOpenFiniteQuotientStage
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    AddCommGroup ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := by
  dsimp [completedGroupAlgebraOpenFiniteQuotientSystem,
    CompletedGroupAlgebraOpenFiniteQuotientStage, CompletedGroupAlgebraCoeffQuotientStage]
  infer_instance

instance instAddCommGroupCompletedGroupAlgebraOpenFiniteQuotientFamily :
    AddCommGroup
      ((K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) :=
  inferInstance

/-- The coercion of zero in the open finite quotient limit is the zero family. -/
@[simp]
theorem coe_zero_completedGroupAlgebraOpenFiniteQuotientLimit :
    ((0 : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) = 0 := by
  funext K
  rfl

/-- The coercion of a sum in the open finite quotient limit is computed coordinatewise. -/
@[simp]
theorem coe_add_completedGroupAlgebraOpenFiniteQuotientLimit
    (x y : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    ((x + y : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) =
      x + y := by
  funext K
  rfl

/-- The coercion of a negation in the open finite quotient limit is computed coordinatewise. -/
@[simp]
theorem coe_neg_completedGroupAlgebraOpenFiniteQuotientLimit
    (x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    ((-x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) =
      -x := by
  funext K
  rfl

/-- The coercion of a subtraction in the open finite quotient limit is computed coordinatewise. -/
@[simp]
theorem coe_sub_completedGroupAlgebraOpenFiniteQuotientLimit
    (x y : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    ((x - y : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) =
      x - y := by
  funext K
  rfl

/-- The coercion of a natural scalar multiple in the open finite quotient limit is coordinatewise. -/
@[simp]
theorem coe_nsmul_completedGroupAlgebraOpenFiniteQuotientLimit
    (n : ℕ) (x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    ((n • x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) =
      n • x := by
  funext K
  rfl

/-- The coercion of an integer scalar multiple in the open finite quotient limit is coordinatewise. -/
@[simp]
theorem coe_zsmul_completedGroupAlgebraOpenFiniteQuotientLimit
    (n : ℤ) (x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    ((n • x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) =
      n • x := by
  funext K
  rfl

instance instAddCommGroupCompletedGroupAlgebraOpenFiniteQuotientLimit :
    AddCommGroup (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
  Function.Injective.addCommGroup
    (fun x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G =>
      (x : (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K))
    Subtype.val_injective
    (coe_zero_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G))
    (coe_add_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G))
    (coe_neg_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G))
    (coe_sub_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G))
    (fun x n => coe_nsmul_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G) n x)
    (fun x n => coe_zsmul_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G) n x)

instance instOneCompletedGroupAlgebraOpenFiniteQuotientLimit :
    One (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  one := ⟨fun K => (1 : CompletedGroupAlgebraOpenFiniteQuotientStage R G K), by
    intro K L hKL
    change completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
      (1 : CompletedGroupAlgebraOpenFiniteQuotientStage R G L) = 1
    exact map_one (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL)⟩

instance instMulCompletedGroupAlgebraOpenFiniteQuotientLimit :
    Mul (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  mul x y := ⟨fun K =>
      (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K) *
        (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from y.1 K), by
    intro K L hKL
    calc
      completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
          ((show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from x.1 L) *
            (show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from y.1 L))
          =
        completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
            (show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from x.1 L) *
          completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
            (show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from y.1 L) := by
            rw [map_mul]
      _ = (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K) *
            (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from y.1 K) := by
            exact congrArg₂ HMul.hMul (x.2 K L hKL) (y.2 K L hKL)⟩

instance instNatCastCompletedGroupAlgebraOpenFiniteQuotientLimit :
    NatCast (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  natCast n := ⟨fun K => (n : CompletedGroupAlgebraOpenFiniteQuotientStage R G K), by
    intro K L hKL
    change completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
      (n : CompletedGroupAlgebraOpenFiniteQuotientStage R G L) = n
    exact map_natCast (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL) n⟩

instance instIntCastCompletedGroupAlgebraOpenFiniteQuotientLimit :
    IntCast (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) where
  intCast n := ⟨fun K => (n : CompletedGroupAlgebraOpenFiniteQuotientStage R G K), by
    intro K L hKL
    change completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
      (n : CompletedGroupAlgebraOpenFiniteQuotientStage R G L) = n
    exact map_intCast (completedGroupAlgebraOpenFiniteQuotientTransition R G hKL) n⟩

instance instRingCompletedGroupAlgebraOpenFiniteQuotientStage
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    Ring ((completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) := by
  dsimp [completedGroupAlgebraOpenFiniteQuotientSystem,
    CompletedGroupAlgebraOpenFiniteQuotientStage, CompletedGroupAlgebraCoeffQuotientStage]
  infer_instance

instance instRingCompletedGroupAlgebraOpenFiniteQuotientFamily :
    Ring ((K : CompletedGroupAlgebraOpenQuotientIndex R G) →
      (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) :=
  inferInstance

instance instPowCompletedGroupAlgebraOpenFiniteQuotientLimit :
    Pow (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) ℕ where
  pow x n := ⟨fun K => (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K) ^ n, by
    intro K L hKL
    change completedGroupAlgebraOpenFiniteQuotientTransition R G hKL
        ((show CompletedGroupAlgebraOpenFiniteQuotientStage R G L from x.1 L) ^ n) =
      (show CompletedGroupAlgebraOpenFiniteQuotientStage R G K from x.1 K) ^ n
    rw [map_pow]
    exact congrArg (fun t => t ^ n) (x.2 K L hKL)⟩

/-- The coercion of one in the open finite quotient limit is the one family. -/
@[simp]
theorem coe_one_completedGroupAlgebraOpenFiniteQuotientLimit :
    ((1 : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) = 1 := by
  funext K
  rfl

/-- The coercion of a product in the open finite quotient limit is computed coordinatewise. -/
@[simp]
theorem coe_mul_completedGroupAlgebraOpenFiniteQuotientLimit
    (x y : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    ((x * y : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) =
      x * y := by
  funext K
  rfl

/-- Natural-number casts into the open finite quotient limit are computed coordinatewise. -/
@[simp]
theorem coe_natCast_completedGroupAlgebraOpenFiniteQuotientLimit (n : ℕ) :
    ((n : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) =
      n := by
  funext K
  rfl

/-- Integer casts into the open finite quotient limit are computed coordinatewise. -/
@[simp]
theorem coe_intCast_completedGroupAlgebraOpenFiniteQuotientLimit (n : ℤ) :
    ((n : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) =
      n := by
  funext K
  rfl

/-- Powers in the open finite quotient limit are computed coordinatewise. -/
@[simp]
theorem coe_pow_completedGroupAlgebraOpenFiniteQuotientLimit
    (x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) (n : ℕ) :
    ((x ^ n : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
      (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K) =
      x ^ n := by
  funext K
  rfl

instance instRingCompletedGroupAlgebraOpenFiniteQuotientLimit :
    Ring (CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :=
  Function.Injective.ring
    (fun x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G =>
      (x : (K : CompletedGroupAlgebraOpenQuotientIndex R G) →
        (completedGroupAlgebraOpenFiniteQuotientSystem R G).X K))
    Subtype.val_injective
    (coe_zero_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G))
    (coe_one_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G))
    (coe_add_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G))
    (coe_mul_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G))
    (coe_neg_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G))
    (coe_sub_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G))
    (fun n x => coe_nsmul_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G) n x)
    (fun n x => coe_zsmul_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G) n x)
    (fun x n => coe_pow_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G) x n)
    (by intro n; exact coe_natCast_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G) n)
    (by intro n; exact coe_intCast_completedGroupAlgebraOpenFiniteQuotientLimit (R := R) (G := G) n)

/-- Projection from the open finite quotient limit sends zero to zero. -/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_zero
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K
      (0 : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) = 0 := rfl

/-- Projection from the open finite quotient limit preserves addition. -/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_add
    (K : CompletedGroupAlgebraOpenQuotientIndex R G)
    (x y : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K (x + y) =
      completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K x +
        completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K y := rfl

/-- Projection from the open finite quotient limit preserves negation. -/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_neg
    (K : CompletedGroupAlgebraOpenQuotientIndex R G)
    (x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K (-x) =
      -completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K x := rfl

/-- Projection from the open finite quotient limit preserves subtraction. -/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_sub
    (K : CompletedGroupAlgebraOpenQuotientIndex R G)
    (x y : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K (x - y) =
      completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K x -
        completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K y := rfl

/-- Projection from the open finite quotient limit sends one to one. -/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_one
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K
      (1 : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) = 1 := rfl

/-- Projection from the open finite quotient limit preserves multiplication. -/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjection_mul
    (K : CompletedGroupAlgebraOpenQuotientIndex R G)
    (x y : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K (x * y) =
      completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K x *
        completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K y := rfl

/-- Projection from the two-parameter limit to one quotient, as a ring homomorphism. -/
def completedGroupAlgebraOpenFiniteQuotientLimitProjectionRingHom
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G) :
    CompletedGroupAlgebraOpenFiniteQuotientLimit R G →+*
      CompletedGroupAlgebraOpenFiniteQuotientStage R G K where
  toFun := completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K
  map_zero' := completedGroupAlgebraOpenFiniteQuotientLimitProjection_zero (R := R) (G := G) K
  map_one' := completedGroupAlgebraOpenFiniteQuotientLimitProjection_one (R := R) (G := G) K
  map_add' := completedGroupAlgebraOpenFiniteQuotientLimitProjection_add (R := R) (G := G) K
  map_mul' := completedGroupAlgebraOpenFiniteQuotientLimitProjection_mul (R := R) (G := G) K

/-- The projection ring homomorphism has the same underlying function as the projection. -/
@[simp]
theorem completedGroupAlgebraOpenFiniteQuotientLimitProjectionRingHom_apply
    [IsTopologicalRing R]
    (K : CompletedGroupAlgebraOpenQuotientIndex R G)
    (x : CompletedGroupAlgebraOpenFiniteQuotientLimit R G) :
    completedGroupAlgebraOpenFiniteQuotientLimitProjectionRingHom R G K x =
      completedGroupAlgebraOpenFiniteQuotientLimitProjection R G K x :=
  rfl


end

end CompletedGroupAlgebra
