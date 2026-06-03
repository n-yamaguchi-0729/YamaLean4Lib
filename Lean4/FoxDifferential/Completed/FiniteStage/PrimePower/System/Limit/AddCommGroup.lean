import FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/PrimePower/System/Limit/AddCommGroup.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Finite-stage completed Fox calculus

Finite quotient stages are used to compare completed Fox boundaries, derivatives, and relation modules with explicit finite group-algebra calculations.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


/-- Zero element of the prime-power finite Fox source inverse limit. -/
instance instZeroFiniteFoxStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    Zero (FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  zero := ⟨fun a => (0 : finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (0 : finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b) = 0
      exact map_zero _⟩

/-- Addition on the prime-power finite Fox source inverse limit. -/
instance instAddFiniteFoxStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    Add (FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  add x y := ⟨fun a =>
      (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) +
        (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          ((show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) +
            (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) +
          (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_add]
      exact congrArg₂ HAdd.hAdd (x.2 a b hab) (y.2 a b hab)⟩

/-- Negation on the prime-power finite Fox source inverse limit. -/
instance instNegFiniteFoxStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    Neg (FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  neg x := ⟨fun a =>
      -(show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (-(show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b)) =
        -(show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_neg]
      exact congrArg Neg.neg (x.2 a b hab)⟩

/-- Subtraction on the prime-power finite Fox source inverse limit. -/
instance instSubFiniteFoxStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    Sub (FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  sub x y := ⟨fun a =>
      (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) -
        (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          ((show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) -
            (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) -
          (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_sub]
      exact congrArg₂ HSub.hSub (x.2 a b hab) (y.2 a b hab)⟩

/-- Natural-number scalar multiplication on the prime-power finite Fox source inverse limit. -/
instance instSMulNatFiniteFoxStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    SMul ℕ (FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  smul m x := ⟨fun a =>
      m • (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (m • (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b)) =
        m • (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_nsmul]
      exact congrArg (m • ·) (x.2 a b hab)⟩

/-- Integer scalar multiplication on the prime-power finite Fox source inverse limit. -/
instance instSMulIntFiniteFoxStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    SMul ℤ (FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) where
  smul m x := ⟨fun a =>
      m • (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (m • (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b)) =
        m • (show finiteFoxStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_zsmul]
      exact congrArg (m • ·) (x.2 a b hab)⟩

omit [DecidableEq X] in
/-- The source-limit family of zero is the zero family. -/
@[simp] theorem finiteFoxStagePrimePowerSourceLimitToFamily_zero
    (N : Subgroup (FreeGroup X)) :
    finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N 0 = 0 := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves addition. -/
@[simp] theorem finiteFoxStagePrimePowerSourceLimitToFamily_add
    (N : Subgroup (FreeGroup X))
    (x y : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (x + y) =
      finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x +
        finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves negation. -/
@[simp] theorem finiteFoxStagePrimePowerSourceLimitToFamily_neg
    (N : Subgroup (FreeGroup X))
    (x : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (-x) =
      -finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves subtraction. -/
@[simp] theorem finiteFoxStagePrimePowerSourceLimitToFamily_sub
    (N : Subgroup (FreeGroup X))
    (x y : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (x - y) =
      finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x -
        finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves natural-number scalar multiplication. -/
@[simp] theorem finiteFoxStagePrimePowerSourceLimitToFamily_nsmul
    (N : Subgroup (FreeGroup X)) (m : ℕ)
    (x : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (m • x) =
      m • finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The source-limit family map preserves integer scalar multiplication. -/
@[simp] theorem finiteFoxStagePrimePowerSourceLimitToFamily_zsmul
    (N : Subgroup (FreeGroup X)) (m : ℤ)
    (x : FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N (m • x) =
      m • finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

/-- Additive commutative group structure on the prime-power finite Fox source inverse limit. -/
instance instAddCommGroupFiniteFoxStagePrimePowerSourceLimit
    (N : Subgroup (FreeGroup X)) :
    AddCommGroup (FiniteFoxStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :=
  Function.Injective.addCommGroup
    (finiteFoxStagePrimePowerSourceLimitToFamily (ℓ := ℓ) (X := X) N)
    (finiteFoxStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N)
    (finiteFoxStagePrimePowerSourceLimitToFamily_zero (ℓ := ℓ) (X := X) N)
    (finiteFoxStagePrimePowerSourceLimitToFamily_add (ℓ := ℓ) (X := X) N)
    (finiteFoxStagePrimePowerSourceLimitToFamily_neg (ℓ := ℓ) (X := X) N)
    (finiteFoxStagePrimePowerSourceLimitToFamily_sub (ℓ := ℓ) (X := X) N)
    (fun z m => finiteFoxStagePrimePowerSourceLimitToFamily_nsmul
      (ℓ := ℓ) (X := X) N m z)
    (fun z m => finiteFoxStagePrimePowerSourceLimitToFamily_zsmul
      (ℓ := ℓ) (X := X) N m z)

/-- Zero element of the prime-power finite Fox target inverse limit. -/
instance instZeroFiniteFoxStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Zero (FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  zero := ⟨fun a => (0 : finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (0 : finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b) = 0
      exact map_zero _⟩

/-- Addition on the prime-power finite Fox target inverse limit. -/
instance instAddFiniteFoxStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Add (FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  add x y := ⟨fun a =>
      (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) +
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          ((show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) +
            (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) +
          (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_add]
      exact congrArg₂ HAdd.hAdd (x.2 a b hab) (y.2 a b hab)⟩

/-- Negation on the prime-power finite Fox target inverse limit. -/
instance instNegFiniteFoxStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Neg (FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  neg x := ⟨fun a =>
      -(show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (-(show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b)) =
        -(show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_neg]
      exact congrArg Neg.neg (x.2 a b hab)⟩

/-- Subtraction on the prime-power finite Fox target inverse limit. -/
instance instSubFiniteFoxStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Sub (FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  sub x y := ⟨fun a =>
      (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) -
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          ((show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b) -
            (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from y.1 b)) =
        (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a) -
          (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from y.1 a)
      rw [map_sub]
      exact congrArg₂ HSub.hSub (x.2 a b hab) (y.2 a b hab)⟩

/-- Natural-number scalar multiplication on the prime-power finite Fox target inverse limit. -/
instance instSMulNatFiniteFoxStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    SMul ℕ (FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  smul m x := ⟨fun a =>
      m • (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (m • (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b)) =
        m • (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_nsmul]
      exact congrArg (m • ·) (x.2 a b hab)⟩

/-- Integer scalar multiplication on the prime-power finite Fox target inverse limit. -/
instance instSMulIntFiniteFoxStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    SMul ℤ (FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) where
  smul m x := ⟨fun a =>
      m • (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a),
    by
      intro a b hab
      change finiteFoxStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (m • (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b from x.1 b)) =
        m • (show finiteFoxStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from x.1 a)
      rw [map_zsmul]
      exact congrArg (m • ·) (x.2 a b hab)⟩

omit [DecidableEq X] in
/-- The target-limit family of zero is the zero family. -/
@[simp] theorem finiteFoxStagePrimePowerTargetLimitToFamily_zero
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N 0 = 0 := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves addition. -/
@[simp] theorem finiteFoxStagePrimePowerTargetLimitToFamily_add
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (x y : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (x + y) =
      finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x +
        finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves negation. -/
@[simp] theorem finiteFoxStagePrimePowerTargetLimitToFamily_neg
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (x : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (-x) =
      -finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves subtraction. -/
@[simp] theorem finiteFoxStagePrimePowerTargetLimitToFamily_sub
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (x y : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (x - y) =
      finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x -
        finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N y := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves natural-number scalar multiplication. -/
@[simp] theorem finiteFoxStagePrimePowerTargetLimitToFamily_nsmul
    (N : Subgroup (FreeGroup X)) [N.Normal] (m : ℕ)
    (x : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (m • x) =
      m • finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

omit [DecidableEq X] in
/-- The target-limit family map preserves integer scalar multiplication. -/
@[simp] theorem finiteFoxStagePrimePowerTargetLimitToFamily_zsmul
    (N : Subgroup (FreeGroup X)) [N.Normal] (m : ℤ)
    (x : FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N (m • x) =
      m • finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N x := by
  funext a
  rfl

/-- Additive commutative group structure on the prime-power finite Fox target inverse limit. -/
instance instAddCommGroupFiniteFoxStagePrimePowerTargetLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    AddCommGroup (FiniteFoxStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :=
  Function.Injective.addCommGroup
    (finiteFoxStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N)
    (finiteFoxStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N)
    (finiteFoxStagePrimePowerTargetLimitToFamily_zero (ℓ := ℓ) (X := X) N)
    (finiteFoxStagePrimePowerTargetLimitToFamily_add (ℓ := ℓ) (X := X) N)
    (finiteFoxStagePrimePowerTargetLimitToFamily_neg (ℓ := ℓ) (X := X) N)
    (finiteFoxStagePrimePowerTargetLimitToFamily_sub (ℓ := ℓ) (X := X) N)
    (fun z m => finiteFoxStagePrimePowerTargetLimitToFamily_nsmul
      (ℓ := ℓ) (X := X) N m z)
    (fun z m => finiteFoxStagePrimePowerTargetLimitToFamily_zsmul
      (ℓ := ℓ) (X := X) N m z)




end

end FoxDifferential
