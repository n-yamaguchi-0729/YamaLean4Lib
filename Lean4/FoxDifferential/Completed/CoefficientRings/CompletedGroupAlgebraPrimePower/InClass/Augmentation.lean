import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.InClass.System.Ring.Projection

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/InClass/Augmentation.lean
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

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The class-restricted coefficient inverse system `i = (a, U) ↦ ZMod (ℓ^a)`. -/
def primePowerCompletedCoeffSystemInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    InverseSystem (I := PrimePowerCompletedGroupAlgebraIndexInClass G C) where
  X := fun i => ModNCompletedCoeff (ℓ ^ i.1)
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    modNCompletedCoeffMap
      (n := ℓ ^ i.1) (m := ℓ ^ j.1)
      (primePow_dvd_primePow (ℓ := ℓ) hij.1)
  continuous_map := by
    intro i j hij
    letI : TopologicalSpace (ModNCompletedCoeff (ℓ ^ i.1)) := ⊥
    letI : TopologicalSpace (ModNCompletedCoeff (ℓ ^ j.1)) := ⊥
    letI : DiscreteTopology (ModNCompletedCoeff (ℓ ^ j.1)) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedCoeffMap_rfl (n := ℓ ^ i.1))) x
  map_comp := by
    intro i j k hij hjk
    funext x
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    letI : Fact (0 < ℓ ^ k.1) := ⟨primePower_pos ℓ k.1⟩
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedCoeffMap_comp
          (n := ℓ ^ i.1) (m := ℓ ^ j.1) (k := ℓ ^ k.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (primePow_dvd_primePow (ℓ := ℓ) hjk.1))) x

/-- Compatibility for the coefficient tower indexed by a finite quotient class.  The finite
quotient component is retained so the augmentation target has the same pro-`C` index shape as the
class-restricted completed group algebra. -/
def PrimePowerCompletedCoeffCompatibleInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : ∀ i : PrimePowerCompletedGroupAlgebraIndexInClass G C,
      ModNCompletedCoeff (ℓ ^ i.1)) : Prop :=
  (primePowerCompletedCoeffSystemInClass ℓ G C).Compatible x

/-- The pro-`C`-indexed coefficient inverse limit attached to the class-restricted
prime-power completed group algebra. -/
abbrev PrimePowerCompletedCoeffInClass (C : ProCGroups.FiniteGroupClass.{u}) : Type _ :=
  {x : ∀ i : PrimePowerCompletedGroupAlgebraIndexInClass G C,
      ModNCompletedCoeff (ℓ ^ i.1) //
    PrimePowerCompletedCoeffCompatibleInClass (ℓ := ℓ) (G := G) C x}

/-- Projection from the pro-`C`-indexed coefficient limit to one finite stage. -/
def primePowerCompletedCoeffProjectionInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    PrimePowerCompletedCoeffInClass ℓ G C → ModNCompletedCoeff (ℓ ^ i.1) :=
  (primePowerCompletedCoeffSystemInClass ℓ G C).projection i

instance instZeroPrimePowerCompletedCoeffInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Zero (PrimePowerCompletedCoeffInClass ℓ G C) where
  zero := ⟨fun _ => 0, by
    dsimp [PrimePowerCompletedCoeffCompatibleInClass]
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    exact map_zero
      (modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1))⟩

instance instAddPrimePowerCompletedCoeffInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Add (PrimePowerCompletedCoeffInClass ℓ G C) where
  add x y := ⟨fun i =>
      (show ZMod (ℓ ^ i.1) from x.1 i) + (show ZMod (ℓ ^ i.1) from y.1 i), by
    dsimp [PrimePowerCompletedCoeffCompatibleInClass]
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) + (show ZMod (ℓ ^ j.1) from y.1 j)) =
      (show ZMod (ℓ ^ i.1) from x.1 i) + (show ZMod (ℓ ^ i.1) from y.1 i)
    rw [map_add]
    exact congrArg₂ HAdd.hAdd (x.2 i j hij) (y.2 i j hij)⟩

instance instNegPrimePowerCompletedCoeffInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Neg (PrimePowerCompletedCoeffInClass ℓ G C) where
  neg x := ⟨fun i => -(show ZMod (ℓ ^ i.1) from x.1 i), by
    dsimp [PrimePowerCompletedCoeffCompatibleInClass]
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        (-(show ZMod (ℓ ^ j.1) from x.1 j)) =
      -(show ZMod (ℓ ^ i.1) from x.1 i)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 i j hij)⟩

instance instSubPrimePowerCompletedCoeffInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Sub (PrimePowerCompletedCoeffInClass ℓ G C) where
  sub x y := ⟨fun i =>
      (show ZMod (ℓ ^ i.1) from x.1 i) - (show ZMod (ℓ ^ i.1) from y.1 i), by
    dsimp [PrimePowerCompletedCoeffCompatibleInClass]
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) - (show ZMod (ℓ ^ j.1) from y.1 j)) =
      (show ZMod (ℓ ^ i.1) from x.1 i) - (show ZMod (ℓ ^ i.1) from y.1 i)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 i j hij) (y.2 i j hij)⟩

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は零元を零元へ送る。 -/
@[simp]
theorem primePowerCompletedCoeffProjectionInClass_zero
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C) :
    primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i
        (0 : PrimePowerCompletedCoeffInClass ℓ G C) = 0 := by
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は和を和へ送る。 -/
@[simp]
theorem primePowerCompletedCoeffProjectionInClass_add
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x y : PrimePowerCompletedCoeffInClass ℓ G C) :
    primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i (x + y) =
      primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i x +
        primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i y := by
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は負元を負元へ送る。 -/
@[simp]
theorem primePowerCompletedCoeffProjectionInClass_neg
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x : PrimePowerCompletedCoeffInClass ℓ G C) :
    primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i (-x) =
      -primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i x := by
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数段階で、指定された有限群クラスに属する段階について、完備群環またはその augmentation ideal の有限段階射影は差を差へ送る。 -/
@[simp]
theorem primePowerCompletedCoeffProjectionInClass_sub
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x y : PrimePowerCompletedCoeffInClass ℓ G C) :
    primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i (x - y) =
      primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i x -
        primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i y := by
  rfl

/-- The class-restricted prime-power completed group algebra carries a canonical augmentation to
the pro-`C`-indexed coefficient limit. -/
def primePowerCompletedGroupAlgebraAugmentationInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    PrimePowerCompletedGroupAlgebraInClass ℓ G C →
      PrimePowerCompletedCoeffInClass ℓ G C := by
  intro x
  refine ⟨fun i => ?_, ?_⟩
  · letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    exact modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2 (x.1 i)
  · dsimp [PrimePowerCompletedCoeffCompatibleInClass]
    intro i j hij
    letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
    letI : Fact (0 < ℓ ^ j.1) := ⟨primePower_pos ℓ j.1⟩
    calc
      modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ j.1) G C j.2 (x.1 j))
        =
      modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2
        (primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij (x.1 j)) := by
          symm
          exact congrFun
            (congrArg DFunLike.coe
              (primePowerCompletedGroupAlgebraStageAugmentationInClass_comp_transition
                (ℓ := ℓ) (G := G) C hij)) (x.1 j)
      _ =
      modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2 (x.1 i) := by
          have hx :
              primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
                  (x.1 j) = x.1 i :=
            x.2 i j hij
          exact congrArg
            (modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2) hx

omit [Fact (0 < ℓ)] in
/-- 素冪係数で定めた 有限群クラスを固定した 有限段階射影が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem primePowerCompletedCoeffProjectionInClass_augmentation
    (C : ProCGroups.FiniteGroupClass.{u}) (i : PrimePowerCompletedGroupAlgebraIndexInClass G C)
    (x : PrimePowerCompletedGroupAlgebraInClass ℓ G C) :
    primePowerCompletedCoeffProjectionInClass (ℓ := ℓ) (G := G) C i
        (primePowerCompletedGroupAlgebraAugmentationInClass (ℓ := ℓ) (G := G) C x) =
      modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2
        (primePowerCompletedGroupAlgebraProjectionInClass (ℓ := ℓ) (G := G) C i x) := rfl

omit [Fact (0 < ℓ)] in
/-- The class-indexed completed group-algebra augmentation has a canonical section, obtained by
placing each compatible coefficient system on the identity monomial at every finite stage. -/
theorem primePowerCompletedGroupAlgebraAugmentationInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{u}) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraAugmentationInClass (ℓ := ℓ) (G := G) C) := by
  intro x
  refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
  · exact MonoidAlgebra.single
      (1 : CompletedGroupAlgebraQuotientInClass G C i.2) (x.1 i)
  · intro i j hij
    change
      primePowerCompletedGroupAlgebraTransitionInClass (ℓ := ℓ) (G := G) C hij
          (MonoidAlgebra.single
            (1 : CompletedGroupAlgebraQuotientInClass G C j.2) (x.1 j)) =
        MonoidAlgebra.single
          (1 : CompletedGroupAlgebraQuotientInClass G C i.2) (x.1 i)
    rw [primePowerCompletedGroupAlgebraTransitionInClass_single]
    have hxcoeff :
        modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1) (x.1 j) = x.1 i := by
      simpa [primePowerCompletedCoeffSystemInClass] using x.2 i j hij
    simpa using congrArg
      (fun a : ModNCompletedCoeff (ℓ ^ i.1) =>
        MonoidAlgebra.single
          (1 : CompletedGroupAlgebraQuotientInClass G C i.2) a)
      hxcoeff
  · apply Subtype.ext
    funext i
    change
      modNCompletedGroupAlgebraStageAugmentationInClass (ℓ ^ i.1) G C i.2
          (MonoidAlgebra.single
            (1 : CompletedGroupAlgebraQuotientInClass G C i.2) (x.1 i)) =
        x.1 i
    simp only [modNCompletedGroupAlgebraStageAugmentationInClass_single]


end

end FoxDifferential
