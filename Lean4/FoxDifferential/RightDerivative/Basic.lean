import FoxDifferential.RightDerivative.GeometricSeries
import FoxDifferential.Discrete.FoxCalculus.Derivative

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/RightDerivative/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Right Fox derivatives

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

structure RightDerivation (G : Type*) [Group G] where
  toAddHom : FoxDifferential.GroupRing G →+ FoxDifferential.GroupRing G
  map_mul' : ∀ u v : FoxDifferential.GroupRing G,
    toAddHom (u * v) =
      toAddHom u * v + FoxDifferential.augmentation G u • toAddHom v

namespace RightDerivation

variable {G : Type*} [Group G]

instance instCoeFunRightDerivation : CoeFun (RightDerivation G) (fun _ =>
    FoxDifferential.GroupRing G → FoxDifferential.GroupRing G) :=
  ⟨fun D => D.toAddHom⟩

@[simp]
theorem map_zero (D : RightDerivation G) : D 0 = 0 :=
  D.toAddHom.map_zero

@[simp]
theorem map_add (D : RightDerivation G) (u v : FoxDifferential.GroupRing G) :
    D (u + v) = D u + D v :=
  D.toAddHom.map_add u v

theorem map_mul (D : RightDerivation G) (u v : FoxDifferential.GroupRing G) :
    D (u * v) = D u * v + FoxDifferential.augmentation G u • D v :=
  D.map_mul' u v

@[simp]
theorem map_one (D : RightDerivation G) : D 1 = 0 := by
  have h := D.map_mul (1 : FoxDifferential.GroupRing G) 1
  simp only [mul_one, augmentation, augmentationAlgHom, AlgHom.toRingHom_eq_coe,
  _root_.map_one, one_smul, left_eq_add] at h
  exact h

theorem map_inv_groupElement (D : RightDerivation G) (g : G) :
    D (MonoidAlgebra.of ℤ G g⁻¹ : FoxDifferential.GroupRing G) =
      -D (MonoidAlgebra.of ℤ G g : FoxDifferential.GroupRing G) *
        (MonoidAlgebra.of ℤ G g⁻¹ : FoxDifferential.GroupRing G) := by
  have h := D.map_mul
    (MonoidAlgebra.of ℤ G g : FoxDifferential.GroupRing G)
    (MonoidAlgebra.of ℤ G g⁻¹ : FoxDifferential.GroupRing G)
  have h0 :
      D.toAddHom (MonoidAlgebra.single (1 : G) 1 : FoxDifferential.GroupRing G) = 0 := by
    change D (1 : FoxDifferential.GroupRing G) = 0
    exact D.map_one
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_inv_cancel, mul_one, augmentation,
  augmentationAlgHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.one_apply,
  one_smul] at h
  rw [h0] at h
  simpa [neg_mul] using eq_neg_of_add_eq_zero_right h.symm

theorem map_pow_groupElement (D : RightDerivation G) (g : G) :
    ∀ n : ℕ,
      D (MonoidAlgebra.of ℤ G (g ^ n) : FoxDifferential.GroupRing G) =
        D (MonoidAlgebra.of ℤ G g : FoxDifferential.GroupRing G) * geomSeries g n
  | 0 => by
      simp only [pow_zero, MonoidAlgebra.of_apply, geomSeries, Finset.range_zero, Finset.sum_empty, mul_zero]
      change D (1 : FoxDifferential.GroupRing G) = 0
      exact D.map_one
  | n + 1 => by
      rw [pow_succ]
      have hmul :
          (MonoidAlgebra.of ℤ G (g ^ n * g) : FoxDifferential.GroupRing G) =
            (MonoidAlgebra.of ℤ G (g ^ n) : FoxDifferential.GroupRing G) *
              MonoidAlgebra.of ℤ G g := by
        simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one]
      rw [hmul, map_mul]
      rw [map_pow_groupElement D g n]
      simp only [MonoidAlgebra.of_apply, mul_assoc, augmentation, augmentationAlgHom, AlgHom.toRingHom_eq_coe,
  RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.one_apply, mul_one, one_smul,
  geomSeries_succ_eq_mul_add_one, mul_add]

def groupRingLinearExtension (δ : G → FoxDifferential.GroupRing G) :
    FoxDifferential.GroupRing G →ₗ[ℤ] FoxDifferential.GroupRing G :=
  Finsupp.linearCombination ℤ δ

@[simp]
theorem groupRingLinearExtension_single (δ : G → FoxDifferential.GroupRing G) (g : G)
    (n : ℤ) :
    groupRingLinearExtension δ (MonoidAlgebra.single g n : FoxDifferential.GroupRing G) =
      n • δ g := by
  exact Finsupp.linearCombination_single ℤ n g

theorem groupRingLinearExtension_map_mul
    (δ : G → FoxDifferential.GroupRing G)
    (hδ : ∀ g h : G, δ (g * h) = δ g * MonoidAlgebra.of ℤ G h + δ h)
    (u v : FoxDifferential.GroupRing G) :
    groupRingLinearExtension δ (u * v) =
      groupRingLinearExtension δ u * v +
        FoxDifferential.augmentation G u • groupRingLinearExtension δ v := by
  classical
  induction u using Finsupp.induction_linear with
  | zero =>
      simp only [groupRingLinearExtension, zero_mul, _root_.map_zero, zero_smul, add_zero]
  | add u₁ u₂ hu₁ hu₂ =>
      simp only [add_mul, _root_.map_add, hu₁, zsmul_eq_mul, add_comm, hu₂, add_left_comm, add_assoc, Int.cast_add]
  | single g n =>
      induction v using Finsupp.induction_linear with
      | zero =>
          simp only [groupRingLinearExtension, mul_zero, _root_.map_zero, smul_zero, add_zero]
      | add v₁ v₂ hv₁ hv₂ =>
          simp only [mul_add, _root_.map_add, hv₁, groupRingLinearExtension_single, zsmul_eq_mul, hv₂, add_left_comm,
  add_assoc, smul_add]
      | single h m =>
          rw [MonoidAlgebra.single_mul_single]
          rw [groupRingLinearExtension_single, groupRingLinearExtension_single,
            groupRingLinearExtension_single]
          rw [hδ]
          simp only [MonoidAlgebra.of_apply, smul_add, zsmul_eq_mul, Int.cast_mul, augmentation, augmentationAlgHom,
  AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.one_apply, mul_one]
          rw [show (Finsupp.single h m : FoxDifferential.GroupRing G) =
              algebraMap ℤ (FoxDifferential.GroupRing G) m *
                (MonoidAlgebra.of ℤ G h : FoxDifferential.GroupRing G) by
                simpa using (MonoidAlgebra.single_eq_algebraMap_mul_of (M := G) h m)]
          change ((n : FoxDifferential.GroupRing G) * (m : FoxDifferential.GroupRing G)) *
                (δ g * (MonoidAlgebra.of ℤ G h : FoxDifferential.GroupRing G)) +
                ((n : FoxDifferential.GroupRing G) * (m : FoxDifferential.GroupRing G)) * δ h =
              (n : FoxDifferential.GroupRing G) * δ g *
                ((m : FoxDifferential.GroupRing G) *
                  (MonoidAlgebra.of ℤ G h : FoxDifferential.GroupRing G)) +
                (n : FoxDifferential.GroupRing G) *
                  ((m : FoxDifferential.GroupRing G) * δ h)
          rw [mul_assoc (n : FoxDifferential.GroupRing G) (δ g)
            ((m : FoxDifferential.GroupRing G) *
              (MonoidAlgebra.of ℤ G h : FoxDifferential.GroupRing G))]
          rw [← mul_assoc (δ g) (m : FoxDifferential.GroupRing G)
            (MonoidAlgebra.of ℤ G h : FoxDifferential.GroupRing G)]
          rw [(Int.cast_commute m (δ g)).eq.symm]
          rw [mul_assoc (m : FoxDifferential.GroupRing G) (δ g)
            (MonoidAlgebra.of ℤ G h : FoxDifferential.GroupRing G)]
          rw [← mul_assoc (n : FoxDifferential.GroupRing G) (m : FoxDifferential.GroupRing G)
            (δ g * (MonoidAlgebra.of ℤ G h : FoxDifferential.GroupRing G))]
          rw [← mul_assoc (n : FoxDifferential.GroupRing G) (m : FoxDifferential.GroupRing G)
            (δ h)]

def ofGroupMap (δ : G → FoxDifferential.GroupRing G)
    (hδ : ∀ g h : G, δ (g * h) = δ g * MonoidAlgebra.of ℤ G h + δ h) :
    RightDerivation G where
  toAddHom := (groupRingLinearExtension δ).toAddMonoidHom
  map_mul' := groupRingLinearExtension_map_mul δ hδ

end RightDerivation

end

end FoxDifferential
