import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.InClass.Basic
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.MonoidAlgebra.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraModN/CoeffMap.lean
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

variable {n m k : ℕ}
variable [Fact (0 < n)] [Fact (0 < m)] [Fact (0 < k)]

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- The coefficient reduction map `ZMod m -> ZMod n` attached to a divisibility relation `n ∣ m`.
-/
def modNCompletedCoeffMap (hnm : n ∣ m) :
    ModNCompletedCoeff m →+* ModNCompletedCoeff n :=
  ZMod.castHom hnm (ModNCompletedCoeff n)

omit [Fact (0 < n)] in
/-- Identity case for `modNCompletedCoeffMap`. -/
@[simp]
theorem modNCompletedCoeffMap_rfl :
    modNCompletedCoeffMap (n := n) (m := n) dvd_rfl = RingHom.id _ := by
  ext x
  rcases ZMod.intCast_surjective x with ⟨t, rfl⟩
  simp only [modNCompletedCoeffMap, ZMod.castHom_self, map_intCast]

omit [Fact (0 < n)] [Fact (0 < m)] [Fact (0 < k)] in
/-- Composition of coefficient reduction maps. -/
@[simp]
theorem modNCompletedCoeffMap_comp (hnm : n ∣ m) (hmk : m ∣ k) :
    (modNCompletedCoeffMap (n := n) (m := m) hnm).comp
        (modNCompletedCoeffMap (n := m) (m := k) hmk) =
      modNCompletedCoeffMap (n := n) (m := k) (dvd_trans hnm hmk) := by
  ext x
  rcases ZMod.intCast_surjective x with ⟨t, rfl⟩
  simp only [modNCompletedCoeffMap, ZMod.castHom_comp, map_intCast]

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- The coefficient reduction map on one residue-coefficient group ring. -/
def modNCompletedGroupRingCoeffMap (H : Type*) [Monoid H] (hnm : n ∣ m) :
    ModNCompletedGroupRing m H →+* ModNCompletedGroupRing n H := by
  letI : Algebra (ModNCompletedCoeff m) (ModNCompletedCoeff n) :=
    ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := m) hnm
  letI : Algebra (ModNCompletedCoeff m) (ModNCompletedGroupRing n H) := inferInstance
  exact
    (MonoidAlgebra.lift (ModNCompletedCoeff m) (ModNCompletedGroupRing n H) H
      (MonoidAlgebra.of (ModNCompletedCoeff n) H)).toRingHom

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- Evaluation of coefficient reduction on a group-like basis element. -/
@[simp]
theorem modNCompletedGroupRingCoeffMap_of
    (H : Type*) [Monoid H] (hnm : n ∣ m) (h : H) :
    modNCompletedGroupRingCoeffMap (n := n) (m := m) H hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m) H h) =
      MonoidAlgebra.of (ModNCompletedCoeff n) H h := by
  classical
  simp only [modNCompletedGroupRingCoeffMap, MonoidAlgebra.of, MonoidAlgebra.single, AlgHom.toRingHom_eq_coe,
  MonoidHom.coe_mk, OneHom.coe_mk, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidAlgebra.smul_single, one_smul]

end

end FoxDifferential
