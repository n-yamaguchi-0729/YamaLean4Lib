import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Coeff.Ring

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraPrimePower/Coeff/Projection.lean
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

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は単位元を単位元へ送る。 -/
@[simp]
theorem primePowerCompletedCoeffProjection_one
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (1 : PrimePowerCompletedCoeff ℓ G) = 1 := by
  change (1 : ZMod (ℓ ^ i.1)) = 1
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は積を積へ送る。 -/
@[simp]
theorem primePowerCompletedCoeffProjection_mul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (x * y) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i x *
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i y := by
  change (show ZMod (ℓ ^ i.1) from (x * y).1 i) =
    (show ZMod (ℓ ^ i.1) from x.1 i) * (show ZMod (ℓ ^ i.1) from y.1 i)
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 有限段階射影が自然数の標準像を各有限段階で同じ自然数の標準像として計算することを述べる。 -/
@[simp]
theorem primePowerCompletedCoeffProjection_natCast
    (i : PrimePowerCompletedGroupAlgebraIndex G) (n : ℕ) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (n : PrimePowerCompletedCoeff ℓ G) = n := by
  change (n : ZMod (ℓ ^ i.1)) = n
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数で定めた 有限段階射影が整数の標準像を各有限段階で同じ整数の標準像として計算することを述べる。 -/
@[simp]
theorem primePowerCompletedCoeffProjection_intCast
    (i : PrimePowerCompletedGroupAlgebraIndex G) (n : ℤ) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (n : PrimePowerCompletedCoeff ℓ G) = n := by
  change (n : ZMod (ℓ ^ i.1)) = n
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は零元を零元へ送る。 -/
@[simp]
theorem primePowerCompletedCoeffProjection_zero
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (0 : PrimePowerCompletedCoeff ℓ G) = 0 := by
  change (0 : ZMod (ℓ ^ i.1)) = 0
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は和を和へ送る。 -/
@[simp]
theorem primePowerCompletedCoeffProjection_add
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (x + y) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i x +
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i y := by
  change (show ZMod (ℓ ^ i.1) from (x + y).1 i) =
    (show ZMod (ℓ ^ i.1) from x.1 i) + (show ZMod (ℓ ^ i.1) from y.1 i)
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は負元を負元へ送る。 -/
@[simp]
theorem primePowerCompletedCoeffProjection_neg
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (-x) =
      -primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i x := by
  change (show ZMod (ℓ ^ i.1) from (-x).1 i) =
    -(show ZMod (ℓ ^ i.1) from x.1 i)
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- 素冪係数段階で、完備群環またはその augmentation ideal の有限段階射影は差を差へ送る。 -/
@[simp]
theorem primePowerCompletedCoeffProjection_sub
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (x - y) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i x -
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i y := by
  change (show ZMod (ℓ ^ i.1) from (x - y).1 i) =
    (show ZMod (ℓ ^ i.1) from x.1 i) - (show ZMod (ℓ ^ i.1) from y.1 i)
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- Coefficient projections with the same prime-power exponent do not depend on the
finite-quotient component of the group-algebra index.  The second index component synchronizes
coefficients and group-algebra stages in one inverse system. -/
theorem primePowerCompletedCoeffProjection_eq_of_same_exponent
    (a : ℕ) (U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G)
    (z : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, U) z =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, V) z := by
  let T : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G := _root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G
  let hTU : (a, T) ≤ (a, U) :=
    ⟨le_rfl, _root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex_le (G := G) U⟩
  let hTV : (a, T) ≤ (a, V) :=
    ⟨le_rfl, _root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex_le (G := G) V⟩
  have hTU_coeff :
      modNCompletedCoeffMap
          (n := ℓ ^ a) (m := ℓ ^ a)
          (primePow_dvd_primePow (ℓ := ℓ) hTU.1) = RingHom.id _ := by
    have hproof :
        primePow_dvd_primePow (ℓ := ℓ) hTU.1 = (dvd_rfl : ℓ ^ a ∣ ℓ ^ a) :=
      Subsingleton.elim _ _
    rw [hproof]
    exact modNCompletedCoeffMap_rfl (n := ℓ ^ a)
  have hTV_coeff :
      modNCompletedCoeffMap
          (n := ℓ ^ a) (m := ℓ ^ a)
          (primePow_dvd_primePow (ℓ := ℓ) hTV.1) = RingHom.id _ := by
    have hproof :
        primePow_dvd_primePow (ℓ := ℓ) hTV.1 = (dvd_rfl : ℓ ^ a ∣ ℓ ^ a) :=
      Subsingleton.elim _ _
    rw [hproof]
    exact modNCompletedCoeffMap_rfl (n := ℓ ^ a)
  have hU := z.2 (a, T) (a, U) hTU
  have hV := z.2 (a, T) (a, V) hTV
  have hU' :
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, U) z =
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, T) z := by
    simpa [primePowerCompletedCoeffProjection, primePowerCompletedCoeffSystem, hTU_coeff] using
      hU
  have hV' :
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, V) z =
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, T) z := by
    simpa [primePowerCompletedCoeffProjection, primePowerCompletedCoeffSystem, hTV_coeff] using
      hV
  exact hU'.trans hV'.symm

end

end FoxDifferential
