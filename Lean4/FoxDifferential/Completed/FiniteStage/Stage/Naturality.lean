import FoxDifferential.Completed.FiniteStage.Stage.Fundamental.Formula

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FiniteStage/Stage/Naturality.lean
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

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

omit [DecidableEq X] in
/-- Commutator-power relators are monotone in the normal subgroup. -/
theorem finiteFoxCommutatorPowerRelatorSet_mono
    {N M : Subgroup (FreeGroup X)} {n : ℕ} (hNM : N ≤ M) :
    finiteFoxCommutatorPowerRelatorSet (F := FreeGroup X) N n ⊆
      finiteFoxCommutatorPowerRelatorSet (F := FreeGroup X) M n := by
  intro g hg
  rcases hg with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl ⟨a, hNM ha, b, hNM hb, rfl⟩
  · exact Or.inr ⟨a, hNM ha, rfl⟩

omit [DecidableEq X] in
/-- The finite Fox commutator-power subgroup is monotone in the normal subgroup. -/
theorem finiteFoxCommutatorPowerSubgroup_mono
    {N M : Subgroup (FreeGroup X)} (hNM : N ≤ M) (n : ℕ) :
    finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n ≤
      finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) M n := by
  simpa [finiteFoxCommutatorPowerSubgroup] using
    Subgroup.normalClosure_mono
      (finiteFoxCommutatorPowerRelatorSet_mono (X := X) (n := n) hNM)

omit [DecidableEq X] in
/-- Commutator-power relators are contravariantly monotone under divisibility of exponents. -/
theorem finiteFoxCommutatorPowerRelatorSet_dvd
    {N : Subgroup (FreeGroup X)} {n m : ℕ} (hnm : n ∣ m) :
    finiteFoxCommutatorPowerRelatorSet (F := FreeGroup X) N m ⊆
      finiteFoxCommutatorPowerRelatorSet (F := FreeGroup X) N n := by
  intro g hg
  rcases hg with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl ⟨a, ha, b, hb, rfl⟩
  · rcases hnm with ⟨k, rfl⟩
    exact Or.inr ⟨a ^ k, N.pow_mem ha k, (pow_mul' a n k).symm⟩

omit [DecidableEq X] in
/-- The finite Fox commutator-power subgroup is contravariantly monotone under divisibility of
exponents. -/
theorem finiteFoxCommutatorPowerSubgroup_dvd
    (N : Subgroup (FreeGroup X)) {n m : ℕ} (hnm : n ∣ m) :
    finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N m ≤
      finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n := by
  simpa [finiteFoxCommutatorPowerSubgroup] using
    Subgroup.normalClosure_mono
      (finiteFoxCommutatorPowerRelatorSet_dvd (X := X) (N := N) hnm)

/-- Natural quotient map `F/N → F/M` induced by an inclusion `N ≤ M`. -/
def finiteFoxStageTargetQuotientMap
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal] (hNM : N ≤ M) :
    finiteFoxStageTargetQuotient (X := X) N →*
      finiteFoxStageTargetQuotient (X := X) M :=
  QuotientGroup.map _ _ (MonoidHom.id (FreeGroup X)) hNM

omit [DecidableEq X] in
/-- Evaluation of the finite-stage target quotient map on a representative. -/
@[simp]
theorem finiteFoxStageTargetQuotientMap_mk
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (w : FreeGroup X) :
    finiteFoxStageTargetQuotientMap (X := X) hNM (QuotientGroup.mk' N w) =
      QuotientGroup.mk' M w := by
  rfl

/-- Group-algebra map on finite-stage targets induced by `N ≤ M`. -/
def finiteFoxStageTargetGroupAlgebraMap
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal] (hNM : N ≤ M) (n : ℕ) :
    finiteFoxStageTargetGroupAlgebra (X := X) N n →+*
      finiteFoxStageTargetGroupAlgebra (X := X) M n :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (finiteFoxStageTargetQuotientMap (X := X) hNM)

omit [DecidableEq X] in
/-- Evaluation of the finite-stage target group-algebra map on a represented word. -/
@[simp]
theorem finiteFoxStageTargetGroupAlgebraMap_of
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (n : ℕ) (w : FreeGroup X) :
    finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w)) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) M) (QuotientGroup.mk' M w) := by
  simp only [finiteFoxStageTargetGroupAlgebraMap, MonoidAlgebra.of, MonoidAlgebra.single,
  QuotientGroup.mk'_apply, MonoidHom.coe_mk, OneHom.coe_mk, MonoidAlgebra.mapDomainRingHom_apply,
  Finsupp.mapDomain_single]
  simpa using congrArg
    (fun q : finiteFoxStageTargetQuotient (X := X) M =>
      Finsupp.single q (1 : ModNCompletedCoeff n))
    (finiteFoxStageTargetQuotientMap_mk (X := X) hNM w)

omit [DecidableEq X] in
/-- Evaluation of the finite-stage target group-algebra map on a quotient basis element. -/
@[simp]
theorem finiteFoxStageTargetGroupAlgebraMap_of_quotient
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (n : ℕ) (q : finiteFoxStageTargetQuotient (X := X) N) :
    finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (finiteFoxStageTargetQuotient (X := X) N) q) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (finiteFoxStageTargetQuotient (X := X) M)
        (finiteFoxStageTargetQuotientMap (X := X) hNM q) := by
  rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
  rw [finiteFoxStageTargetGroupAlgebraMap_of, finiteFoxStageTargetQuotientMap_mk]

/-- Natural quotient map between finite-stage source quotients induced by `N ≤ M`. -/
def finiteFoxStageSourceQuotientMap
    {N M : Subgroup (FreeGroup X)} (hNM : N ≤ M) (n : ℕ) :
    FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n →*
      FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) M n :=
  QuotientGroup.map _ _ (MonoidHom.id (FreeGroup X))
    (finiteFoxCommutatorPowerSubgroup_mono (X := X) hNM n)

omit [DecidableEq X] in
/-- Evaluation of the finite-stage source quotient map on a representative. -/
@[simp]
theorem finiteFoxStageSourceQuotientMap_mk
    {N M : Subgroup (FreeGroup X)}
    (hNM : N ≤ M) (n : ℕ) (w : FreeGroup X) :
    finiteFoxStageSourceQuotientMap (X := X) hNM n
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) =
      QuotientGroup.mk'
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) M n) w := by
  rfl

/-- Group-algebra map on finite-stage source quotients induced by `N ≤ M`. -/
def finiteFoxStageSourceGroupAlgebraMap
    {N M : Subgroup (FreeGroup X)} (hNM : N ≤ M) (n : ℕ) :
    MonoidAlgebra (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) →+*
      MonoidAlgebra (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) M n) :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (finiteFoxStageSourceQuotientMap (X := X) hNM n)

omit [DecidableEq X] in
/-- Evaluation of the finite-stage source group-algebra map on a represented word. -/
@[simp]
theorem finiteFoxStageSourceGroupAlgebraMap_of
    {N M : Subgroup (FreeGroup X)}
    (hNM : N ≤ M) (n : ℕ) (w : FreeGroup X) :
    finiteFoxStageSourceGroupAlgebraMap (X := X) hNM n
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)
          (QuotientGroup.mk'
            (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) w)) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) M n)
        (QuotientGroup.mk'
          (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) M n) w) := by
  simp only [finiteFoxStageSourceGroupAlgebraMap, MonoidAlgebra.of, MonoidAlgebra.single,
  QuotientGroup.mk'_apply, MonoidHom.coe_mk, OneHom.coe_mk, MonoidAlgebra.mapDomainRingHom_apply,
  Finsupp.mapDomain_single]
  simpa using congrArg
    (fun q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) M n =>
      Finsupp.single q (1 : ModNCompletedCoeff n))
    (finiteFoxStageSourceQuotientMap_mk (X := X) hNM n w)

omit [DecidableEq X] in
/-- Evaluation of the finite-stage source group-algebra map on a quotient basis element. -/
@[simp]
theorem finiteFoxStageSourceGroupAlgebraMap_of_quotient
    {N M : Subgroup (FreeGroup X)}
    (hNM : N ≤ M) (n : ℕ)
    (q : FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    finiteFoxStageSourceGroupAlgebraMap (X := X) hNM n
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) M n)
        (finiteFoxStageSourceQuotientMap (X := X) hNM n q) := by
  rcases QuotientGroup.mk'_surjective
      (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
  rw [finiteFoxStageSourceGroupAlgebraMap_of, finiteFoxStageSourceQuotientMap_mk]

/-- Semidirect target map induced by functoriality in the normal subgroup. -/
def finiteFoxStageSemidirectMap
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal] (hNM : N ≤ M) (n : ℕ) :
    FiniteFoxStageSemidirect (X := X) N n →*
      FiniteFoxStageSemidirect (X := X) M n where
  toFun a :=
    { left := fun i => finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n (a.left i)
      right := finiteFoxStageTargetQuotientMap (X := X) hNM a.right }
  map_one' := by
    apply FiniteFoxStageSemidirect.ext
    · funext i
      simp only [FiniteFoxStageSemidirect.one_left, Pi.zero_apply, map_zero]
    · simp only [FiniteFoxStageSemidirect.one_right, map_one]
  map_mul' a b := by
    apply FiniteFoxStageSemidirect.ext
    · funext i
      have hright :
          finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
              (MonoidAlgebra.single a.right (1 : ModNCompletedCoeff n)) =
            MonoidAlgebra.single
              (finiteFoxStageTargetQuotientMap (X := X) hNM a.right) 1 := by
        simpa [MonoidAlgebra.of, MonoidAlgebra.single] using
          (finiteFoxStageTargetGroupAlgebraMap_of_quotient
            (X := X) hNM n a.right)
      simp only [FiniteFoxStageSemidirect.mul_left, MonoidAlgebra.of_apply, Pi.add_apply, Pi.smul_apply,
  smul_eq_mul, map_add, map_mul, hright]
    · simp only [FiniteFoxStageSemidirect.mul_right, map_mul]

/-- The finite-stage semidirect map carries the lift for `N` to the lift for `M`. -/
theorem finiteFoxStageSemidirectMap_lift
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (n : ℕ) (w : FreeGroup X) :
    finiteFoxStageSemidirectMap (X := X) hNM n
        (finiteFoxStageLift (X := X) N n w) =
      finiteFoxStageLift (X := X) M n w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [finiteFoxStageLift, QuotientGroup.mk'_apply, map_one]
  | of x =>
      apply FiniteFoxStageSemidirect.ext
      · funext i
        by_cases hix : i = x
        · subst hix
          simp only [finiteFoxStageSemidirectMap, finiteFoxStageLift, QuotientGroup.mk'_apply, FreeGroup.lift_apply_of,
  MonoidHom.coe_mk, OneHom.coe_mk, Pi.single_eq_same, map_one]
        · simp only [finiteFoxStageSemidirectMap, finiteFoxStageLift, QuotientGroup.mk'_apply, FreeGroup.lift_apply_of,
  MonoidHom.coe_mk, OneHom.coe_mk, Pi.single_eq_of_ne hix, map_zero]
      · exact finiteFoxStageTargetQuotientMap_mk (X := X) hNM (FreeGroup.of x)
  | inv_of x hx =>
      simpa using congrArg Inv.inv hx
  | mul x y hx hy =>
      simp only [map_mul, hx, hy]

/-- Naturality of finite-stage Fox derivative coordinates under `N ≤ M`. -/
theorem finiteFoxStageDerivative_natural
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (n : ℕ) (i : X) (w : FreeGroup X) :
    finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
        (finiteFoxStageDerivative (X := X) N n i w) =
      finiteFoxStageDerivative (X := X) M n i w := by
  have h :=
    congrArg FiniteFoxStageSemidirect.left
      (finiteFoxStageSemidirectMap_lift (X := X) hNM n w)
  simpa [finiteFoxStageDerivative, finiteFoxStageDerivativeVector,
    finiteFoxStageSemidirectMap] using congrFun h i

/-- Naturality of finite-stage group-algebra derivative coordinates under `N ≤ M`. -/
theorem finiteFoxStageGroupAlgebraDerivative_natural
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (n : ℕ) (i : X)
    (x : MonoidAlgebra (ModNCompletedCoeff n)
        (FreeGroup X ⧸ finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n)) :
    finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
        (finiteFoxStageGroupAlgebraDerivative (X := X) N n i x) =
      finiteFoxStageGroupAlgebraDerivative (X := X) M n i
        (finiteFoxStageSourceGroupAlgebraMap (X := X) hNM n x) := by
  refine MonoidAlgebra.induction_on
    (p := fun x =>
      finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
          (finiteFoxStageGroupAlgebraDerivative (X := X) N n i x) =
        finiteFoxStageGroupAlgebraDerivative (X := X) M n i
          (finiteFoxStageSourceGroupAlgebraMap (X := X) hNM n x))
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
    rw [finiteFoxStageGroupAlgebraDerivative_of,
      finiteFoxStageSourceGroupAlgebraMap_of,
      finiteFoxStageGroupAlgebraDerivative_of,
      finiteFoxStageDerivative_natural]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a x hx
    have htargetScalar :
        finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
            (MonoidAlgebra.single
              (1 : finiteFoxStageTargetQuotient (X := X) N) a) =
          MonoidAlgebra.single
            (1 : finiteFoxStageTargetQuotient (X := X) M) a := by
      simp only [finiteFoxStageTargetGroupAlgebraMap, MonoidAlgebra.mapDomainRingHom, RingHom.coe_mk,
  MonoidHom.coe_mk, OneHom.coe_mk, Finsupp.mapDomain_single, map_one]
    have hsourceScalar :
        finiteFoxStageSourceGroupAlgebraMap (X := X) hNM n
            (MonoidAlgebra.single
              (1 : FreeGroup X ⧸
                finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) N n) a) =
          MonoidAlgebra.single
            (1 : FreeGroup X ⧸
              finiteFoxCommutatorPowerSubgroup (F := FreeGroup X) M n) a := by
      simp only [finiteFoxStageSourceGroupAlgebraMap, MonoidAlgebra.mapDomainRingHom, RingHom.coe_mk,
  MonoidHom.coe_mk, OneHom.coe_mk, Finsupp.mapDomain_single, map_one]
    calc
      finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
          (finiteFoxStageGroupAlgebraDerivative (X := X) N n i (a • x))
        =
          finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
            (a • finiteFoxStageGroupAlgebraDerivative (X := X) N n i x) := by
            rw [LinearMap.map_smul]
      _ =
          a • finiteFoxStageTargetGroupAlgebraMap (X := X) hNM n
            (finiteFoxStageGroupAlgebraDerivative (X := X) N n i x) := by
            simp only [Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
  Function.comp_apply, id_eq, map_mul, htargetScalar]
      _ =
          a • finiteFoxStageGroupAlgebraDerivative (X := X) M n i
            (finiteFoxStageSourceGroupAlgebraMap (X := X) hNM n x) := by
            rw [hx]
      _ =
          finiteFoxStageGroupAlgebraDerivative (X := X) M n i
            (a • finiteFoxStageSourceGroupAlgebraMap (X := X) hNM n x) := by
            rw [LinearMap.map_smul]
      _ =
            finiteFoxStageGroupAlgebraDerivative (X := X) M n i
            (finiteFoxStageSourceGroupAlgebraMap (X := X) hNM n (a • x)) := by
            congr 1
            simp only [Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
  Function.comp_apply, id_eq, map_mul, hsourceScalar]


end

end FoxDifferential
