import FoxDifferential.Completed.FreeProC.ProCIntegerBifilteredStageRightProjection

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/SemidirectKernelBasis.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Componentwise kernel bases for completed Fox semidirect stages

The completed density route needs the finite semidirect stage kernels to form a neighbourhood
basis at the identity of `Z_C[[H]]^X ⋊ H`.  For actual finite quotients this is usually proved in
components: the completed Fox-coordinate projections separate the additive coordinate direction,
and the target quotient maps separate the group direction.  This file packages that componentwise
argument.

No finite-stage exactness is hidden here.  The only mathematical input is that identity
neighbourhoods in the semidirect product contain a rectangle in the coordinate and target
components; the continuous/topological file proves this for the standard product topology.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v

section AdditiveKernelBasis

variable {A : Type u} [AddZeroClass A] [TopologicalSpace A]
variable {J : Type v} {B : J → Type*} [∀ j, AddZeroClass (B j)]
variable (π : ∀ j : J, A →+ B j)

/-- Additive-coordinate quotient kernels form a neighbourhood basis at zero.

This is the additive analogue of `HasIdentityQuotientKernelNeighbourhoodBasis`.  It is used for
the left coordinate `Z_C[[H]]^X`, whose finite-stage maps are additive homomorphisms rather than
multiplicative homomorphisms. -/
def HasAdditiveIdentityQuotientKernelNeighbourhoodBasis : Prop :=
  ∀ U : Set A, IsOpen U → (0 : A) ∈ U →
    ∃ j : J, ∀ z : A, π j z = 0 → z ∈ U

end AdditiveKernelBasis

section CoordinateKernelBasis

variable {A : Type u} [AddCommMonoid A] [TopologicalSpace A]
variable {J : Type v} [Preorder J] [Nonempty J]
variable {B : J → Type*} [∀ j, AddCommMonoid (B j)]
variable {X : Type u} [Fintype X]

/-- A finite product neighbourhood around zero in `X -> A`, stated in a form convenient for
coordinatewise kernel-basis arguments. -/
def HasFiniteCoordinateZeroRectangularNeighbourhoods : Prop :=
  ∀ U : Set (X → A), IsOpen U → (0 : X → A) ∈ U →
    ∃ V : X → Set A,
      (∀ x : X, IsOpen (V x) ∧ (0 : A) ∈ V x) ∧
      ∀ v : X → A, (∀ x : X, v x ∈ V x) → v ∈ U

/-- Coordinatewise additive homomorphism induced by a stage coefficient map. -/
def coordinatewiseAddMonoidHom
    (π : ∀ j : J, A →+ B j) (j : J) :
    (X → A) →+ (X → B j) where
  toFun v := fun x => π j (v x)
  map_zero' := by
    funext x
    exact map_zero (π j)
  map_add' v w := by
    funext x
    exact map_add (π j) (v x) (w x)

omit [TopologicalSpace A] [Preorder J] [Nonempty J] [Fintype X] in
@[simp]
theorem coordinatewiseAddMonoidHom_apply
    (π : ∀ j : J, A →+ B j) (j : J) (v : X → A) (x : X) :
    coordinatewiseAddMonoidHom (X := X) π j v x = π j (v x) :=
  rfl

/-- If coefficient kernels form a zero-neighbourhood basis and stage kernels are monotone along a
directed finite-stage system, then the coordinatewise finite product maps also form a
zero-neighbourhood kernel basis. -/
theorem coordinatewiseAdditiveKernelBasis_of_component_basis
    (π : ∀ j : J, A →+ B j)
    (hrect : HasFiniteCoordinateZeroRectangularNeighbourhoods (A := A) (X := X))
    (hdir : Directed (· ≤ ·) (id : J → J))
    (hbasis : HasAdditiveIdentityQuotientKernelNeighbourhoodBasis (A := A) π)
    (hmono : ∀ {i j : J}, i ≤ j → ∀ a : A, π j a = 0 → π i a = 0) :
    HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
      (A := X → A)
      (fun j : J => coordinatewiseAddMonoidHom (X := X) π j) := by
  intro U hU hUzero
  rcases hrect U hU hUzero with ⟨V, hV, hrectU⟩
  have hstage : ∀ x : X, ∃ j : J, ∀ a : A, π j a = 0 → a ∈ V x := by
    intro x
    exact hbasis (V x) (hV x).1 (hV x).2
  choose jx hjx using hstage
  classical
  have hupper : ∀ s : Finset X, ∃ k : J, ∀ x : X, x ∈ s → jx x ≤ k := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨Classical.choice (inferInstance : Nonempty J), by simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true]⟩
    | insert x s hxs ih =>
        rcases ih with ⟨k, hk⟩
        rcases hdir (jx x) k with ⟨l, hxl, hkl⟩
        refine ⟨l, ?_⟩
        intro y hy
        rw [Finset.mem_insert] at hy
        rcases hy with rfl | hy
        · exact hxl
        · exact (hk y hy).trans hkl
  rcases hupper (Finset.univ : Finset X) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro v hv
  refine hrectU v ?_
  intro x
  exact hjx x (v x) (hmono (hk x (by simp only [Finset.mem_univ])) (v x) (by
    have hvx := congrArg (fun f : X → B k => f x) hv
    simpa [coordinatewiseAddMonoidHom] using hvx))

end CoordinateKernelBasis

section AbstractSemidirectComponentBasis

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable {J : Type v} [Preorder J]
variable (Nstage : J → Subgroup (FreeGroup X)) [∀ j, (Nstage j).Normal]
variable (nstage : J → ℕ) [∀ j, Fact (0 < nstage j)]

/-- Identity neighbourhoods in the completed Fox semidirect product contain component rectangles.

For the standard product topology this follows from the homeomorphism
`Z_C[[H]]^X ⋊ H ≃ Z_C[[H]]^X × H`; it is kept as a named property so the algebraic componentwise
kernel-basis theorem below is independent of the concrete topology construction. -/
def HasSemidirectRectangularIdentityNeighbourhoods
    (C : ProCGroups.FiniteGroupClass.{u})
    [TopologicalSpace (ZCCompletedGroupAlgebra C H)]
    [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] : Prop :=
  ∀ U : Set (ZCCompletedFoxSemidirect C X H),
    IsOpen U → (1 : ZCCompletedFoxSemidirect C X H) ∈ U →
      ∃ UL : Set (ZCFreeFoxCoordinates C (X := X) (H := H)),
      ∃ UR : Set H,
        IsOpen UL ∧ (0 : ZCFreeFoxCoordinates C (X := X) (H := H)) ∈ UL ∧
        IsOpen UR ∧ (1 : H) ∈ UR ∧
        ∀ y : ZCCompletedFoxSemidirect C X H,
          y.left ∈ UL → y.right ∈ UR → y ∈ U

omit [∀ (j : J), Fact (0 < nstage j)] in
omit [DecidableEq X] in
/-- If the coordinate kernels and target kernels are neighbourhood bases in the two components,
and the finite-stage kernels are monotone along the directed stage system, then the semidirect
stage kernels are a neighbourhood basis at the identity.

This is the topological bridge needed to feed actual finite quotient projections into the completed
Fox density theorem. -/
theorem freeProCZCCompletedFoxSemidirectStageMap_identity_basis_of_component_bases
    (hrect : HasSemidirectRectangularIdentityNeighbourhoods
      (X := X) (H := H) ProC.finiteQuotientClass)
    (hdir : Directed (· ≤ ·) (id : J → J))
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H) →+
        finiteFoxStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J, H →* finiteFoxStageTargetQuotient (X := X) (Nstage j))
    (hscalar : ∀ j : J, ∀ (h : H)
      (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)),
        stageLeft j (zcGroupLike ProC.finiteQuotientClass H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (finiteFoxStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hleft_basis :
      HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
        (A := ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
        stageLeft)
    (hright_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis (Y := H) stageRight)
    (hleft_mono : ∀ {i j : J}, i ≤ j →
      ∀ v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H),
        stageLeft j v = 0 → stageLeft i v = 0)
    (hright_mono : ∀ {i j : J}, i ≤ j → ∀ h : H,
        stageRight j h = 1 → stageRight i h = 1) :
    HasIdentityQuotientKernelNeighbourhoodBasis
      (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
      (fun j : J =>
        freeProCZCCompletedFoxSemidirectStageMap
          (ProC := ProC) (X := X) (H := H) (Nstage j) (nstage j)
          (stageLeft j) (stageRight j) (hscalar j)) := by
  intro U hU hUone
  rcases hrect U hU hUone with
    ⟨UL, UR, hULopen, hULzero, hURopen, hURone, hrectangle⟩
  rcases hleft_basis UL hULopen hULzero with ⟨i, hi⟩
  rcases hright_basis UR hURopen hURone with ⟨j, hj⟩
  rcases hdir i j with ⟨k, hik, hjk⟩
  refine ⟨k, ?_⟩
  intro y hy
  have hycoords : stageLeft k y.left = 0 ∧ stageRight k y.right = 1 := by
    exact
      (freeProCZCCompletedFoxSemidirectStageMap_mem_ker_iff
        (ProC := ProC) (X := X) (H := H) (N := Nstage k) (n := nstage k)
        (stageLeft := stageLeft k) (stageRight := stageRight k)
        (hscalar := hscalar k) (y := y)).1 hy
  exact hrectangle y
    (hi y.left (hleft_mono hik y.left hycoords.1))
    (hj y.right (hright_mono hjk y.right hycoords.2))

end AbstractSemidirectComponentBasis

section BifilteredZCBasis

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable {J : Type v} [Preorder J]
variable (Nstage : J → Subgroup (FreeGroup X)) [∀ j, (Nstage j).Normal]
variable (nstage : J → ℕ) [∀ j, Fact (0 < nstage j)]
variable (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
variable (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
variable (zcIndex : J → ZCCompletedGroupAlgebraIndex ProC.finiteQuotientClass H)
variable (hzcIndex : ∀ {i j : J}, i ≤ j → zcIndex i ≤ zcIndex j)
variable (hmod : ∀ j : J, nstage j ∣ (zcIndex j).1.modulus)
variable (qmap : ∀ j : J,
  CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2 →*
    finiteFoxStageTargetQuotient (X := X) (Nstage j))

omit [TopologicalSpace (ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- The left coordinate kernels of the actual `Z_C[[H]]` bifiltered stage maps are monotone along
stage refinement. -/
theorem zcFreeFoxCoordinatesBifilteredStageMap_kernel_mono
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    {i j : J} (hij : i ≤ j)
    (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hv :
      zcFreeFoxCoordinatesBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage
        (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
        j v = 0) :
      zcFreeFoxCoordinatesBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage
        (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
        i v = 0 := by
  have htransition :=
    zcFreeFoxCoordinatesBifilteredStageMap_transition
      (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn
      (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
      (fun hij a =>
        zcCompletedGroupAlgebraBifilteredStageCoeffMap_transition
          (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
          hmod qmap hcoeff_mod hqmap_transition hij a)
      hij v
  -- The coefficient-map transition theorem above packages the exact finite target transition.
  -- Reading the displayed equality backwards shows that the coarser coordinate is the transition
  -- of the finer coordinate, hence a finer zero maps to a coarser zero.
  calc
    zcFreeFoxCoordinatesBifilteredStageMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage
        (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
        i v
        = finiteFoxStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij)
            (zcFreeFoxCoordinatesBifilteredStageMap
              (ProC := ProC) (X := X) (H := H) Nstage nstage
              (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
                (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
              j v) := htransition.symm
    _ = 0 := by
      rw [hv]
      funext x
      exact map_zero (finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij))

omit [TopologicalSpace (ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)] in
omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- The coefficient kernels of actual `Z_C[[H]]` bifiltered finite-stage maps are monotone along
stage refinement. -/
theorem zcCompletedGroupAlgebraBifilteredStageCoeffMap_kernel_mono
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    {i j : J} (hij : i ≤ j)
    (a : ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
    (ha :
      zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j a = 0) :
      zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap i a = 0 := by
  have htransition :=
    zcCompletedGroupAlgebraBifilteredStageCoeffMap_transition
      (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
      hmod qmap hcoeff_mod hqmap_transition hij a
  calc
    zcCompletedGroupAlgebraBifilteredStageCoeffMap
        (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap i a
        = finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij)
            (zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j a) :=
          htransition.symm
    _ = 0 := by
      rw [ha]
      exact map_zero (finiteFoxStageBifilteredTargetGroupAlgebraMap (X := X) (hN hij) (hn hij))

omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Additive kernel basis for completed Fox-coordinate projections, reduced to the coefficient
ring projections.  This is the next component-level target after semidirect kernel bases: prove the
coefficient maps `Z_C[[H]] -> (Z/n_j)[F/N_j]` have kernel neighbourhood basis, and the coordinate
result follows for finite `X`. -/
theorem zcFreeFoxCoordinatesBifilteredStageMap_additive_basis_of_coeff_basis
    [Fintype X] [Nonempty J]
    (hcoord_rect :
      HasFiniteCoordinateZeroRectangularNeighbourhoods
        (A := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H) (X := X))
    (hdir : Directed (· ≤ ·) (id : J → J))
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    (hcoeff_basis :
      HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
        (A := ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
        (fun j : J =>
          (zcCompletedGroupAlgebraBifilteredStageCoeffMap
            (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j).toAddMonoidHom)) :
    HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
      (A := ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
      (fun j : J =>
        zcFreeFoxCoordinatesBifilteredStageMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage
          (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
            (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k) j) := by
  change
    HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
      (A := X → ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)
      (fun j : J =>
        coordinatewiseAddMonoidHom (X := X)
          (fun k : J =>
            (zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k).toAddMonoidHom) j)
  exact
    coordinatewiseAdditiveKernelBasis_of_component_basis
      (X := X)
      (fun k : J =>
        (zcCompletedGroupAlgebraBifilteredStageCoeffMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k).toAddMonoidHom)
      hcoord_rect hdir hcoeff_basis
      (fun hij a ha =>
        zcCompletedGroupAlgebraBifilteredStageCoeffMap_kernel_mono
          (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
          hmod qmap hcoeff_mod hqmap_transition hij a ha)

omit [TopologicalSpace (ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)] in
omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- The right kernels of the automatically defined bifiltered stage maps are monotone along stage
refinement. -/
theorem zcCompletedGroupAlgebraBifilteredStageRightMap_kernel_mono
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    {i j : J} (hij : i ≤ j) (h : H)
    (hh :
      zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j h = 1) :
      zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap i h = 1 := by
  calc
    zcCompletedGroupAlgebraBifilteredStageRightMap
        (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap i h
        = finiteFoxStageTargetQuotientMap (X := X) (hN hij)
            (zcCompletedGroupAlgebraBifilteredStageRightMap
              (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j h) :=
          (zcCompletedGroupAlgebraBifilteredStageRightMap_transition
            (ProC := ProC) (X := X) (H := H) (Nstage := Nstage) (hN := hN)
            (zcIndex := zcIndex) (hzcIndex := hzcIndex) (qmap := qmap)
            hqmap_transition hij h).symm
    _ = 1 := by
      rw [hh]
      exact map_one (finiteFoxStageTargetQuotientMap (X := X) (hN hij))

omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Componentwise zero/identity kernel bases imply the identity-neighbourhood kernel basis for
the actual `Z_C[[H]]` bifiltered semidirect stage maps.

This removes the need to prove the semidirect kernel basis in one monolithic step: it is enough to
prove it for the completed Fox-coordinate projections and for the target quotient maps. -/
theorem freeProCZCFoxSemiZCBifilteredStageMap_identity_basis_of_component_bases
    (hrect : HasSemidirectRectangularIdentityNeighbourhoods
      (X := X) (H := H) ProC.finiteQuotientClass)
    (hdir : Directed (· ≤ ·) (id : J → J))
    (hcoeff_mod : ∀ {i j : J} (hij : i ≤ j),
      ∀ a : ModNCompletedCoeff (zcIndex j).1.modulus,
        modNCompletedCoeffMap
            (n := nstage i) (m := (zcIndex i).1.modulus) (hmod i)
            (modNCompletedCoeffMap
              (n := (zcIndex i).1.modulus) (m := (zcIndex j).1.modulus)
              (hzcIndex hij).1 a) =
          modNCompletedCoeffMap (n := nstage i) (m := nstage j) (hn hij)
            (modNCompletedCoeffMap
              (n := nstage j) (m := (zcIndex j).1.modulus) (hmod j) a))
    (hqmap_transition : ∀ {i j : J} (hij : i ≤ j),
      ∀ q : CompletedGroupAlgebraQuotientInClass H ProC.finiteQuotientClass (zcIndex j).2,
        qmap i
            ((OpenNormalSubgroupInClass.map
              (C := ProC.finiteQuotientClass) (G := H)
              (U := OrderDual.ofDual (zcIndex i).2)
              (V := OrderDual.ofDual (zcIndex j).2)
              (hzcIndex hij).2) q) =
          finiteFoxStageTargetQuotientMap (X := X) (hN hij) (qmap j q))
    (hleft_basis :
      HasAdditiveIdentityQuotientKernelNeighbourhoodBasis
        (A := ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
        (fun j : J =>
          zcFreeFoxCoordinatesBifilteredStageMap
            (ProC := ProC) (X := X) (H := H) Nstage nstage
            (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
              (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k) j))
    (hright_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := H)
        (fun j : J =>
          zcCompletedGroupAlgebraBifilteredStageRightMap
            (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j)) :
    HasIdentityQuotientKernelNeighbourhoodBasis
      (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
      (fun j : J =>
        freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap j) := by
  refine
    freeProCZCCompletedFoxSemidirectStageMap_identity_basis_of_component_bases
      (ProC := ProC) (X := X) (H := H) Nstage nstage hrect hdir
      (fun j =>
        zcFreeFoxCoordinatesBifilteredStageMap
          (ProC := ProC) (X := X) (H := H) Nstage nstage
          (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
            (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k) j)
      (fun j =>
        zcCompletedGroupAlgebraBifilteredStageRightMap
          (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap j)
      (fun j h v =>
        zcFreeFoxCoordinatesBifilteredStageMap_smul_groupLike
          (ProC := ProC) (X := X) (H := H) Nstage nstage
          (fun k => zcCompletedGroupAlgebraBifilteredStageCoeffMap
            (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k)
          (zcCompletedGroupAlgebraBifilteredStageRightMap
            (ProC := ProC) (X := X) (H := H) Nstage zcIndex qmap)
          (fun k h => zcCompletedGroupAlgebraBifilteredStageCoeffMap_groupLike_autoRight
            (ProC := ProC) (X := X) (H := H) Nstage nstage zcIndex hmod qmap k h)
          j h v)
      hleft_basis hright_basis ?_ ?_
  · intro i j hij v hv
    exact zcFreeFoxCoordinatesBifilteredStageMap_kernel_mono
      (ProC := ProC) (X := X) (H := H) Nstage nstage hN hn zcIndex hzcIndex
      hmod qmap hcoeff_mod hqmap_transition hij v hv
  · intro i j hij h hh
    exact zcCompletedGroupAlgebraBifilteredStageRightMap_kernel_mono
      (ProC := ProC) (X := X) (H := H) Nstage hN zcIndex hzcIndex qmap
      hqmap_transition hij h hh

end BifilteredZCBasis

end

end FoxDifferential
