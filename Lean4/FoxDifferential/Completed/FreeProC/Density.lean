import FoxDifferential.Completed.FreeProC.SemidirectLift

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/FreeProC/Density.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Density criteria for the free pro-C completed Fox graph

This file turns the remaining completion step into reusable topology and finite-stage APIs.
The main target is the statement that every completed Fox boundary cycle `(v, 1)` is a limit of
algebraic kernel-word cycles `(D w, 1)`.

The declarations below do not assert that density is automatic.  They reduce it to concrete
neighbourhood or open-subgroup approximation statements, which are the forms produced by finite
quotient arguments.
-/

namespace FoxDifferential

noncomputable section

universe u v

section GenericClosureAPI

variable {Y : Type u} [TopologicalSpace Y]
variable {S T : Set Y}

/-- A direct neighbourhood approximation criterion for set-theoretic closure.

This is the form used when a finite-stage argument has already produced an algebraic point of
`S` inside every open neighbourhood of a boundary point. -/
theorem subset_closure_of_open_neighbourhood_approximation
    (happrox :
      ∀ y : Y, y ∈ T → ∀ U : Set Y, IsOpen U → y ∈ U →
        ∃ s : Y, s ∈ S ∧ s ∈ U) :
    T ⊆ closure S := by
  intro y hy
  rw [mem_closure_iff]
  intro U hU hyU
  rcases happrox y hy U hU hyU with ⟨s, hsS, hsU⟩
  exact ⟨s, hsU, hsS⟩

end GenericClosureAPI

section OpenSubgroupClosureAPI

variable {Y : Type u} [Group Y] [TopologicalSpace Y]
variable {S T : Set Y}

/-- Left open subgroup neighbourhood basis, stated as a proposition rather than a structure.

For every neighbourhood `U` of `y`, one can find an open subgroup `V` such that the left coset
`y V` is contained in `U`.  This is the exact topological input needed to pass from finite/open
subgroup approximations to ordinary closure. -/
def HasLeftOpenSubgroupNeighbourhoodBasis (Y : Type u) [Group Y] [TopologicalSpace Y] : Prop :=
  ∀ (y : Y) (U : Set Y), IsOpen U → y ∈ U →
    ∃ V : Subgroup Y, IsOpen ((V : Subgroup Y) : Set Y) ∧
      ∀ z : Y, z ∈ V → y * z ∈ U

/-- A normal-subgroup version of the left open subgroup neighbourhood basis.

This is the form naturally supplied by profinite finite-quotient separation, where neighbourhoods
of the identity are refined by open normal subgroups. -/
def HasLeftOpenNormalSubgroupNeighbourhoodBasis
    (Y : Type u) [Group Y] [TopologicalSpace Y] : Prop :=
  ∀ (y : Y) (U : Set Y), IsOpen U → y ∈ U →
    ∃ V : Subgroup Y, V.Normal ∧ IsOpen ((V : Subgroup Y) : Set Y) ∧
      ∀ z : Y, z ∈ V → y * z ∈ U

/-- The normal-subgroup basis implies the subgroup basis. -/
theorem HasLeftOpenNormalSubgroupNeighbourhoodBasis.to_subgroup_basis
    (hbasis : HasLeftOpenNormalSubgroupNeighbourhoodBasis Y) :
    HasLeftOpenSubgroupNeighbourhoodBasis Y := by
  intro y U hU hyU
  rcases hbasis y U hU hyU with ⟨V, _hVnormal, hVopen, hVcoset⟩
  exact ⟨V, hVopen, hVcoset⟩

/-- Closure criterion using open-subgroup approximations.

It is enough to approximate each `y ∈ T` modulo every open subgroup `V`, in the sense that for
some `s ∈ S` the correction `y⁻¹ * s` lies in `V`. -/
theorem subset_closure_of_openSubgroup_approximation
    (hbasis : HasLeftOpenSubgroupNeighbourhoodBasis Y)
    (happrox :
      ∀ y : Y, y ∈ T → ∀ V : Subgroup Y,
        IsOpen ((V : Subgroup Y) : Set Y) →
          ∃ s : Y, s ∈ S ∧ y⁻¹ * s ∈ V) :
    T ⊆ closure S := by
  refine subset_closure_of_open_neighbourhood_approximation ?_
  intro y hy U hU hyU
  rcases hbasis y U hU hyU with ⟨V, hVopen, hVcoset⟩
  rcases happrox y hy V hVopen with ⟨s, hsS, hsV⟩
  refine ⟨s, hsS, ?_⟩
  have hcoset : y * (y⁻¹ * s) ∈ U := hVcoset (y⁻¹ * s) hsV
  simpa [mul_assoc] using hcoset

/-- Closure criterion using open-normal-subgroup approximations. -/
theorem subset_closure_of_openNormalSubgroup_approximation
    (hbasis : HasLeftOpenNormalSubgroupNeighbourhoodBasis Y)
    (happrox :
      ∀ y : Y, y ∈ T → ∀ V : Subgroup Y,
        V.Normal → IsOpen ((V : Subgroup Y) : Set Y) →
          ∃ s : Y, s ∈ S ∧ y⁻¹ * s ∈ V) :
    T ⊆ closure S := by
  refine subset_closure_of_open_neighbourhood_approximation ?_
  intro y hy U hU hyU
  rcases hbasis y U hU hyU with ⟨V, hVnormal, hVopen, hVcoset⟩
  rcases happrox y hy V hVnormal hVopen with ⟨s, hsS, hsV⟩
  refine ⟨s, hsS, ?_⟩
  have hcoset : y * (y⁻¹ * s) ∈ U := hVcoset (y⁻¹ * s) hsV
  simpa [mul_assoc] using hcoset

/-- Coset approximation gives a pointwise closure statement. -/
theorem mem_closure_of_openSubgroup_approximation
    (hbasis : HasLeftOpenSubgroupNeighbourhoodBasis Y)
    {y : Y} (_hy : y ∈ T)
    (happrox :
      ∀ V : Subgroup Y, IsOpen ((V : Subgroup Y) : Set Y) →
        ∃ s : Y, s ∈ S ∧ y⁻¹ * s ∈ V) :
    y ∈ closure S := by
  rw [mem_closure_iff]
  intro U hU hyU
  rcases hbasis y U hU hyU with ⟨V, hVopen, hVcoset⟩
  rcases happrox V hVopen with ⟨s, hsS, hsV⟩
  refine ⟨s, ?_, hsS⟩
  have hcoset : y * (y⁻¹ * s) ∈ U := hVcoset (y⁻¹ * s) hsV
  simpa [mul_assoc] using hcoset

end OpenSubgroupClosureAPI

section QuotientKernelClosureAPI

variable {Y : Type u} [Group Y] [TopologicalSpace Y]
variable {S T : Set Y}

/-- A left neighbourhood basis expressed directly by kernels of quotient maps.

This is the form produced by finite-stage maps: every open neighbourhood of `y` contains a
left coset `y * ker π_j`. -/
def HasLeftQuotientKernelNeighbourhoodBasis
    {J : Type v} {Q : J → Type*} [∀ j, Group (Q j)]
    (π : ∀ j : J, Y →* Q j) : Prop :=
  ∀ (y : Y) (U : Set Y), IsOpen U → y ∈ U →
    ∃ j : J, ∀ z : Y, z ∈ (π j).ker → y * z ∈ U

/-- If quotient kernels form a left neighbourhood basis, then equality at every quotient stage
gives closure.

This is the abstract topology step for the remaining Crowell density theorem: finite quotient
exactness supplies `s ∈ S` with `π_j s = π_j y`; the quotient-kernel basis turns this into
ordinary topological approximation. -/
theorem subset_closure_of_quotientKernel_approximation
    {J : Type v} {Q : J → Type*} [∀ j, Group (Q j)]
    (π : ∀ j : J, Y →* Q j)
    (hbasis : HasLeftQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (happrox :
      ∀ y : Y, y ∈ T → ∀ j : J,
        ∃ s : Y, s ∈ S ∧ π j s = π j y) :
    T ⊆ closure S := by
  refine subset_closure_of_open_neighbourhood_approximation ?_
  intro y hy U hU hyU
  rcases hbasis y U hU hyU with ⟨j, hj⟩
  rcases happrox y hy j with ⟨s, hsS, hπ⟩
  have hker : y⁻¹ * s ∈ (π j).ker := by
    change π j (y⁻¹ * s) = 1
    rw [map_mul, map_inv, hπ]
    simp only [inv_mul_cancel]
  refine ⟨s, hsS, ?_⟩
  have hsU : y * (y⁻¹ * s) ∈ U := hj (y⁻¹ * s) hker
  simpa [mul_assoc] using hsU

end QuotientKernelClosureAPI

section CompletedFoxDensity

open scoped Topology

variable {ProC : ProCGroups.ProC.ProCGroupPredicate}
variable {X H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [DecidableEq X]
variable [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]

/-- The semidirect point `(D w, 1)` attached to an abstract free-group kernel word candidate.

The word may or may not actually lie in the kernel.  Kernel membership is recorded separately in
lemmas such as `freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet`. -/
def freeProCZCCompletedFoxSemidirectKernelWordPoint (φ : X → H) (w : FreeGroup X) :
    ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H :=
  { left :=
      zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass (FreeGroup.lift φ) w,
    right := (1 : H) }

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
@[simp]
theorem freeProCZCCompletedFoxSemidirectKernelWordPoint_left
    (φ : X → H) (w : FreeGroup X) :
    (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w).left =
      zcFreeGroupFoxDerivativeVector ProC.finiteQuotientClass (FreeGroup.lift φ) w :=
  rfl

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
@[simp]
theorem freeProCZCCompletedFoxSemidirectKernelWordPoint_right
    (φ : X → H) (w : FreeGroup X) :
    (freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w).right = 1 :=
  rfl

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- A genuine kernel word gives an element of the algebraic kernel-word cycle set. -/
theorem freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
    (φ : X → H) {w : FreeGroup X} (hw : FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w ∈
      freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ := by
  exact ⟨w, hw, rfl⟩

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Expanded membership form for the algebraic kernel-word cycle set. -/
theorem mem_freeProCZCCompletedFoxSemidirectKernelCycleSet_iff
    (φ : X → H)
    (y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) :
    y ∈ freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ ↔
      ∃ w : FreeGroup X, FreeGroup.lift φ w = 1 ∧
        y = freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w := by
  constructor
  · intro hy
    rcases hy with ⟨w, hw, hy⟩
    exact ⟨w, hw, hy⟩
  · rintro ⟨w, hw, hy⟩
    rw [hy]
    exact freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
      (ProC := ProC) φ hw

omit [TopologicalSpace (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
omit [DecidableEq X] in
/-- Boundary-cycle membership for a displayed point `(v, 1)`. -/
theorem freeProCZCCompletedFoxSemidirectBoundaryCycleSet_mk_iff
    [Fintype X] (φ : X → H)
    (v : ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H)) :
    ({ left := v, right := (1 : H) } :
        ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) ∈
      freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ↔
        zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ) v = 0 := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨rfl, h⟩

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Quotient-kernel approximation form of the completed Fox density statement.

This is the finite-stage attack surface for the remaining density theorem: once finite quotient
exactness produces, for every finite quotient stage `j`, a kernel word whose semidirect point has
the same `j`-th quotient image as the boundary cycle, the completed density statement follows. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_quotKernel_approx
    [Fintype X] (φ : X → H)
    {J : Type v} {Q : J → Type*} [∀ j, Group (Q j)]
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H →* Q j)
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H) π)
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ j : J,
            ∃ w : FreeGroup X,
              FreeGroup.lift φ w = 1 ∧
                π j (freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (ProC := ProC) φ w) = π j y) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  refine subset_closure_of_quotientKernel_approximation
    (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (S := freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ)
    (T := freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ)
    π hbasis ?_
  intro y hy j
  rcases happrox y hy j with ⟨w, hw, hπ⟩
  exact
    ⟨freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w,
      freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
        (ProC := ProC) φ hw,
      hπ⟩

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Neighbourhood approximation form of the completed Fox density statement.

For every boundary cycle and every open neighbourhood of it in the completed semidirect product,
there is a genuine kernel word whose point `(D w, 1)` lies in that neighbourhood.  This proves the
set-level density statement used by the Crowell middle exactness theorem. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_open_neighbourhood_approx
    [Fintype X] (φ : X → H)
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ U : Set (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H),
            IsOpen U → y ∈ U →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w ∈ U) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  refine subset_closure_of_open_neighbourhood_approximation ?_
  intro y hy U hU hyU
  rcases happrox y hy U hU hyU with ⟨w, hw, hUmem⟩
  refine ⟨freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w, ?_, hUmem⟩
  exact freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
    (ProC := ProC) φ hw

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Open-subgroup approximation form of the completed Fox density statement.

This is the intended entry point for finite quotient arguments: for every open subgroup `V` of
the completed Fox semidirect group, approximate a boundary cycle `y` by a kernel-word cycle point
modulo the left coset `y V`. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_openSubgroup_approx
    [Fintype X] (φ : X → H)
    (hbasis :
      HasLeftOpenSubgroupNeighbourhoodBasis
        (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ V : Subgroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H),
            IsOpen ((V : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                y⁻¹ * freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (ProC := ProC) φ w ∈ V) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  refine subset_closure_of_openSubgroup_approximation
    (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (S := freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ)
    (T := freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ)
    hbasis ?_
  intro y hy V hVopen
  rcases happrox y hy V hVopen with ⟨w, hw, hVmem⟩
  exact
    ⟨freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w,
      freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
        (ProC := ProC) φ hw,
      hVmem⟩

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Open-normal-subgroup approximation form of the completed Fox density statement. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_openNormalSubgroup_approx
    [Fintype X] (φ : X → H)
    (hbasis :
      HasLeftOpenNormalSubgroupNeighbourhoodBasis
        (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ V : Subgroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H),
            V.Normal →
            IsOpen ((V : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                y⁻¹ * freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (ProC := ProC) φ w ∈ V) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) := by
  refine subset_closure_of_openNormalSubgroup_approximation
    (Y := ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)
    (S := freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ)
    (T := freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ)
    hbasis ?_
  intro y hy V hVnormal hVopen
  rcases happrox y hy V hVnormal hVopen with ⟨w, hw, hVmem⟩
  exact
    ⟨freeProCZCCompletedFoxSemidirectKernelWordPoint (ProC := ProC) φ w,
      freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
        (ProC := ProC) φ hw,
      hVmem⟩

/-- Open-subgroup approximation places every completed boundary cycle inside the closed
generated Fox graph target. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_openSubgroup_approx
    [Fintype X] (φ : X → H)
    (hbasis :
      HasLeftOpenSubgroupNeighbourhoodBasis
        (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ V : Subgroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H),
            IsOpen ((V : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                y⁻¹ * freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (ProC := ProC) φ w ∈ V) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density
      (ProC := ProC) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_openSubgroup_approx
        (ProC := ProC) φ hbasis happrox)

/-- Open-normal-subgroup approximation places every completed boundary cycle inside the closed
generated Fox graph target. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_openNormalSubgroup_approx
    [Fintype X] (φ : X → H)
    (hbasis :
      HasLeftOpenNormalSubgroupNeighbourhoodBasis
        (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ V : Subgroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H),
            V.Normal →
            IsOpen ((V : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                y⁻¹ * freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (ProC := ProC) φ w ∈ V) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget
        (ProC := ProC) φ : Subgroup
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
          (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density
      (ProC := ProC) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_openNormalSubgroup_approx
        (ProC := ProC) φ hbasis happrox)

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)] in
/-- Under the standard continuity inputs, open-subgroup approximation upgrades the one-sided
closure statement to the equality between boundary cycles and the closure of kernel-word cycles. -/
theorem closure_freeProCZCFoxSemiKernelCycleSet_eq_boundaryCycleSet_of_openSubgroup_approx
    [Fintype X] [T1Space H]
    [TopologicalSpace (ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)]
    [T1Space (ZCCompletedGroupAlgebra ProC.finiteQuotientClass H)]
    (φ : X → H)
    (hleft :
      Continuous
        (fun y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H => y.left))
    (hright :
      Continuous
        (fun y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H => y.right))
    (hboundary :
      Continuous
        (zcFreeGroupFoxBoundary ProC.finiteQuotientClass (FreeGroup.lift φ)))
    (hbasis :
      HasLeftOpenSubgroupNeighbourhoodBasis
        (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H))
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ →
          ∀ V : Subgroup (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H),
            IsOpen ((V : Subgroup
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) : Set
              (ZCCompletedFoxSemidirect ProC.finiteQuotientClass X H)) →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                y⁻¹ * freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (ProC := ProC) φ w ∈ V) :
    closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (ProC := ProC) φ) =
      freeProCZCCompletedFoxSemidirectBoundaryCycleSet (ProC := ProC) φ := by
  exact
    (closure_freeProCZCFoxSemiKernelCycleSet_eq_boundaryCycleSet_iff_density
      (ProC := ProC) φ hleft hright hboundary).2
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_openSubgroup_approx
        (ProC := ProC) φ hbasis happrox)

end CompletedFoxDensity

end

end FoxDifferential
