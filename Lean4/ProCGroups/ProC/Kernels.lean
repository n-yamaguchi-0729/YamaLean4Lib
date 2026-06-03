import Mathlib.GroupTheory.Abelianization.Defs
import ProCGroups.Abelian.TopologicalAbelianization
import ProCGroups.ProC.Subgroups.Closed

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/Kernels.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

namespace ProCGroups.ProC

noncomputable section

open scoped Pointwise

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The kernel subgroup of a continuous homomorphism. -/
abbrev ProfiniteKernelSubgroup (psi : ContinuousMonoidHom G H) : Subgroup G :=
  psi.toMonoidHom.ker

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The kernel of a continuous homomorphism into a `T1` topological group is closed. -/
theorem isClosed_profiniteKernelSubgroup [T1Space H] (psi : ContinuousMonoidHom G H) :
    IsClosed ((ProfiniteKernelSubgroup psi : Subgroup G) : Set G) := by
  simpa [ProfiniteKernelSubgroup, MonoidHom.mem_ker] using
    (isClosed_singleton (x := (1 : H))).preimage psi.continuous_toFun

/-- The topological kernel abelianization
`ker psi / closure([ker psi, ker psi])`. -/
abbrev ProfiniteKernelAbelianization (psi : ContinuousMonoidHom G H) : Type u :=
  TopologicalAbelianization (ProfiniteKernelSubgroup psi)

/-- Additive notation for the topological kernel abelianization. -/
abbrev ProfiniteKernelAbelianizationAdd (psi : ContinuousMonoidHom G H) : Type u :=
  Additive (ProfiniteKernelAbelianization psi)

/-- Pro-`C` notation for the topological kernel abelianization.

The `ProC` parameter records the ambient pro-`C` theory in theorem statements; the underlying type
is the ordinary topological abelianization of the closed kernel. -/
abbrev ProCKernelAbelianization
    (ProC : ProCGroupPredicate.{u}) (psi : ContinuousMonoidHom G H) : Type u :=
  let _proCMarker : ProCGroupPredicate.{u} := ProC
  ProfiniteKernelAbelianization psi

/-- Additive notation for the pro-`C` kernel abelianization. -/
abbrev ProCKernelAbelianizationAdd
    (ProC : ProCGroupPredicate.{u}) (psi : ContinuousMonoidHom G H) : Type u :=
  Additive (ProCKernelAbelianization ProC psi)

/-- Canonical quotient map from the algebraic kernel abelianization to the topological kernel
abelianization. -/
def kernelAbelianizationToProfiniteKernelAbelianizationHom
    (psi : ContinuousMonoidHom G H) :
    Abelianization (ProfiniteKernelSubgroup psi) →*
      ProfiniteKernelAbelianization psi :=
  QuotientGroup.lift
    (commutator (ProfiniteKernelSubgroup psi))
    (QuotientGroup.mk'
      (Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)))
    (by
      intro x hx
      exact
        (QuotientGroup.eq_one_iff
          (N := Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)) x).2
          (Subgroup.commutator_le_closedCommutator (ProfiniteKernelSubgroup psi) hx))

/-- Additive form of the quotient from `(ker psi)^ab` to the topological kernel
abelianization. -/
def kernelAbelianizationToProfiniteKernelAbelianization
    (psi : ContinuousMonoidHom G H) :
    Additive (Abelianization (ProfiniteKernelSubgroup psi)) →+
      ProfiniteKernelAbelianizationAdd psi :=
  (kernelAbelianizationToProfiniteKernelAbelianizationHom
    (G := G) (H := H) psi).toAdditive

omit [IsTopologicalGroup H] in
/-- The canonical quotient map sends the class of a kernel element to its class modulo the
topological closure of the commutator subgroup. -/
@[simp]
theorem kernelAbelianizationToProfiniteKernelAbelianization_of
    (psi : ContinuousMonoidHom G H) (n : ProfiniteKernelSubgroup psi) :
    kernelAbelianizationToProfiniteKernelAbelianization
        (G := G) (H := H) psi (Additive.ofMul (Abelianization.of n)) =
      Additive.ofMul
        (QuotientGroup.mk'
          (Subgroup.closedCommutator (ProfiniteKernelSubgroup psi)) n) := by
  rfl

omit [IsTopologicalGroup H] in
/-- The canonical map from the algebraic kernel abelianization to the topological one is
surjective. -/
theorem kernelAbelianizationToProfiniteKernelAbelianization_surjective
    (psi : ContinuousMonoidHom G H) :
    Function.Surjective
      (kernelAbelianizationToProfiniteKernelAbelianization
        (G := G) (H := H) psi) := by
  intro x
  change ∃ y : Additive (Abelianization (ProfiniteKernelSubgroup psi)),
    Additive.ofMul
      (kernelAbelianizationToProfiniteKernelAbelianizationHom
        (G := G) (H := H) psi (Additive.toMul y)) = x
  rcases QuotientGroup.mk'_surjective
      (Subgroup.closedCommutator (ProfiniteKernelSubgroup psi))
      (Additive.toMul x) with
    ⟨n, hn⟩
  refine ⟨Additive.ofMul (Abelianization.of n), ?_⟩
  apply Additive.toMul.injective
  simpa using hn

omit [IsTopologicalGroup H] in
/-- The closed kernel of a morphism out of a pro-`C` group is pro-`C`. -/
theorem proCGroup_profiniteKernelSubgroup
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.HasFiniteQuotientHereditary]
    [ProC.DeterminedByFiniteQuotients] [ProCGroup ProC G]
    [T1Space H] (psi : ContinuousMonoidHom G H) :
    ProCGroup ProC (ProfiniteKernelSubgroup psi) :=
  ProCGroup.of_isClosed_subgroup ProC (ProfiniteKernelSubgroup psi)
    (isClosed_profiniteKernelSubgroup psi)

omit [IsTopologicalGroup H] in
/-- The closed kernel of a morphism between pro-`C` groups is pro-`C`.

This form avoids an extra public `[T1Space H]` assumption because the pro-`C` target is Hausdorff. -/
theorem proCGroup_profiniteKernelSubgroup_of_proCGroupTarget
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.HasFiniteQuotientHereditary]
    [ProC.DeterminedByFiniteQuotients] [ProCGroup ProC G]
    {H0 : Type u} [Group H0] [TopologicalSpace H0] [IsTopologicalGroup H0]
    [ProCGroup ProC H0] (psi : ContinuousMonoidHom G H0) :
    ProCGroup ProC (ProfiniteKernelSubgroup psi) := by
  letI : T1Space H0 := ProCGroup.t1Space ProC H0
  exact proCGroup_profiniteKernelSubgroup (G := G) (H := H0) ProC psi

/-- Public namespace form: the kernel of a morphism of pro-`C` groups is pro-`C`. -/
theorem ProCGroup.profiniteKernelSubgroup
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.HasFiniteQuotientHereditary]
    [ProC.DeterminedByFiniteQuotients]
    {G H0 : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H0] [TopologicalSpace H0] [IsTopologicalGroup H0]
    [ProCGroup ProC G] [ProCGroup ProC H0]
    (psi : ContinuousMonoidHom G H0) :
    ProCGroup ProC (ProfiniteKernelSubgroup psi) :=
  proCGroup_profiniteKernelSubgroup_of_proCGroupTarget
    (G := G) (H0 := H0) ProC psi

omit [IsTopologicalGroup H] in
/-- The topological kernel abelianization of a morphism out of a pro-`C` group is pro-`C`. -/
theorem proCGroup_profiniteKernelAbelianization
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.HasFiniteQuotientHereditary]
    [ProC.DeterminedByFiniteQuotients] [ProCGroup ProC G]
    [T1Space H] (psi : ContinuousMonoidHom G H) :
    ProCGroup ProC (ProCKernelAbelianization ProC psi) := by
  let N : Subgroup G := ProfiniteKernelSubgroup psi
  letI : ProCGroup ProC N :=
    proCGroup_profiniteKernelSubgroup (G := G) (H := H) ProC psi
  change ProCGroup ProC (N ⧸ Subgroup.closedCommutator N)
  exact ProCGroup.quotient_closedNormalSubgroup ProC
    (Subgroup.closedCommutator N)
    (Subgroup.isClosed_closedCommutator N)

omit [IsTopologicalGroup H] in
/-- The topological kernel abelianization of a morphism between pro-`C` groups is pro-`C`,
without an extra public `[T1Space H]` assumption. -/
theorem proCGroup_profiniteKernelAbelianization_of_proCGroupTarget
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.HasFiniteQuotientHereditary]
    [ProC.DeterminedByFiniteQuotients] [ProCGroup ProC G]
    {H0 : Type u} [Group H0] [TopologicalSpace H0] [IsTopologicalGroup H0]
    [ProCGroup ProC H0] (psi : ContinuousMonoidHom G H0) :
    ProCGroup ProC (ProCKernelAbelianization ProC psi) := by
  letI : T1Space H0 := ProCGroup.t1Space ProC H0
  exact proCGroup_profiniteKernelAbelianization (G := G) (H := H0) ProC psi

/-- Public namespace form: the topological `N^ab(C)` of a morphism of pro-`C` groups is pro-`C`. -/
theorem ProCGroup.profiniteKernelAbelianization
    (ProC : ProCGroupPredicate.{u})
    [ProC.HasFiniteQuotientMelnikovFormation] [ProC.HasFiniteQuotientHereditary]
    [ProC.DeterminedByFiniteQuotients]
    {G H0 : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H0] [TopologicalSpace H0] [IsTopologicalGroup H0]
    [ProCGroup ProC G] [ProCGroup ProC H0]
    (psi : ContinuousMonoidHom G H0) :
    ProCGroup ProC (ProCKernelAbelianization ProC psi) :=
  proCGroup_profiniteKernelAbelianization_of_proCGroupTarget
    (G := G) (H0 := H0) ProC psi

end

end ProCGroups.ProC
