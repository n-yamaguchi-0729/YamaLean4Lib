import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import ProCGroups.Topologies.ContinuousMonoidHom

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Topologies/ContinuousMulEquiv.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Topological group constructions

Topological subgroup, quotient, continuous homomorphism, continuous equivalence, conjugation, and full-subgroup-topology lemmas.
-/

namespace ContinuousMulEquiv

universe u v

section

variable {G : Type u} {H : Type v}
variable [Group G] [Group H]
variable [TopologicalSpace G] [TopologicalSpace H]

/-- The continuous monoid homomorphism induced by a continuous multiplicative equivalence. -/
def toContinuousMonoidHom (e : G ≃ₜ* H) : G →ₜ* H :=
  { toMonoidHom := e.toMulEquiv.toMonoidHom
    continuous_toFun := e.continuous_toFun }

/-- The continuous monoid homomorphism underlying a continuous multiplicative equivalence evaluates as the equivalence. -/
@[simp] theorem toContinuousMonoidHom_apply (e : G ≃ₜ* H) (g : G) :
    e.toContinuousMonoidHom g = e g :=
  rfl

/-- Build a continuous multiplicative equivalence from inverse continuous homomorphisms. -/
noncomputable def ofHomInv
    (f : G →ₜ* H) (g : H →ₜ* G)
    (hleft : Function.LeftInverse g f)
    (hright : Function.RightInverse g f) :
    G ≃ₜ* H :=
  { toMulEquiv :=
      { toFun := f
        invFun := g
        left_inv := hleft
        right_inv := hright
        map_mul' := f.map_mul }
    continuous_toFun := f.continuous_toFun
    continuous_invFun := g.continuous_toFun }

@[simp] theorem ofHomInv_apply
    (f : G →ₜ* H) (g : H →ₜ* G)
    (hleft : Function.LeftInverse g f)
    (hright : Function.RightInverse g f) (x : G) :
    ofHomInv f g hleft hright x = f x :=
  rfl

end

/-- Upgrade a bijective continuous homomorphism from a compact topological group to a Hausdorff
topological group to a continuous multiplicative equivalence. -/
noncomputable def ofBijectiveCompactToT2
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    [CompactSpace G] [T2Space H]
    (φ : G →* H) (hφcont : Continuous φ)
    (hφ : Function.Bijective φ) :
    G ≃ₜ* H := by
  let e : G ≃ H := Equiv.ofBijective φ hφ
  let eh : G ≃ₜ H :=
    e.toHomeomorphOfContinuousClosed hφcont (Continuous.isClosedMap hφcont)
  exact ContinuousMulEquiv.mk' eh (by
    intro x y
    exact φ.map_mul x y)

@[simp 900] theorem ofBijectiveCompactToT2_apply
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    [CompactSpace G] [T2Space H]
    (φ : G →* H) (hφcont : Continuous φ)
    (hφ : Function.Bijective φ) (x : G) :
    ofBijectiveCompactToT2 φ hφcont hφ x = φ x := by
  unfold ofBijectiveCompactToT2
  rfl

end ContinuousMulEquiv

namespace ContinuousMonoidHom

universe u v

/-- The first isomorphism theorem for continuous monoid homomorphisms from a compact group to a
Hausdorff group, with the quotient and range carrying their induced topologies. -/
noncomputable def quotientKerContinuousMulEquivRange
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G] [CompactSpace G]
    [Group H] [TopologicalSpace H] [T2Space H]
    (f : G →ₜ* H) :
    (G ⧸ (f.toMonoidHom.ker : Subgroup G)) ≃ₜ* f.toMonoidHom.range := by
  let φ : (G ⧸ (f.toMonoidHom.ker : Subgroup G)) →* f.toMonoidHom.range :=
    (QuotientGroup.quotientKerEquivRange f.toMonoidHom).toMonoidHom
  have hφcont : Continuous φ := by
    refine (QuotientGroup.isQuotientMap_mk f.toMonoidHom.ker).continuous_iff.2 ?_
    simpa [φ, ContinuousMonoidHom.rangeRestrict] using f.rangeRestrict.continuous_toFun
  exact ContinuousMulEquiv.ofBijectiveCompactToT2 φ hφcont
    (QuotientGroup.quotientKerEquivRange f.toMonoidHom).bijective

/-- The quotient-by-kernel equivalence to the range sends a representative to its image. -/
@[simp] theorem quotientKerContinuousMulEquivRange_mk
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G] [CompactSpace G]
    [Group H] [TopologicalSpace H] [T2Space H]
    (f : G →ₜ* H) (g : G) :
    quotientKerContinuousMulEquivRange f
        (QuotientGroup.mk' (f.toMonoidHom.ker : Subgroup G) g) =
      f.toMonoidHom.rangeRestrict g :=
  rfl

/-- Coercing the quotient-by-kernel equivalence to the codomain gives the original homomorphism value. -/
@[simp] theorem coe_quotientKerContinuousMulEquivRange_mk
    {G : Type u} {H : Type v}
    [Group G] [TopologicalSpace G] [CompactSpace G]
    [Group H] [TopologicalSpace H] [T2Space H]
    (f : G →ₜ* H) (g : G) :
    (quotientKerContinuousMulEquivRange f
        (QuotientGroup.mk' (f.toMonoidHom.ker : Subgroup G) g) : H) = f g :=
  rfl

end ContinuousMonoidHom
