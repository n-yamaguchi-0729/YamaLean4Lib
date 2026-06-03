import ProCGroups.ProC.Subgroups.Products

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/Quotients/LeftQuotientMaps.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

/-- The natural projection `G/K → G/H` for closed subgroups `K ≤ H`, viewed as a quotient-space
map on left cosets. -/
def leftQuotientProjection
    {G : Type u} [Group G] (K H : Subgroup G) (hKH : K ≤ H) :
    G ⧸ K → G ⧸ H :=
  Quotient.map' id <| by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    exact hKH hab

variable {G : Type u} [Group G]

/-- The projection on left quotients sends the class of `g` modulo `K` to the class of `g`
modulo `H`. -/
@[simp] theorem leftQuotientProjection_mk
    (K H : Subgroup G) (hKH : K ≤ H) (g : G) :
    leftQuotientProjection K H hKH (QuotientGroup.mk (s := K) g) =
      QuotientGroup.mk (s := H) g := by
  rfl

/-- The natural map between nested left quotients is continuous. -/
theorem continuous_leftQuotientProjection
    [TopologicalSpace G]
    (K H : Subgroup G) (hKH : K ≤ H) :
    Continuous (leftQuotientProjection K H hKH : G ⧸ K → G ⧸ H) := by
  refine (QuotientGroup.isQuotientMap_mk K).continuous_iff.2 ?_
  simpa [Function.comp, leftQuotientProjection_mk] using
    (QuotientGroup.continuous_mk : Continuous (QuotientGroup.mk (s := H) : G → G ⧸ H))

/-- The left-quotient projection to itself is the identity. -/
@[simp] theorem leftQuotientProjection_id
    (K : Subgroup G) :
    leftQuotientProjection K K le_rfl = id := by
  funext x
  refine Quotient.inductionOn x ?_
  intro g
  rfl

/-- Left-quotient projections compose along chains of subgroup inclusions. -/
@[simp] theorem leftQuotientProjection_comp
    (K H L : Subgroup G) (hKH : K ≤ H) (hHL : H ≤ L) :
    leftQuotientProjection H L hHL ∘ leftQuotientProjection K H hKH =
      leftQuotientProjection K L (hKH.trans hHL) := by
  funext x
  refine Quotient.inductionOn x ?_
  intro g
  rfl

/-- Pointwise form of the composition law for left-quotient projections. -/
@[simp] theorem leftQuotientProjection_comp_apply
    (K H L : Subgroup G) (hKH : K ≤ H) (hHL : H ≤ L) (x : G ⧸ K) :
    leftQuotientProjection H L hHL (leftQuotientProjection K H hKH x) =
      leftQuotientProjection K L (hKH.trans hHL) x := by
  simpa using congrArg (fun f => f x) (leftQuotientProjection_comp (K := K) (H := H) (L := L)
    hKH hHL)

/-- Symmetric pointwise form of the composition law for left-quotient projections. -/
theorem leftQuotientProjection_comp_apply_symm
    (K H L : Subgroup G) (hKH : K ≤ H) (hHL : H ≤ L) (x : G ⧸ K) :
    leftQuotientProjection K L (hKH.trans hHL) x =
      leftQuotientProjection H L hHL (leftQuotientProjection K H hKH x) := by
  exact (leftQuotientProjection_comp_apply (K := K) (H := H) (L := L) hKH hHL x).symm

/-- The natural map between nested left quotients is surjective. -/
theorem surjective_leftQuotientProjection
    (K H : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (leftQuotientProjection K H hKH : G ⧸ K → G ⧸ H) := by
  intro x
  refine Quotient.inductionOn x ?_
  intro g
  exact ⟨QuotientGroup.mk (s := K) g, rfl⟩

/-- Left-quotient projections are equivariant for the ambient left action of `G`. -/
@[simp] theorem leftQuotientProjection_smul
    (K H : Subgroup G) (hKH : K ≤ H) (g : G) (x : G ⧸ K) :
    leftQuotientProjection K H hKH (g • x) =
      g • leftQuotientProjection K H hKH x := by
  refine Quotient.inductionOn x ?_
  intro y
  rfl

end ProCGroups.ProC
