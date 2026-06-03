import Mathlib.Topology.Algebra.Group.Quotient
import ProCGroups.ProC.GroupPredicate

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/MaximalQuotients/ResidualCore.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open Set

namespace ProCGroups.ProC

universe u

section

variable {ProC : ProCGroupPredicate}

/-- Bundled closed normal kernels whose quotient is pro-`C`. -/
structure ProCQuotientKernel
    (ProC : ProCGroupPredicate)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  toSubgroup : Subgroup G
  normal : toSubgroup.Normal
  quotient_isProC : letI := normal; ProC (G := G ⧸ toSubgroup)

attribute [instance] ProCQuotientKernel.normal

/-- The residual core `R_C(G)`, defined as the intersection of all normal kernels with
pro-`C` quotient. -/
noncomputable def proCResidualCore
    (ProC : ProCGroupPredicate)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Subgroup G :=
  sInf (Set.range fun N : ProCQuotientKernel ProC G => N.toSubgroup)

/-- The residual core is a normal subgroup. -/
@[instance]
theorem proCResidualCore_normal
    (ProC : ProCGroupPredicate)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    (proCResidualCore ProC G).Normal := by
  change
    (sInf (Set.range fun N : ProCQuotientKernel ProC G => N.toSubgroup)).Normal
  simpa [proCResidualCore, sInf_range] using
    (Subgroup.normal_iInf_normal
      (a := fun N : ProCQuotientKernel ProC G => N.toSubgroup)
      (norm := fun N => N.normal))
/-- Closure of the pro-`C` notion under injective continuous homomorphisms. -/
structure IsSubgroupClosedProC (ProC : ProCGroupPredicate) : Prop where
  of_injective :
    ∀ {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      (f : G →* H), Continuous f → Function.Injective f →
        ProC (G := H) → ProC (G := G)

/-- Closure under extensions with abelian kernel . -/
structure IsClosedUnderExtensionsWithAbelianKernel (ProC : ProCGroupPredicate) : Prop where
  of_extension :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (A : Subgroup G), [A.Normal] → CommGroup ↥A →
        ProC (G := ↥A) → ProC (G := G ⧸ A) → ProC (G := G)

end

end ProCGroups.ProC
