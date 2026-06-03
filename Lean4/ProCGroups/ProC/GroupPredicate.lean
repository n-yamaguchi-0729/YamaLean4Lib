import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/GroupPredicate.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Abstract pro-C predicates

`ProCGroupPredicate` is the low-level wrapper for an abstract topological pro-`C` condition.
For concrete finite quotient classes, the public entry point is
`ProCGroups.ProC.IsProCGroup C G`; use this wrapper only when a theorem must quantify over an
abstract predicate before its controlling finite quotient class has been fixed.
-/

namespace ProCGroups.ProC

universe u

/-- A predicate packaging the statement that a topological group belongs to a chosen pro-`C`
class. -/
structure ProCGroupPredicate where
  holds : {G : Type u} → [Group G] → [TopologicalSpace G] → [IsTopologicalGroup G] → Prop

namespace ProCGroupPredicate

/-- A pro-`C` group predicate coerces to its underlying predicate on topological groups. -/
instance instCoeFunProCGroupPredicate : CoeFun ProCGroupPredicate
    (fun _ => {G : Type u} → [Group G] → [TopologicalSpace G] → [IsTopologicalGroup G] → Prop) where
  coe P := @P.holds

end ProCGroupPredicate

end ProCGroups.ProC
