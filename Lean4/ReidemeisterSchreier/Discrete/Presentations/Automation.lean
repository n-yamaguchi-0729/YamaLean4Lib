/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/Presentations/Automation.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Small proof automation for relator calculations

This file provides lightweight tactics that sit on top of the normal-closure
and `RelatorEquivalent` API.  They intentionally do not contain
downstream-specific rewriting rules.

The basic `relator_equivalent` tactic handles routine goals from hypotheses,
reflexivity, relator-set membership, normal-closure membership, quotient
equality, products, inverses, powers, conjugates, and two-sided contexts.

The `relator_equivalent!` variant additionally uses `simp_all`, so it may
strongly simplify the local context.  If either tactic fails, state the missing
intermediate relator-equivalence lemma explicitly, make relator-family
membership visible, or convert a quotient equality back through
`relatorEquivalent_iff_eq_in_presentedQuotient`.
-/

namespace ReidemeisterSchreier.Discrete.Presentations

/-- Try the standard reusable steps in a relator calculation:

* use an existing hypothesis;
* close reflexive `RelatorEquivalent` goals;
* turn membership in the relator set or its normal closure into
  `RelatorEquivalent _ _ 1`;
* recursively split products, inverses, powers, contexts, and conjugates;
* simplify the definition of `RelatorEquivalent`;
* move to quotient equality and simplify.

This is deliberately general.  It is meant to clear routine endpoints in
longer application proofs, not to encode downstream-specific rewrite rules.
-/
macro "relator_equivalent" : tactic =>
  `(tactic|
    repeat first
    | assumption
    | exact RelatorEquivalent.refl _ _
    | apply RelatorEquivalent.of_mem; assumption
    | apply RelatorEquivalent.of_mem_normalClosure; assumption
    | apply RelatorEquivalent.mul
    | apply RelatorEquivalent.mul_eq_one
    | apply RelatorEquivalent.inv
    | apply RelatorEquivalent.inv_eq_one
    | apply RelatorEquivalent.pow
    | apply RelatorEquivalent.pow_eq_one
    | apply RelatorEquivalent.zpow
    | apply RelatorEquivalent.zpow_eq_one
    | apply RelatorEquivalent.context
    | apply RelatorEquivalent.conj
    | apply RelatorEquivalent.conj_eq_one
    | simp only [RelatorEquivalent]
    | rw [relatorEquivalent_iff_eq_in_presentedQuotient]; simp only)

/-- A more aggressive variant of `relator_equivalent`.

This tactic uses `simp_all`, so it strongly simplifies the local context as well
as the target. -/
macro "relator_equivalent!" : tactic =>
  `(tactic|
    first
    | relator_equivalent
    | simp_all only [RelatorEquivalent]
    | rw [relatorEquivalent_iff_eq_in_presentedQuotient]; simp_all only)

end ReidemeisterSchreier.Discrete.Presentations
