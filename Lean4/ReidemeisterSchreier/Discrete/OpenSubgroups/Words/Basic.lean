import ReidemeisterSchreier.FreeGroup.PrefixParent

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Discrete/OpenSubgroups/Words/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free-word compatibility for Schreier theory

Free-group word lemmas, prefix-parent compatibility, Nielsen-Schreier calculations, and cancellation rules for Schreier generators.
-/

namespace ReidemeisterSchreier.Discrete.OpenSubgroups


/-- The initial segments of the reduced word representing an element of a free group. -/
def freeGroupInitialSegments {X : Type u} [DecidableEq X] (t : FreeGroup X) :
    Set (FreeGroup X) := by
  exact
    {u | ∃ n ≤ (FreeGroup.toWord t).length, u = FreeGroup.mk (List.take n (FreeGroup.toWord t))}


end ReidemeisterSchreier.Discrete.OpenSubgroups
