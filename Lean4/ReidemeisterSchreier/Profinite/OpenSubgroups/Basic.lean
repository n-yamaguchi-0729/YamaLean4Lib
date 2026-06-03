import ProCGroups.GroupTheory.Subgroups

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ReidemeisterSchreier/Profinite/OpenSubgroups/Basic.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Profinite open-subgroup Schreier theory

Profinite open subgroup quotients, finite permutation targets, dense free models, exact right Schreier generation, and topological rank bounds.
-/

open scoped Topology Pointwise


open ProCGroups
open ProCGroups.GroupTheory

universe u v

/-!
# Profinite open-subgroup basics

This module now only re-exports general rank and subgroup-relation helpers
from `ProCGroups` for RS profinite files. RS-specific open-subgroup theorems
live in the more focused files under this directory.
-/
