import FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.System.AddCommGroup

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/CoefficientRings/CompletedGroupAlgebraModN/System/CompletionMap.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed coefficient algebras

Coefficient algebras, residue stages, and completed group-algebra maps are kept as the scalar layer for completed Fox calculus.
-/
namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u


variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < n)] in
/-- Compatibility lemma modNCompletedGroupAlgebraStageMap_compatibleMaps. -/
theorem modNCompletedGroupAlgebraStageMap_compatibleMaps :
    (modNCompletedGroupAlgebraSystem n G).CompatibleMaps
      (fun U => modNCompletedGroupAlgebraStageMap n G U) := by
  intro U V hUV
  funext x
  exact congrFun
    (congrArg DFunLike.coe
      (modNCompletedGroupAlgebraStageMap_compatible (n := n) (G := G) (U := U) (V := V) hUV))
    x

/-- The canonical map `(ZMod n)[G] → lim_U (ZMod n)[G/U]`. -/
def toModNCompletedGroupAlgebra :
    ModNCompletedGroupRing n G → ModNCompletedGroupAlgebra n G := by
  letI : TopologicalSpace (ModNCompletedGroupRing n G) := ⊥
  exact
    (modNCompletedGroupAlgebraSystem n G).inverseLimitLift
      (fun U => modNCompletedGroupAlgebraStageMap n G U)
      (modNCompletedGroupAlgebraStageMap_compatibleMaps (n := n) (G := G))

omit [Fact (0 < n)] in
/-- 法 n 係数で定めた 有限段階射影が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
@[simp]
theorem modNCompletedGroupAlgebraProjection_toCompleted
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (x : ModNCompletedGroupRing n G) :
    modNCompletedGroupAlgebraProjection n G U (toModNCompletedGroupAlgebra n G x) =
      modNCompletedGroupAlgebraStageMap n G U x := by
  rfl

end

end FoxDifferential
