import ProCGroups.InverseSystems.CompatibilityAndSurjectivity
import ProCGroups.Topologies.QuotientMaps

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/InverseSystems/Quotients.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Inverse systems and inverse limits

Defines inverse systems of topological groups and proves lift, projection, exactness, quotient, stagewise isomorphism, and finite-stage factorization results.
-/

open scoped Topology

namespace ProCGroups
namespace InverseSystems

universe u v

namespace InverseSystem

variable {I : Type u} [Preorder I]
variable (S : InverseSystem.{u, v} (I := I))
variable [∀ i, Group (S.X i)] [IsGroupSystem S]
variable [∀ i, IsTopologicalGroup (S.X i)]

/-- The transition map of a group-valued inverse system, bundled as a homomorphism. -/
def transitionHom {i j : I} (hij : i ≤ j) : S.X j →* S.X i where
  toFun := S.map hij
  map_one' := IsGroupSystem.map_one (S := S) hij
  map_mul' := IsGroupSystem.map_mul (S := S) hij

omit [∀ i, IsTopologicalGroup (S.X i)] in
@[simp] theorem transitionHom_apply {i j : I} (hij : i ≤ j) (x : S.X j) :
    S.transitionHom hij x = S.map hij x := rfl

omit [∀ i, IsTopologicalGroup (S.X i)] in
/-- The bundled transition homomorphism is continuous. -/
theorem continuous_transitionHom {i j : I} (hij : i ≤ j) :
    Continuous (S.transitionHom hij) :=
  S.continuous_map hij

/-- Closed normal subgroups of the stages, compatible with transition maps. -/
structure CompatibleClosedNormalSubgroups where
  N : ∀ i, Subgroup (S.X i)
  normal : ∀ i, (N i).Normal
  closed : ∀ i, IsClosed ((N i : Subgroup (S.X i)) : Set (S.X i))
  map_le :
    ∀ {i j : I} (hij : i ≤ j), N j ≤ (N i).comap (S.transitionHom hij)

namespace CompatibleClosedNormalSubgroups

variable {S}
variable (Q : S.CompatibleClosedNormalSubgroups)

instance instNormalN (i : I) : (Q.N i).Normal := Q.normal i

/-- The transition map induced on stage quotients. -/
def quotientMap {i j : I} (hij : i ≤ j) :
    S.X j ⧸ Q.N j →* S.X i ⧸ Q.N i :=
  QuotientGroup.map (N := Q.N j) (M := Q.N i) (f := S.transitionHom hij) (Q.map_le hij)

omit [∀ i, IsTopologicalGroup (S.X i)] in
@[simp] theorem quotientMap_mk {i j : I} (hij : i ≤ j) (x : S.X j) :
    Q.quotientMap hij (QuotientGroup.mk' (Q.N j) x) =
      QuotientGroup.mk' (Q.N i) (S.map hij x) := by
  exact QuotientGroup.map_mk' (N := Q.N j) (M := Q.N i)
    (f := S.transitionHom hij) (Q.map_le hij) x

omit [∀ i, IsTopologicalGroup (S.X i)] in
/-- The induced map on stage quotients is continuous. -/
theorem continuous_quotientMap {i j : I} (hij : i ≤ j) :
    Continuous (Q.quotientMap hij) := by
  refine (QuotientGroup.isQuotientMap_mk (N := Q.N j)).continuous_iff.2 ?_
  change Continuous fun x : S.X j => QuotientGroup.mk' (Q.N i) (S.map hij x)
  exact QuotientGroup.continuous_mk.comp (S.continuous_map hij)

/-- The inverse system obtained by quotienting each stage by a compatible closed normal subgroup. -/
def quotientInverseSystem : InverseSystem (I := I) where
  X := fun i => S.X i ⧸ Q.N i
  topologicalSpace := fun i => inferInstance
  map := fun {_i _j} hij => Q.quotientMap hij
  continuous_map := fun {_i _j} hij => Q.continuous_quotientMap hij
  map_id := by
    intro i
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change QuotientGroup.mk' (Q.N i) (S.map (le_rfl : i ≤ i) a) =
      QuotientGroup.mk' (Q.N i) a
    exact congrArg (QuotientGroup.mk' (Q.N i)) (S.map_id_apply i a)
  map_comp := by
    intro i j k hij hjk
    funext x
    refine Quotient.inductionOn' x ?_
    intro a
    change QuotientGroup.mk' (Q.N i) (S.map hij (S.map hjk a)) =
      QuotientGroup.mk' (Q.N i) (S.map (hij.trans hjk) a)
    exact congrArg (QuotientGroup.mk' (Q.N i)) (S.map_comp_apply hij hjk a)

instance quotientInverseSystem_stageGroup (i : I) :
    Group (Q.quotientInverseSystem.X i) := by
  change Group (S.X i ⧸ Q.N i)
  infer_instance

instance quotientInverseSystem_stageTopologicalGroup (i : I) :
    IsTopologicalGroup (Q.quotientInverseSystem.X i) := by
  change IsTopologicalGroup (S.X i ⧸ Q.N i)
  infer_instance

/-- The quotient inverse system is group-valued. -/
instance quotientInverseSystem_isGroupSystem :
    IsGroupSystem Q.quotientInverseSystem where
  map_one := by
    intro i j hij
    exact (Q.quotientMap hij).map_one
  map_mul := by
    intro i j hij x y
    exact (Q.quotientMap hij).map_mul x y
  map_inv := by
    intro i j hij x
    exact (Q.quotientMap hij).map_inv x

/-- The stagewise quotient maps form a morphism from the original system to the quotient system. -/
def toQuotientInverseSystem : S.Morphism Q.quotientInverseSystem where
  map := fun i => QuotientGroup.mk' (Q.N i)
  continuous_map := fun _ => QuotientGroup.continuous_mk
  comm := by
    intro i j hij
    funext x
    exact (Q.quotientMap_mk hij x).symm

/-- Kernel of the map from the inverse limit to the inverse limit of stage quotients. -/
def inverseLimitKernel : Subgroup S.inverseLimit :=
  ⨅ i, (Q.N i).comap (projectionHom (S := S) i)

instance inverseLimitKernel_normal : Q.inverseLimitKernel.Normal where
  conj_mem x hx g := by
    rw [inverseLimitKernel] at hx ⊢
    simp only [projectionHom, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.coe_mk, OneHom.coe_mk,
  projection_apply] at hx ⊢
    intro i
    simpa using (Q.normal i).conj_mem (S.projection i x) (hx i) (S.projection i g)

omit [∀ i, IsTopologicalGroup (S.X i)] in
theorem mem_inverseLimitKernel_iff (x : S.inverseLimit) :
    x ∈ Q.inverseLimitKernel ↔ ∀ i, S.projection i x ∈ Q.N i := by
  simp only [inverseLimitKernel, projectionHom, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.coe_mk,
  OneHom.coe_mk, projection_apply]

/-- The canonical comparison from the quotient of the inverse limit to the inverse limit of the
stage quotients. -/
noncomputable def quotientInverseLimitComparison :
    S.inverseLimit ⧸ Q.inverseLimitKernel →ₜ* Q.quotientInverseSystem.inverseLimit := by
  let T : InverseSystem (I := I) := Q.quotientInverseSystem
  let φ : S.inverseLimit →ₜ* T.inverseLimit :=
    { toMonoidHom :=
        { toFun := S.limMap Q.toQuotientInverseSystem
          map_one' := by
            apply T.ext
            intro i
            calc
              T.projection i (S.limMap Q.toQuotientInverseSystem 1) =
                  Q.toQuotientInverseSystem.map i (S.projection i (1 : S.inverseLimit)) := by
                exact S.π_limMap_apply Q.toQuotientInverseSystem i 1
              _ = 1 := by
                change QuotientGroup.mk' (Q.N i) (S.projection i (1 : S.inverseLimit)) = 1
                rw [projection_one (S := S) i]
                simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_one]
          map_mul' := by
            intro x y
            apply T.ext
            intro i
            calc
              T.projection i (S.limMap Q.toQuotientInverseSystem (x * y)) =
                  Q.toQuotientInverseSystem.map i (S.projection i (x * y)) := by
                exact S.π_limMap_apply Q.toQuotientInverseSystem i (x * y)
              _ =
                  Q.toQuotientInverseSystem.map i (S.projection i x) *
                    Q.toQuotientInverseSystem.map i (S.projection i y) := by
                change QuotientGroup.mk' (Q.N i) (S.projection i (x * y)) =
                  QuotientGroup.mk' (Q.N i) (S.projection i x) *
                    QuotientGroup.mk' (Q.N i) (S.projection i y)
                rw [projection_mul (S := S) i x y]
                simp only [projection_apply, QuotientGroup.mk'_apply, QuotientGroup.mk_mul]
              _ =
                  T.projection i (S.limMap Q.toQuotientInverseSystem x) *
                    T.projection i (S.limMap Q.toQuotientInverseSystem y) := by
                rw [← S.π_limMap_apply Q.toQuotientInverseSystem i x,
                  ← S.π_limMap_apply Q.toQuotientInverseSystem i y] }
      continuous_toFun := S.continuous_limMap Q.toQuotientInverseSystem }
  refine QuotientGroup.liftₜ Q.inverseLimitKernel φ ?_
  intro x hx
  apply T.ext
  intro i
  have hxi : S.projection i x ∈ Q.N i := (Q.mem_inverseLimitKernel_iff x).1 hx i
  change QuotientGroup.mk' (Q.N i) (S.projection i x) = 1
  exact (QuotientGroup.eq_one_iff (N := Q.N i) (S.projection i x)).2 hxi

omit [∀ i, IsTopologicalGroup (S.X i)] in
@[simp] theorem quotientInverseLimitComparison_mk (x : S.inverseLimit) :
    Q.quotientInverseLimitComparison (QuotientGroup.mk' Q.inverseLimitKernel x) =
      S.limMap Q.toQuotientInverseSystem x :=
  by
    unfold quotientInverseLimitComparison
    rfl

omit [∀ i, IsTopologicalGroup (S.X i)] in
@[simp] theorem projection_quotientInverseLimitComparison_mk
    (i : I) (x : S.inverseLimit) :
    Q.quotientInverseSystem.projection i
        (Q.quotientInverseLimitComparison (QuotientGroup.mk' Q.inverseLimitKernel x)) =
      QuotientGroup.mk' (Q.N i) (S.projection i x) := by
  rw [quotientInverseLimitComparison_mk]
  rfl

omit [∀ i, IsTopologicalGroup (S.X i)] in
/-- The comparison map has trivial kernel. -/
theorem ker_quotientInverseLimitComparison :
    Q.quotientInverseLimitComparison.toMonoidHom.ker = ⊥ := by
  ext a
  constructor
  · intro ha
    refine Quotient.inductionOn' a ?_ ha
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff (N := Q.inverseLimitKernel) x).2 <| by
      rw [Q.mem_inverseLimitKernel_iff]
      intro i
      have hcoord :=
        congrArg (fun y => Q.quotientInverseSystem.projection i y) hx
      change QuotientGroup.mk' (Q.N i) (S.projection i x) = 1 at hcoord
      exact (QuotientGroup.eq_one_iff (N := Q.N i) (S.projection i x)).1 hcoord
  · intro ha
    rw [Subgroup.mem_bot] at ha
    rw [MonoidHom.mem_ker, ha]
    exact map_one Q.quotientInverseLimitComparison

omit [∀ i, IsTopologicalGroup (S.X i)] in
/-- The comparison map is injective: its kernel is exactly the subgroup used in the quotient. -/
theorem injective_quotientInverseLimitComparison :
    Function.Injective Q.quotientInverseLimitComparison :=
  (MonoidHom.ker_eq_bot_iff (f := Q.quotientInverseLimitComparison.toMonoidHom)).mp
    Q.ker_quotientInverseLimitComparison

/-- The comparison map is surjective for compact Hausdorff systems over a directed index. -/
theorem surjective_quotientInverseLimitComparison
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    Function.Surjective Q.quotientInverseLimitComparison := by
  let T : InverseSystem (I := I) := Q.quotientInverseSystem
  letI : ∀ i, T2Space (T.X i) := fun i => by
    dsimp [T, quotientInverseSystem]
    haveI : IsClosed ((Q.N i : Subgroup (S.X i)) : Set (S.X i)) := Q.closed i
    infer_instance
  have hlimsurj : Function.Surjective (S.limMap Q.toQuotientInverseSystem) :=
    S.surjective_limMap (T := T) hdir Q.toQuotientInverseSystem
      (fun i => QuotientGroup.mk'_surjective (Q.N i))
  intro y
  rcases hlimsurj y with ⟨x, hx⟩
  refine ⟨QuotientGroup.mk' Q.inverseLimitKernel x, ?_⟩
  simpa [quotientInverseLimitComparison_mk] using hx

/-- The comparison map is bijective for compact Hausdorff systems over a directed index. -/
theorem bijective_quotientInverseLimitComparison
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    Function.Bijective Q.quotientInverseLimitComparison :=
  ⟨Q.injective_quotientInverseLimitComparison,
    Q.surjective_quotientInverseLimitComparison hdir⟩

/-- The quotient of an inverse limit by a compatible closed normal family is the inverse limit of
the stage quotients. -/
noncomputable def quotientInverseLimitContinuousMulEquiv
    [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]
    (hdir : Directed (· ≤ ·) (id : I → I)) :
    S.inverseLimit ⧸ Q.inverseLimitKernel ≃ₜ* Q.quotientInverseSystem.inverseLimit := by
  let T : InverseSystem (I := I) := Q.quotientInverseSystem
  let f := Q.quotientInverseLimitComparison
  letI : CompactSpace S.inverseLimit := inferInstance
  letI : CompactSpace (S.inverseLimit ⧸ Q.inverseLimitKernel) := inferInstance
  letI : ∀ i, T2Space (T.X i) := fun i => by
    dsimp [T, quotientInverseSystem]
    haveI : IsClosed ((Q.N i : Subgroup (S.X i)) : Set (S.X i)) := Q.closed i
    infer_instance
  letI : T2Space T.inverseLimit := T.t2Space_inverseLimit
  exact ContinuousMulEquiv.ofBijectiveCompactToT2
    f.toMonoidHom f.continuous_toFun (Q.bijective_quotientInverseLimitComparison hdir)

end CompatibleClosedNormalSubgroups

end InverseSystem

end InverseSystems
end ProCGroups
