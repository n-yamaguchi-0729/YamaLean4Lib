import ProCGroups.InverseSystems.Basic
import ProCGroups.InverseSystems.Utilities

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/InverseSystems/CompatibilityAndSurjectivity.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Inverse systems and inverse limits

Defines inverse systems of topological groups and proves lift, projection, exactness, quotient, stagewise isomorphism, and finite-stage factorization results.
-/

open Set
open scoped Topology

namespace ProCGroups.InverseSystems

universe u v w

section

variable {I : Type u} [Preorder I]

attribute [instance] InverseSystem.topologicalSpace

namespace InverseSystem

variable (S : InverseSystem (I := I))

/-- Compatibility restricted to indices below a fixed stage. This is only used to prove
nonemptiness of the inverse limit. -/
private def CompatibleUpTo (j : I) (x : ∀ i, S.X i) : Prop :=
  ∀ k, ∀ hkj : k ≤ j, S.map hkj (x j) = x k

private theorem isClosed_setOf_compatibleUpTo [∀ i, T2Space (S.X i)] (j : I) :
    IsClosed {x : ∀ i, S.X i | S.CompatibleUpTo j x} := by
  simp only [CompatibleUpTo, setOf_forall]
  refine isClosed_iInter fun k => isClosed_iInter fun hkj => ?_
  exact isClosed_eq ((S.continuous_map hkj).comp (continuous_apply j)) (continuous_apply k)

private theorem compatibleUpTo_nonempty (j : I) [∀ i, Nonempty (S.X i)] :
    ({x : ∀ i, S.X i | S.CompatibleUpTo j x} : Set (∀ i, S.X i)).Nonempty := by
  classical
  let xj : S.X j := Classical.choice (inferInstance : Nonempty (S.X j))
  let x : ∀ i, S.X i := fun i =>
    if hij : i ≤ j then S.map hij xj else Classical.choice (inferInstance : Nonempty (S.X i))
  refine ⟨x, ?_⟩
  intro k hkj
  simp only [le_refl, ↓reduceDIte, map_id_apply, hkj, x]

private theorem compatibleUpTo_mono {j j' : I} (hjj' : j ≤ j') :
    {x : ∀ i, S.X i | S.CompatibleUpTo j' x} ⊆ {x : ∀ i, S.X i | S.CompatibleUpTo j x} := by
  intro x hx k hkj
  calc
    S.map hkj (x j) = S.map hkj (S.map hjj' (x j')) := by rw [hx j hjj']
    _ = S.map (hkj.trans hjj') (x j') := by rw [S.map_comp_apply hkj hjj']
    _ = x k := hx k (hkj.trans hjj')

/-- The inverse limit of nonempty compact Hausdorff spaces is nonempty. -/
theorem nonempty_inverseLimit [∀ i, Nonempty (S.X i)] [∀ i, CompactSpace (S.X i)]
    [∀ i, T2Space (S.X i)] (hdir : Directed (· ≤ ·) (id : I → I)) :
    Nonempty S.inverseLimit := by
  classical
  let Y : I → Set (∀ i, S.X i) := fun j => {x | S.CompatibleUpTo j x}
  have hclosed : ∀ j, IsClosed (Y j) := fun j => S.isClosed_setOf_compatibleUpTo j
  have hfinite : ∀ s : Finset I, (⋂ i ∈ s, Y i).Nonempty := by
    intro s
    by_cases hs : s.Nonempty
    · rcases exists_upperBound_finset (I := I) hdir s hs with ⟨j, hj⟩
      rcases S.compatibleUpTo_nonempty j with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simp only [Y, mem_iInter]
      intro i hi
      exact S.compatibleUpTo_mono (hj i hi) hx
    · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst hs'
      refine ⟨fun i => Classical.choice (inferInstance : Nonempty (S.X i)), ?_⟩
      simp only [Finset.notMem_empty, iInter_of_empty, iInter_univ, mem_univ]
  rcases CompactSpace.iInter_nonempty hclosed hfinite with ⟨x, hx⟩
  refine ⟨⟨x, ?_⟩⟩
  intro i j hij
  exact (mem_iInter.mp hx j) i hij

/-- Special case for inverse systems of nonempty finite discrete spaces. -/
theorem nonempty_inverseLimit_of_finite [∀ i, Finite (S.X i)] [∀ i, Nonempty (S.X i)]
    [∀ i, DiscreteTopology (S.X i)] (hdir : Directed (· ≤ ·) (id : I → I)) :
    Nonempty S.inverseLimit := by
  letI : ∀ i, CompactSpace (S.X i) := fun _ => inferInstance
  letI : ∀ i, T2Space (S.X i) := fun _ => inferInstance
  exact S.nonempty_inverseLimit hdir

/-- A morphism of inverse systems over the same directed preorder. -/
structure Morphism (T : InverseSystem (I := I)) where
  map : ∀ i, S.X i → T.X i
  continuous_map : ∀ i, Continuous (map i)
  comm : ∀ {i j : I} (hij : i ≤ j), T.map hij ∘ map j = map i ∘ S.map hij

namespace Morphism

variable {S}
variable {T U : InverseSystem (I := I)}

/-- A morphism of inverse systems commutes with transition maps pointwise. -/
@[simp] theorem comm_apply (Θ : S.Morphism T) {i j : I} (hij : i ≤ j) (x : S.X j) :
    T.map hij (Θ.map j x) = Θ.map i (S.map hij x) := by
  simpa [Function.comp] using congrFun (Θ.comm hij) x

/-- The identity morphism of an inverse system. -/
def id (S : InverseSystem (I := I)) : S.Morphism S where
  map := fun _ => fun x => x
  continuous_map := fun _ => continuous_id
  comm := fun _ => by
    funext x
    rfl

/-- The identity morphism of an inverse system acts as the identity at each stage. -/
@[simp] theorem id_apply (i : I) (x : S.X i) :
    (id S).map i x = x := rfl

/-- Composition of morphisms of inverse systems. -/
def comp (Φ : T.Morphism U) (Θ : S.Morphism T) : S.Morphism U where
  map := fun i => Φ.map i ∘ Θ.map i
  continuous_map := fun i => (Φ.continuous_map i).comp (Θ.continuous_map i)
  comm := fun {i j} hij => by
    funext x
    calc
      U.map hij ((Φ.map j ∘ Θ.map j) x) = U.map hij (Φ.map j (Θ.map j x)) := rfl
      _ = Φ.map i (T.map hij (Θ.map j x)) := by
        exact congrFun (Φ.comm hij) (Θ.map j x)
      _ = Φ.map i (Θ.map i (S.map hij x)) := by
        rw [Θ.comm_apply hij x]
      _ = ((Φ.map i ∘ Θ.map i) ∘ S.map hij) x := by
        rfl

/-- Composition of morphisms of inverse systems is computed stagewise. -/
@[simp] theorem comp_apply (Φ : T.Morphism U) (Θ : S.Morphism T) (i : I) (x : S.X i) :
    (comp Φ Θ).map i x = Φ.map i (Θ.map i x) := rfl

end Morphism

/-- A morphism of inverse systems sends inverse-limit projections to a compatible family. -/
theorem compatibleMaps_morphism {T : InverseSystem (I := I)} (Θ : S.Morphism T) :
    T.CompatibleMaps (fun i => Θ.map i ∘ S.projection i) := by
  intro i j hij
  funext x
  calc
    T.map hij (Θ.map j (S.projection j x)) = Θ.map i (S.map hij (S.projection j x)) := by
      exact Θ.comm_apply hij (S.projection j x)
    _ = Θ.map i (S.projection i x) := by rw [S.projection_compatible x i j hij]

/-- The induced map on inverse limits of a morphism of inverse systems. -/
def limMap {T : InverseSystem (I := I)} (Θ : S.Morphism T) :
    S.inverseLimit → T.inverseLimit :=
  T.inverseLimitLift (fun i => Θ.map i ∘ S.projection i) (S.compatibleMaps_morphism Θ)

/-- A projection after the induced map on inverse limits is the corresponding stage map after projection. -/
@[simp] theorem π_comp_limMap {T : InverseSystem (I := I)} (Θ : S.Morphism T) (i : I) :
    T.projection i ∘ S.limMap Θ = Θ.map i ∘ S.projection i := by
  simp only [limMap, projection_comp_inverseLimitLift]

/-- Pointwise form of the projection formula for the induced map on inverse limits. -/
@[simp] theorem π_limMap_apply {T : InverseSystem (I := I)} (Θ : S.Morphism T)
    (i : I) (x : S.inverseLimit) :
    T.projection i (S.limMap Θ x) = Θ.map i (S.projection i x) := by
  simpa [Function.comp] using congrFun (S.π_comp_limMap (Θ := Θ) i) x

/-- The map induced on inverse limits by a morphism of inverse systems is continuous. -/
theorem continuous_limMap {T : InverseSystem (I := I)} (Θ : S.Morphism T) :
    Continuous (S.limMap Θ) := by
  refine T.continuous_inverseLimitLift (fun i => Θ.map i ∘ S.projection i) ?_ (S.compatibleMaps_morphism Θ)
  intro i
  exact (Θ.continuous_map i).comp (S.continuous_projection i)

/-- The inverse-limit map induced by the identity morphism is the identity. -/
@[simp] theorem limMap_id :
    S.limMap (Morphism.id S) = id := by
  funext x
  apply S.ext
  intro i
  change S.projection i (S.limMap (Morphism.id S) x) = S.projection i x
  rw [S.π_limMap_apply (Θ := Morphism.id S)]
  rfl

/-- The inverse-limit map induced by a composite morphism is the composite of the induced maps. -/
@[simp] theorem limMap_comp {T U : InverseSystem (I := I)} (Φ : T.Morphism U) (Θ : S.Morphism T) :
    S.limMap (Morphism.comp Φ Θ) = T.limMap Φ ∘ S.limMap Θ := by
  funext x
  apply U.ext
  intro i
  change U.projection i (S.limMap (Morphism.comp Φ Θ) x) = U.projection i ((T.limMap Φ ∘ S.limMap Θ) x)
  calc
    U.projection i (S.limMap (Morphism.comp Φ Θ) x) = (Morphism.comp Φ Θ).map i (S.projection i x) := by
      rw [S.π_limMap_apply (Θ := Morphism.comp Φ Θ)]
    _ = Φ.map i (Θ.map i (S.projection i x)) := rfl
    _ = U.projection i ((T.limMap Φ ∘ S.limMap Θ) x) := by
      rw [Function.comp, T.π_limMap_apply (Θ := Φ), S.π_limMap_apply (Θ := Θ)]

/-- The induced map on inverse limits is injective when all stage maps are injective. -/
theorem injective_limMap {T : InverseSystem (I := I)} (Θ : S.Morphism T)
    (hinj : ∀ i, Function.Injective (Θ.map i)) :
    Function.Injective (S.limMap Θ) := by
  intro x y hxy
  apply S.ext
  intro i
  apply hinj i
  simpa using congrArg (T.projection i) hxy

/-- If all components of a morphism of inverse systems are embeddings, then the induced map on
inverse limits is an embedding. -/
theorem embedding_limMap {T : InverseSystem (I := I)} (Θ : S.Morphism T)
    (hemb : ∀ i, Topology.IsEmbedding (Θ.map i)) :
    Topology.IsEmbedding (S.limMap Θ) := by
  let hsubS : Topology.IsEmbedding (Subtype.val : S.inverseLimit → ∀ i, S.X i) :=
    Topology.IsEmbedding.subtypeVal
  let hpi : Topology.IsEmbedding (Pi.map fun i => Θ.map i : (∀ i, S.X i) → ∀ i, T.X i) :=
    Topology.IsEmbedding.piMap fun i => hemb i
  have hcomp :
      Topology.IsEmbedding
        (((Subtype.val : T.inverseLimit → ∀ i, T.X i) ∘ S.limMap Θ) : S.inverseLimit → ∀ i, T.X i) := by
    simpa [Function.comp] using (hpi.comp hsubS)
  exact Topology.IsEmbedding.of_comp (S.continuous_limMap Θ) continuous_subtype_val hcomp

/-- If all components of a morphism of inverse systems are surjective,
then the induced map on inverse limits is surjective. -/
theorem surjective_limMap {T : InverseSystem (I := I)} [∀ i, CompactSpace (S.X i)]
    [∀ i, T2Space (S.X i)] [∀ i, T2Space (T.X i)] (hdir : Directed (· ≤ ·) (id : I → I))
    (Θ : S.Morphism T) (hsurj : ∀ i, Function.Surjective (Θ.map i)) :
    Function.Surjective (S.limMap Θ) := by
  intro xlim
  let F : InverseSystem (I := I) := {
    X := fun i => {x : S.X i // Θ.map i x = T.projection i xlim}
    topologicalSpace := fun _ => inferInstance
    map := fun {i j} hij x =>
      ⟨S.map hij x.1, by
        calc
          Θ.map i (S.map hij x.1) = T.map hij (Θ.map j x.1) := by
            symm
            exact Θ.comm_apply hij x.1
          _ = T.map hij (T.projection j xlim) := by rw [x.2]
          _ = T.projection i xlim := T.projection_compatible xlim i j hij⟩
    continuous_map := fun {i j} hij =>
      Continuous.subtype_mk ((S.continuous_map hij).comp continuous_subtype_val) fun x => by
        calc
          Θ.map i (S.map hij x.1) = T.map hij (Θ.map j x.1) := by
            symm
            exact Θ.comm_apply hij x.1
          _ = T.map hij (T.projection j xlim) := by rw [x.2]
          _ = T.projection i xlim := T.projection_compatible xlim i j hij
    map_id := fun i => by
      funext x
      apply Subtype.ext
      simp only [projection_apply, map_id_apply, id_eq]
    map_comp := fun {i j k} hij hjk => by
      funext x
      apply Subtype.ext
      simp only [projection_apply, Function.comp_apply, S.map_comp_apply hij hjk]}
  letI : ∀ i, Nonempty (F.X i) := fun i => by
    rcases hsurj i (T.projection i xlim) with ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩
  letI : ∀ i, T2Space (F.X i) := fun _ => inferInstance
  letI : ∀ i, CompactSpace (F.X i) := fun i => by
    let hs : IsClosed {x : S.X i | Θ.map i x = T.projection i xlim} :=
      isClosed_eq (Θ.continuous_map i) continuous_const
    simpa [F] using hs.isClosedEmbedding_subtypeVal.compactSpace
  rcases InverseSystem.nonempty_inverseLimit (S := F) hdir with ⟨y⟩
  refine ⟨⟨fun i => (y.1 i).1, ?_⟩, ?_⟩
  · intro i j hij
    exact congrArg Subtype.val (y.2 i j hij)
  · apply T.ext
    intro i
    simpa using (y.1 i).2

/-- Compatible surjections from a compact space induce a surjection
onto the inverse limit. -/
theorem surjective_inverseLimitLift {X : Type w} [TopologicalSpace X] [CompactSpace X]
    [Nonempty I]
    (ψ : ∀ i, X → S.X i) (hψ : ∀ i, Continuous (ψ i)) (hcompat : S.CompatibleMaps ψ)
    (hsurj : ∀ i, Function.Surjective (ψ i)) (hdir : Directed (· ≤ ·) (id : I → I))
    [∀ i, T2Space (S.X i)] :
    Function.Surjective (S.inverseLimitLift ψ hcompat) := by
  intro xlim
  let Z : I → Set X := fun i => {x | ψ i x = S.projection i xlim}
  have hclosed : ∀ i, IsClosed (Z i) := fun i => isClosed_eq (hψ i) continuous_const
  have hfinite : ∀ s : Finset I, (⋂ i ∈ s, Z i).Nonempty := by
    intro s
    by_cases hs : s.Nonempty
    · rcases exists_upperBound_finset (I := I) hdir s hs with ⟨j, hj⟩
      rcases hsurj j (S.projection j xlim) with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      simp only [Z, mem_iInter]
      intro i hi
      have hfac : S.map (hj i hi) (ψ j x) = ψ i x := by
        simpa [Function.comp] using congrFun (hcompat i j (hj i hi)) x
      calc
        ψ i x = S.map (hj i hi) (ψ j x) := hfac.symm
        _ = S.map (hj i hi) (S.projection j xlim) := by rw [hx]
        _ = S.projection i xlim := S.projection_compatible xlim i j (hj i hi)
    · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst hs'
      let j : I := Classical.choice ‹Nonempty I›
      rcases hsurj j (S.projection j xlim) with ⟨x, hx⟩
      exact ⟨x, by simp only [Finset.notMem_empty, iInter_of_empty, iInter_univ, mem_univ]⟩
  rcases CompactSpace.iInter_nonempty hclosed hfinite with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply S.ext
  intro i
  calc
    S.projection i (S.inverseLimitLift ψ hcompat x) = ψ i x := by
      rfl
    _ = S.projection i xlim := mem_iInter.mp hx i

/-- If an inverse limit over a directed index set is finite, one projection separates all points. -/
theorem exists_injective_projection_of_finite_inverseLimit [Nonempty I]
    (hdir : Directed (· ≤ ·) (id : I → I)) [Finite S.inverseLimit] :
    ∃ k, Function.Injective (S.projection k) := by
  classical
  letI : Fintype S.inverseLimit := Fintype.ofFinite S.inverseLimit
  let pairs : Finset (S.inverseLimit × S.inverseLimit) :=
    Finset.univ.filter fun p => p.1 ≠ p.2
  have hseparate :
      ∀ p : S.inverseLimit × S.inverseLimit, p ∈ pairs →
        ∃ i, S.projection i p.1 ≠ S.projection i p.2 := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by
      exact (Finset.mem_filter.mp hp).2
    by_contra h
    apply hpne
    apply S.ext
    intro i
    by_contra hneq
    exact h ⟨i, hneq⟩
  have hfinset :
      ∀ t : Finset (S.inverseLimit × S.inverseLimit),
        (∀ p, p ∈ t → ∃ i, S.projection i p.1 ≠ S.projection i p.2) →
          ∃ k, ∀ p, p ∈ t → S.projection k p.1 ≠ S.projection k p.2 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro _
        exact ⟨Classical.choice ‹Nonempty I›, by simp only [Finset.notMem_empty, projection_apply, ne_eq, IsEmpty.forall_iff, implies_true]⟩
    | insert p t hpt ih =>
        intro ht
        rcases ht p (by simp only [Finset.mem_insert, true_or]) with ⟨j, hj⟩
        have ht_rest : ∀ q, q ∈ t → ∃ i, S.projection i q.1 ≠ S.projection i q.2 := by
          intro q hq
          exact ht q (by simp only [Finset.mem_insert, hq, or_true])
        rcases ih ht_rest with ⟨i, hi⟩
        rcases hdir i j with ⟨k, hik, hjk⟩
        refine ⟨k, ?_⟩
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with rfl | hq
        · intro heq
          apply hj
          calc
            S.projection j q.1 = S.map hjk (S.projection k q.1) := by
              exact (S.projection_compatible q.1 j k hjk).symm
            _ = S.map hjk (S.projection k q.2) := by rw [heq]
            _ = S.projection j q.2 := S.projection_compatible q.2 j k hjk
        · intro heq
          apply hi q hq
          calc
            S.projection i q.1 = S.map hik (S.projection k q.1) := by
              exact (S.projection_compatible q.1 i k hik).symm
            _ = S.map hik (S.projection k q.2) := by rw [heq]
            _ = S.projection i q.2 := S.projection_compatible q.2 i k hik
  rcases hfinset pairs hseparate with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  intro x y hxy
  by_contra hne
  exact hk (x, y) (by simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, hne, not_false_eq_true, and_self, pairs]) hxy

end InverseSystem
end
end ProCGroups.InverseSystems
