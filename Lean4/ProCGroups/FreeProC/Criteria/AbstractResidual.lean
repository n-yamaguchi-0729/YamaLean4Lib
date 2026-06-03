import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
import ProCGroups.FiniteGroups.StandardClasses

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProC/Criteria/AbstractResidual.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C groups

Develops free pro-C groups on spaces and pointed spaces, their universal properties, finite quotient characterizations, and standard comparison isomorphisms.
-/

namespace ProCGroups.FreeProC

universe u v


/-- A finite group embedding into a finite direct power of `S`.

This definition does not require `S` to be simple; the literature term "finite `S`-group" is the
special case where `S` is the distinguished finite simple group. -/
def EmbedsInFinitePower
    (S : Type u) [Group S]
    (G : Type u) [Group G] : Prop :=
  Finite G ∧ ∃ ι : Type u, Finite ι ∧ ∃ f : G →* (ι → S), Function.Injective f

/-- A finite-group class contains all finite `S`-groups. -/
def ContainsAllFiniteSGroups
    (C : ProCGroups.FiniteGroupClass.{u})
    (S : Type u) [Group S] : Prop :=
  ∀ {G : Type u} [Group G], EmbedsInFinitePower S G → C G

/-- An abstract group has generator rank at most `κ` if it is a quotient of a free group on a set
of cardinality at most `κ`. -/
def HasGeneratorRankAtMost
    (G : Type u) [Group G] (κ : Cardinal) : Prop :=
  ∃ X : Type u, Cardinal.mk X ≤ κ ∧ ∃ φ : FreeGroup X →* G, Function.Surjective φ

/-- Residual `C`-ness for an abstract group, stated directly in terms of separating nontrivial
elements by finite `C`-quotients. -/
def IsResiduallyFiniteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (G : Type u) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 →
    ∃ Q : Type u, ∃ _ : Group Q, C Q ∧ ∃ φ : G →* Q, φ g ≠ 1

/-- Residual separation when the only allowed finite targets are finite `S`-groups. -/
def IsResiduallyFiniteSGroups
    (S : Type u) [Group S]
    (G : Type u) [Group G] : Prop :=
  ∀ g : G, g ≠ 1 →
    ∃ Q : Type u, ∃ _ : Group Q, EmbedsInFinitePower S Q ∧ ∃ φ : G →* Q, φ g ≠ 1

/-- Finite direct powers of `S` embed into a finite direct power of `S`. -/
theorem embedsInFinitePower_pi
    (S : Type u) [Group S] [Finite S]
    (ι : Type u) [Finite ι] :
    EmbedsInFinitePower S (ι → S) := by
  refine ⟨inferInstance, ι, inferInstance, MonoidHom.id (ι → S), ?_⟩
  exact fun _ _ h => h

/-- A finite group embeds into the rank-one direct power of itself. -/
theorem embedsInFinitePower_self
    (S : Type u) [Group S] [Finite S] :
    EmbedsInFinitePower S S := by
  let f : S →* (PUnit.{u + 1} → S) :=
    { toFun := fun s _ => s
      map_one' := by
        funext _
        rfl
      map_mul' := by
        intro _ _
        funext _
        rfl }
  refine ⟨inferInstance, PUnit.{u + 1}, inferInstance, f, ?_⟩
  intro a b h
  exact congrFun h PUnit.unit

/-- A finite group that injects into a finite `S`-group is a finite `S`-group. -/
theorem EmbedsInFinitePower.of_injective
    {S : Type u} [Group S] {G H : Type u} [Group G] [Group H]
    [Finite G] (hH : EmbedsInFinitePower S H) (f : G →* H)
    (hf : Function.Injective f) :
    EmbedsInFinitePower S G := by
  rcases hH with ⟨_, ι, hι, e, he⟩
  exact ⟨inferInstance, ι, hι, e.comp f, he.comp hf⟩

/-- Subgroups of finite `S`-groups are finite `S`-groups. -/
theorem EmbedsInFinitePower.subgroup
    {S : Type u} [Group S] {G : Type u} [Group G]
    (hG : EmbedsInFinitePower S G) (H : Subgroup G) :
    EmbedsInFinitePower S H := by
  rcases hG with ⟨hfinite, ι, hι, f, hf⟩
  haveI : Finite G := hfinite
  haveI : Finite H := Finite.of_injective ((↑) : H → G) Subtype.coe_injective
  exact ⟨inferInstance, ι, hι, f.comp H.subtype, hf.comp Subtype.coe_injective⟩

/-- Binary products of finite `S`-groups are finite `S`-groups. -/
theorem EmbedsInFinitePower.prod
    {S : Type u} [Group S] {G H : Type u} [Group G] [Group H]
    (hG : EmbedsInFinitePower S G) (hH : EmbedsInFinitePower S H) :
    EmbedsInFinitePower S (G × H) := by
  rcases hG with ⟨hfiniteG, ιG, hιG, fG, hfG⟩
  rcases hH with ⟨hfiniteH, ιH, hιH, fH, hfH⟩
  haveI : Finite G := hfiniteG
  haveI : Finite H := hfiniteH
  haveI : Finite ιG := hιG
  haveI : Finite ιH := hιH
  let f : G × H →* (Sum ιG ιH → S) :=
    { toFun := fun gh i =>
        match i with
        | Sum.inl iG => fG gh.1 iG
        | Sum.inr iH => fH gh.2 iH
      map_one' := by
        funext i
        cases i
        · simp only [Prod.fst_one, map_one, Pi.one_apply]
        · simp only [Prod.snd_one, map_one, Pi.one_apply]
      map_mul' := by
        intro a b
        funext i
        cases i
        · simp only [Prod.fst_mul, map_mul, Pi.mul_apply]
        · simp only [Prod.snd_mul, map_mul, Pi.mul_apply] }
  refine ⟨inferInstance, Sum ιG ιH, inferInstance, f, ?_⟩
  intro a b hab
  apply Prod.ext
  · apply hfG
    funext i
    exact congrFun hab (Sum.inl i)
  · apply hfH
    funext i
    exact congrFun hab (Sum.inr i)

/-- Every finite `S`-group is killed by the exponent of `S`. -/
theorem EmbedsInFinitePower.pow_exponent_eq_one
    {S : Type u} [Group S] {G : Type u} [Group G]
    (hG : EmbedsInFinitePower S G) (g : G) :
    g ^ Monoid.exponent S = 1 := by
  rcases hG with ⟨_, ι, _, f, hf⟩
  apply hf
  funext i
  rw [map_pow, map_one]
  exact Monoid.pow_exponent_eq_one (f g i)

/-- Homomorphisms into finite `S`-groups kill every `S`-exponent power. -/
theorem EmbedsInFinitePower.map_pow_exponent_eq_one
    {S : Type u} [Group S] {G Q : Type u} [Group G] [Group Q]
    (hQ : EmbedsInFinitePower S Q) (φ : G →* Q) (g : G) :
    φ (g ^ Monoid.exponent S) = 1 := by
  rw [map_pow]
  exact hQ.pow_exponent_eq_one (φ g)

/-- If some `S`-exponent power is nontrivial, finite `S`-groups cannot separate all nontrivial
elements. -/
theorem not_isResiduallyFiniteSGroups_of_pow_exponent_ne_one
    {S : Type u} [Group S] {G : Type u} [Group G] {g : G}
    (hg : g ^ Monoid.exponent S ≠ 1) :
    ¬ IsResiduallyFiniteSGroups S G := by
  intro hres
  rcases hres (g ^ Monoid.exponent S) hg with ⟨Q, hQGroup, hQ, φ, hφ⟩
  letI : Group Q := hQGroup
  exact hφ (hQ.map_pow_exponent_eq_one φ g)

/-- A nonzero power of a free generator is nontrivial. -/
theorem freeGroup_of_pow_ne_one
    {X : Type u} (x : X) {n : ℕ} (hn : n ≠ 0) :
    (FreeGroup.of x : FreeGroup X) ^ n ≠ 1 := by
  intro hpow
  have hx : (FreeGroup.of x : FreeGroup X) = 1 :=
    (pow_eq_one_iff_left (M := FreeGroup X) hn).mp hpow
  exact FreeGroup.of_ne_one x hx

/-- Finite `S`-groups alone cannot make a nonempty free group residually `S`. -/
theorem not_isResiduallyFiniteSGroups_freeGroup_of_nonempty
    (S : Type u) [Group S] [Finite S] {X : Type u} (x : X) :
    ¬ IsResiduallyFiniteSGroups S (FreeGroup X) :=
  not_isResiduallyFiniteSGroups_of_pow_exponent_ne_one
    (S := S) (G := FreeGroup X) (g := FreeGroup.of x)
    (freeGroup_of_pow_ne_one x (Monoid.exponent_ne_zero_of_finite (G := S)))

/-- A class containing all finite `S`-groups contains every finite direct power of `S`. -/
theorem ContainsAllFiniteSGroups.pi_mem
    {C : ProCGroups.FiniteGroupClass.{u}} {S : Type u} [Group S] [Finite S]
    (hcontains : ContainsAllFiniteSGroups C S)
    (ι : Type u) [Finite ι] :
    C (ι → S) :=
  hcontains (embedsInFinitePower_pi S ι)

/-- A class containing all finite `S`-groups contains `S` itself. -/
theorem ContainsAllFiniteSGroups.self_mem
    {C : ProCGroups.FiniteGroupClass.{u}} {S : Type u} [Group S] [Finite S]
    (hcontains : ContainsAllFiniteSGroups C S) :
    C S :=
  hcontains (embedsInFinitePower_self S)

end ProCGroups.FreeProC
