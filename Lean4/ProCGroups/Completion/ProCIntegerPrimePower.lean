import ProCGroups.Completion.ProCInteger

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/Completion/ProCIntegerPrimePower.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C integers and finite cyclic stages

Constructs pro-C integers as inverse limits of allowed finite cyclic rings and records coordinate formulas at each finite modulus.
-/

namespace ProCGroups.Completion

noncomputable section

universe u

namespace ProCIntegerIndex

/-- The `p^k` coefficient coordinate for `ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p)`. -/
def pGroupPower (p k : ℕ) [Fact (Nat.Prime p)] :
    ProCIntegerIndex (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}) where
  modulus := p ^ k
  positive := by
    exact Nat.pow_pos (show 0 < p from (Fact.out : Nat.Prime p).pos)
  cyclic_mem := by
    letI : NeZero (p ^ k) := ⟨Nat.ne_of_gt (Nat.pow_pos
      (show 0 < p from (Fact.out : Nat.Prime p).pos))⟩
    letI : Fintype (ZMod (p ^ k)) := ZMod.fintype (p ^ k)
    constructor
    · have hfinZ : Finite (ZMod (p ^ k)) := Finite.of_fintype _
      have hfinMul : Finite (Multiplicative (ZMod (p ^ k))) :=
        @Finite.of_equiv _ _ hfinZ Multiplicative.toAdd
      exact @Finite.of_equiv _ _ hfinMul Equiv.ulift.symm
    · intro g
      refine ⟨k, ?_⟩
      cases g with
      | up g' =>
        apply ULift.ext
        change g' ^ p ^ k = 1
        cases g' with
        | ofAdd z =>
          change Multiplicative.ofAdd ((p ^ k) • z) = Multiplicative.ofAdd 0
          simp only [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, ofAdd_zero]

/-- The prime-power coefficient index has modulus `p ^ n`. -/
@[simp]
theorem modulus_pGroupPower (p k : ℕ) [Fact (Nat.Prime p)] :
    (pGroupPower p k :
      ProCIntegerIndex (FiniteGroupClass.pGroup p : FiniteGroupClass.{u})).modulus = p ^ k :=
  rfl

/-- Any coefficient index for the finite `p`-group class is dominated by a prime-power modulus. -/
theorem modulus_dvd_pow_of_mem_pGroup (p : ℕ)
    (i : ProCIntegerIndex (FiniteGroupClass.pGroup p : FiniteGroupClass.{u})) :
    ∃ k, i.modulus ∣ p ^ k := by
  rcases i.cyclic_mem with ⟨_hfin, hp⟩
  rcases hp (ULift.up (Multiplicative.ofAdd (1 : ZMod i.modulus))) with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  letI : NeZero i.modulus := ⟨Nat.ne_of_gt i.positive⟩
  have hk' : ((p ^ k : ℕ) : ZMod i.modulus) = 0 := by
    have hdown := congrArg ULift.down hk
    change (Multiplicative.ofAdd (1 : ZMod i.modulus)) ^ (p ^ k) = 1 at hdown
    have h := congrArg Multiplicative.toAdd hdown
    simpa using h
  exact (ZMod.natCast_eq_zero_iff (p ^ k) i.modulus).mp hk'

/-- The finite `p`-group coefficient indices for pro-`C` integers are directed. -/
theorem directed_pGroup (p : ℕ) [Fact (Nat.Prime p)] :
    Directed (· ≤ ·)
      (id : ProCIntegerIndex (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}) →
        ProCIntegerIndex (FiniteGroupClass.pGroup p : FiniteGroupClass.{u})) := by
  intro i j
  rcases modulus_dvd_pow_of_mem_pGroup (p := p) i with ⟨ki, hki⟩
  rcases modulus_dvd_pow_of_mem_pGroup (p := p) j with ⟨kj, hkj⟩
  refine ⟨pGroupPower p (ki + kj), ?_, ?_⟩
  · exact dvd_trans hki (pow_dvd_pow p (Nat.le_add_right ki kj))
  · exact dvd_trans hkj (pow_dvd_pow p (Nat.le_add_left kj ki))

end ProCIntegerIndex

/-- The distinguished element `1` projects to `1` on every prime-power coordinate. -/
@[simp]
theorem proCIntegerProj_pGroupPower_one (p k : ℕ) [Fact (Nat.Prime p)] :
    proCIntegerProj
        (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}))
        (ProCIntegerIndex.pGroupPower p k)
        (proCIntegerOne
          (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}))).toAdd =
      (1 : ZMod (p ^ k)) :=
  rfl

/-- The ordinary integers are dense in the pro-`p` integer coefficient ring. -/
theorem denseRange_intToProCInteger_pGroup (p : ℕ) [Fact (Nat.Prime p)] :
    DenseRange (intToProCInteger
      (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}))) := by
  let C : FiniteGroupClass.{u} := FiniteGroupClass.pGroup p
  let S := proCIntegerSystem C
  let φ : ∀ i : ProCIntegerIndex C, ℤ → S.X i := fun i n => (n : ZMod i.modulus)
  have hφ : S.CompatibleMaps φ := by
    intro i j hij
    funext n
    exact map_intCast (ZMod.castHom hij (ZMod i.modulus)) n
  have hsurj : ∀ i, Function.Surjective (φ i) := by
    intro i
    exact ZMod.intCast_surjective
  letI : Nonempty (ProCIntegerIndex C) := ⟨ProCIntegerIndex.pGroupPower p 0⟩
  have hdense : DenseRange (S.inverseLimitLift φ hφ) :=
    ProCGroups.InverseSystems.InverseSystem.denseRange_lift
      (S := S) φ hφ hsurj (ProCIntegerIndex.directed_pGroup (p := p))
  simpa [C, S, φ, proCIntegerSystem, ProCIntegerLimitCarrier, ProCIntegerCompatible, intToProCInteger,
    ProCGroups.InverseSystems.InverseSystem.inverseLimitLift] using hdense

/-- The multiplicative infinite-cyclic map is dense in the pro-`p` integers. -/
theorem denseRange_multiplicativeIntToProCInteger_pGroup (p : ℕ) [Fact (Nat.Prime p)] :
    DenseRange
      (multiplicativeIntToProCInteger
        (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}))) := by
  simpa [multiplicativeIntToProCInteger, intToProCInteger, DenseRange, Function.comp_def] using
    (denseRange_intToProCInteger_pGroup (p := p) :
      DenseRange (intToProCInteger
        (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}))))

/-- The distinguished element `1` topologically generates the pro-`p` integers. -/
theorem topologicallyGenerates_singleton_proCIntegerOne_pGroup
    (p : ℕ) [Fact (Nat.Prime p)] :
    ProCGroups.Generation.TopologicallyGenerates
      (G := Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0})))
      ({proCIntegerOne
        (C := (FiniteGroupClass.pGroup p : FiniteGroupClass.{0}))} : Set _) := by
  let C : FiniteGroupClass.{0} := FiniteGroupClass.pGroup p
  simpa [C, proCIntegerOne] using
    (ProCGroups.Generation.topologicallyGenerates_singleton_of_denseRange_mint
      (f := multiplicativeIntToProCInteger (C := C))
      (denseRange_multiplicativeIntToProCInteger_pGroup (p := p)))

/-- The pro-`p` integers are a pro-`p` group. -/
theorem isProPGroup_multiplicative_proCInteger_pGroup (p : ℕ) [Fact (Nat.Prime p)] :
    ProCGroups.ProC.IsProPGroup p
      (Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0}))) := by
  let C : FiniteGroupClass.{0} := FiniteGroupClass.pGroup p
  letI : Nonempty (ProCIntegerIndex C) := ⟨ProCIntegerIndex.pGroupPower p 0⟩
  simpa [ProCGroups.ProC.IsProPGroup, C] using
    isProCGroup_multiplicative_proCInteger
      (C := C)
      (FiniteGroupClass.pGroup_formation p).isomClosed
      (FiniteGroupClass.pGroup_formation p).quotientClosed
      (ProCIntegerIndex.directed_pGroup (p := p))

/-- The pro-`p` integers are procyclic. -/
theorem isProcyclicGroup_multiplicative_proCInteger_pGroup (p : ℕ) [Fact (Nat.Prime p)] :
    ProCGroups.ProC.IsProcyclicGroup
      (Multiplicative
        (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0}))) := by
  exact ProCGroups.ProC.isProcyclicGroup_of_topologicallyGenerates_singleton
    (G := Multiplicative
      (ProCIntegerLimitCarrier (FiniteGroupClass.pGroup p : FiniteGroupClass.{0})))
    ((isProPGroup_multiplicative_proCInteger_pGroup (p := p)).1)
    (topologicallyGenerates_singleton_proCIntegerOne_pGroup (p := p))

end

end ProCGroups.Completion
