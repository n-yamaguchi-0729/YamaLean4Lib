import FenchelNielsenZomorrodian.Discrete.MainTheorem
import FenchelNielsenZomorrodian.Profinite.CompactFuchsianSignature
import FenchelNielsenZomorrodian.Profinite.Perfectness
import FenchelNielsenZomorrodian.Profinite.SmoothQuotient

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Profinite/DiscreteBridge.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Bridge from discrete compact Fuchsian quotients to profinite quotients

Transfers compact zero-genus three-step finite-index constructions through the profinite presentation to obtain finite smooth profinite quotients.
-/

namespace FenchelNielsen

universe u

open scoped BigOperators

namespace ProfiniteFGroup

theorem mul_swap_eq_one_of_mul_eq_one
    {G : Type*} [Group G] {a b : G} (h : a * b = 1) :
    b * a = 1 := by
  have ha : a = b⁻¹ := by
    calc
      a = a * 1 := by simp only [mul_one]
      _ = a * (b * b⁻¹) := by simp only [mul_one, mul_inv_cancel]
      _ = (a * b) * b⁻¹ := by group
      _ = b⁻¹ := by simp only [h, one_mul]
  simp only [ha, mul_inv_cancel]

/-- The abstract compact Fuchsian presentation maps to a compact profinite `F`-group by sending
the paper generators to the corresponding profinite presentation generators. -/
noncomputable def compactPresentationHomToProfinite
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods) :
    FuchsianPresentedGroup
        (compactFuchsianSignature Δ.signature hCompact hPeriods) →*
      Δ.carrier := by
  let σ := compactFuchsianSignature Δ.signature hCompact hPeriods
  let f : FuchsianGenerator σ → Δ.carrier
    | .elliptic i => Δ.inertia i
    | .surfaceA i => Δ.surfaceA i
    | .surfaceB i => Δ.surfaceB i
  refine PresentedGroup.toGroup (rels := relators σ) (f := f) ?_
  intro r hr
  rcases hr with ⟨i, rfl⟩ | rfl
  · have hpow : Δ.inertia i ^ Δ.signature.periods i = 1 := by
      rw [← Δ.inertia_order i]
      exact pow_orderOf_eq_one (Δ.inertia i)
    simpa [σ, f, xWord, compactFuchsianSignature] using hpow
  · have hCusp :
        ((List.finRange Δ.signature.numCusps).map fun j => Δ.cusp j).prod = 1 := by
      apply List.prod_eq_one
      intro x hx
      rcases List.mem_map.mp hx with ⟨j, _hj, rfl⟩
      exfalso
      rw [hCompact] at j
      exact Nat.not_lt_zero _ j.2
    have hRel :
        ((List.finRange Δ.signature.orbitGenus).map fun i =>
              ⁅Δ.surfaceA i, Δ.surfaceB i⁆).prod *
            ((List.finRange Δ.signature.numPeriods).map fun k => Δ.inertia k).prod =
          1 := by
      simpa [profiniteFenchelTotalRelation, hCusp, mul_assoc] using
        Δ.presentation_relation
    have hRel' :
        ((List.finRange Δ.signature.numPeriods).map fun k => Δ.inertia k).prod *
            ((List.finRange Δ.signature.orbitGenus).map fun i =>
              ⁅Δ.surfaceA i, Δ.surfaceB i⁆).prod =
          1 :=
      mul_swap_eq_one_of_mul_eq_one hRel
    simpa [σ, f, totalRelation, xWord, aWord, bWord, compactFuchsianSignature,
      map_list_prod, Function.comp_def, map_commutatorElement] using hRel'

@[local simp]
theorem compactPresentationHomToProfinite_elliptic
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (i : Fin Δ.signature.numPeriods) :
    compactPresentationHomToProfinite Δ hCompact hPeriods
        (ellipticElement
          (compactFuchsianSignature Δ.signature hCompact hPeriods) i) =
      Δ.inertia i := by
  simp only [compactPresentationHomToProfinite, ellipticElement, PresentedGroup.toGroup.of]

@[local simp]
theorem compactPresentationHomToProfinite_surfaceA
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (i : Fin Δ.signature.orbitGenus) :
    compactPresentationHomToProfinite Δ hCompact hPeriods
        (PresentedGroup.of
          (rels := relators
            (compactFuchsianSignature Δ.signature hCompact hPeriods))
          (FuchsianGenerator.surfaceA i)) =
      Δ.surfaceA i := by
  simp only [compactPresentationHomToProfinite, PresentedGroup.toGroup.of]

@[local simp]
theorem compactPresentationHomToProfinite_surfaceB
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (i : Fin Δ.signature.orbitGenus) :
    compactPresentationHomToProfinite Δ hCompact hPeriods
        (PresentedGroup.of
          (rels := relators
            (compactFuchsianSignature Δ.signature hCompact hPeriods))
          (FuchsianGenerator.surfaceB i)) =
      Δ.surfaceB i := by
  simp only [compactPresentationHomToProfinite, PresentedGroup.toGroup.of]

private theorem compactPresentationHomToProfinite_elliptic_order
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (i : Fin Δ.signature.numPeriods) :
    orderOf
        (ellipticElement
          (compactFuchsianSignature Δ.signature hCompact hPeriods) i) =
      Δ.signature.periods i := by
  apply Nat.dvd_antisymm
  · simpa [compactFuchsianSignature] using
      orderOf_dvd_of_pow_eq_one
        (ellipticElement_pow_period_eq_one
          (compactFuchsianSignature Δ.signature hCompact hPeriods) i)
  · have hdiv :=
      orderOf_map_dvd
        (compactPresentationHomToProfinite Δ hCompact hPeriods)
        (ellipticElement
          (compactFuchsianSignature Δ.signature hCompact hPeriods) i)
    simpa [compactPresentationHomToProfinite_elliptic,
      Δ.inertia_order i] using hdiv

private noncomputable def compactDiscreteNormalQuotientGeneratorImageCore
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (H : Subgroup
      (FuchsianPresentedGroup
        (compactFuchsianSignature Δ.signature hCompact hPeriods)))
    [H.Normal] :
    ProfiniteFenchelGeneratorIndex.{u} Δ.signature →
      FuchsianPresentedGroup
          (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H
  | ULift.up (.surfaceA i) =>
      QuotientGroup.mk' H
        (PresentedGroup.of
          (rels := relators
            (compactFuchsianSignature Δ.signature hCompact hPeriods))
          (FuchsianGenerator.surfaceA i))
  | ULift.up (.surfaceB i) =>
      QuotientGroup.mk' H
        (PresentedGroup.of
          (rels := relators
            (compactFuchsianSignature Δ.signature hCompact hPeriods))
          (FuchsianGenerator.surfaceB i))
  | ULift.up (.cusp _) => 1
  | ULift.up (.inertia i) =>
      QuotientGroup.mk' H
        (ellipticElement
          (compactFuchsianSignature Δ.signature hCompact hPeriods) i)

private noncomputable def compactDiscreteNormalQuotientGeneratorImage
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (H : Subgroup
      (FuchsianPresentedGroup
        (compactFuchsianSignature Δ.signature hCompact hPeriods)))
    [H.Normal] :
    ProfiniteFenchelGeneratorIndex.{u} Δ.signature →
      ULift.{u, 0}
        (FuchsianPresentedGroup
            (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H) :=
  fun x =>
    ULift.up
      (compactDiscreteNormalQuotientGeneratorImageCore Δ hCompact hPeriods H x)

private theorem compactDiscreteNormalQuotientGeneratorImage_total_relation
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (H : Subgroup
      (FuchsianPresentedGroup
        (compactFuchsianSignature Δ.signature hCompact hPeriods)))
    [H.Normal] :
    profiniteFenchelTotalRelation
        (fun i => compactDiscreteNormalQuotientGeneratorImageCore
          Δ hCompact hPeriods H
          (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
        (fun i => compactDiscreteNormalQuotientGeneratorImageCore
          Δ hCompact hPeriods H
          (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
        (fun j => compactDiscreteNormalQuotientGeneratorImageCore
          Δ hCompact hPeriods H
          (ULift.up (ProfiniteFenchelGenerator.cusp j)))
        (fun k => compactDiscreteNormalQuotientGeneratorImageCore
          Δ hCompact hPeriods H
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) = 1 := by
  let σ := compactFuchsianSignature Δ.signature hCompact hPeriods
  let q : FuchsianPresentedGroup σ →*
      FuchsianPresentedGroup σ ⧸ H :=
    QuotientGroup.mk' H
  have hPresented :
      q (PresentedGroup.mk (relators σ) (totalRelation σ)) = 1 := by
    simpa using congrArg q
      (PresentedGroup.one_of_mem (rels := relators σ)
        (x := totalRelation σ) (Or.inr rfl))
  have hPresented' :
      q (PresentedGroup.mk (relators σ)
            (((List.finRange Δ.signature.numPeriods).map fun i =>
              xWord σ i).prod)) *
          q (PresentedGroup.mk (relators σ)
            (((List.finRange Δ.signature.orbitGenus).map fun j =>
              ⁅aWord σ j, bWord σ j⁆).prod)) =
        1 := by
    simpa [σ, q, totalRelation, xWord, aWord, bWord, ellipticElement,
      Function.comp_def, map_commutatorElement, compactFuchsianSignature] using hPresented
  have hDiscreteTotal :
      ((List.finRange Δ.signature.numPeriods).map fun i =>
            q (PresentedGroup.mk (relators σ) (xWord σ i))).prod *
          ((List.finRange Δ.signature.orbitGenus).map fun j =>
            ⁅q (PresentedGroup.mk (relators σ) (aWord σ j)),
              q (PresentedGroup.mk (relators σ) (bWord σ j))⁆).prod =
        1 := by
    simpa [map_list_prod, Function.comp_def, map_commutatorElement] using hPresented'
  have hSwapped :
      ((List.finRange Δ.signature.orbitGenus).map fun j =>
            ⁅q (PresentedGroup.mk (relators σ) (aWord σ j)),
              q (PresentedGroup.mk (relators σ) (bWord σ j))⁆).prod *
          ((List.finRange Δ.signature.numPeriods).map fun i =>
            q (PresentedGroup.mk (relators σ) (xWord σ i))).prod =
        1 :=
    mul_swap_eq_one_of_mul_eq_one hDiscreteTotal
  have hCusp :
      ((List.finRange Δ.signature.numCusps).map fun _j =>
          (1 :
            FuchsianPresentedGroup σ ⧸ H)).prod = 1 := by
    rw [hCompact]
    simp only [List.finRange_zero, List.map_nil, List.prod_nil]
  simpa [profiniteFenchelTotalRelation,
    compactDiscreteNormalQuotientGeneratorImageCore, σ, q, hCusp,
    compactFuchsianSignature, mul_assoc] using hSwapped

private theorem compactDiscreteNormalQuotientGeneratorImage_lifted_total_relation
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (H : Subgroup
      (FuchsianPresentedGroup
        (compactFuchsianSignature Δ.signature hCompact hPeriods)))
    [H.Normal] :
    profiniteFenchelTotalRelation
        (fun i => compactDiscreteNormalQuotientGeneratorImage
          Δ hCompact hPeriods H
          (ULift.up (ProfiniteFenchelGenerator.surfaceA i)))
        (fun i => compactDiscreteNormalQuotientGeneratorImage
          Δ hCompact hPeriods H
          (ULift.up (ProfiniteFenchelGenerator.surfaceB i)))
        (fun j => compactDiscreteNormalQuotientGeneratorImage
          Δ hCompact hPeriods H
          (ULift.up (ProfiniteFenchelGenerator.cusp j)))
        (fun k => compactDiscreteNormalQuotientGeneratorImage
          Δ hCompact hPeriods H
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) = 1 := by
  apply
    (MulEquiv.ulift :
      ULift.{u, 0}
        (FuchsianPresentedGroup
          (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H) ≃*
        FuchsianPresentedGroup
          (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H).injective
  simpa [compactDiscreteNormalQuotientGeneratorImage, profiniteFenchelTotalRelation,
    map_list_prod, Function.comp_def, map_commutatorElement] using
    compactDiscreteNormalQuotientGeneratorImage_total_relation
      Δ hCompact hPeriods H

private theorem compactDiscreteNormalQuotientGeneratorImage_period_relation
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (H : Subgroup
      (FuchsianPresentedGroup
        (compactFuchsianSignature Δ.signature hCompact hPeriods)))
    [H.Normal]
    (k : Fin Δ.signature.numPeriods) :
    compactDiscreteNormalQuotientGeneratorImageCore
        Δ hCompact hPeriods H
        (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^
      Δ.signature.periods k = 1 := by
  change
      (QuotientGroup.mk' H
        (ellipticElement
          (compactFuchsianSignature Δ.signature hCompact hPeriods) k)) ^
        (compactFuchsianSignature Δ.signature hCompact hPeriods).periods k = 1
  rw [← map_pow, ellipticElement_pow_period_eq_one, map_one]

private theorem compactDiscreteNormalQuotientGeneratorImage_lifted_period_relation
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (H : Subgroup
      (FuchsianPresentedGroup
        (compactFuchsianSignature Δ.signature hCompact hPeriods)))
    [H.Normal]
    (k : Fin Δ.signature.numPeriods) :
    compactDiscreteNormalQuotientGeneratorImage
        Δ hCompact hPeriods H
        (ULift.up (ProfiniteFenchelGenerator.inertia k)) ^
      Δ.signature.periods k = 1 := by
  apply
    (MulEquiv.ulift :
      ULift.{u, 0}
        (FuchsianPresentedGroup
          (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H) ≃*
        FuchsianPresentedGroup
          (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H).injective
  simpa [compactDiscreteNormalQuotientGeneratorImage] using
    compactDiscreteNormalQuotientGeneratorImage_period_relation
      Δ hCompact hPeriods H k

private theorem compactDiscreteNormalQuotient_derivedLength
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (H : Subgroup
      (FuchsianPresentedGroup
        (compactFuchsianSignature Δ.signature hCompact hPeriods)))
    [H.Normal]
    (hHQuot :
      SubgroupQuotientHasDerivedLengthAtMost H 3) :
    derivedSeries
        (FuchsianPresentedGroup
          (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H) 3 =
      ⊥ := by
  let σ := compactFuchsianSignature Δ.signature hCompact hPeriods
  let q : FuchsianPresentedGroup σ →*
      FuchsianPresentedGroup σ ⧸ H :=
    QuotientGroup.mk' H
  have hmap :
      Subgroup.map q (derivedSeries (FuchsianPresentedGroup σ) 3) =
        derivedSeries (FuchsianPresentedGroup σ ⧸ H) 3 :=
    derivedSeries_map_surjective q (QuotientGroup.mk'_surjective H) 3
  apply le_antisymm
  · intro y hy
    rw [← hmap] at hy
    rcases hy with ⟨x, hx, rfl⟩
    exact Subgroup.mem_bot.mpr
      ((QuotientGroup.eq_one_iff x).2 (hHQuot hx))
  · exact bot_le

private theorem compactDiscreteNormalQuotientGeneratorImage_inertia_order
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (H : Subgroup
      (FuchsianPresentedGroup
        (compactFuchsianSignature Δ.signature hCompact hPeriods)))
    [H.Normal]
    (hHTF : IsTorsionFreeGroup H)
    (k : Fin Δ.signature.numPeriods) :
    orderOf
        (compactDiscreteNormalQuotientGeneratorImageCore
          Δ hCompact hPeriods H
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) =
      Δ.signature.periods k := by
  let σ := compactFuchsianSignature Δ.signature hCompact hPeriods
  let q : FuchsianPresentedGroup σ →*
      FuchsianPresentedGroup σ ⧸ H :=
    QuotientGroup.mk' H
  have hKerTF : IsTorsionFreeGroup q.ker := by
    change IsTorsionFreeGroup (QuotientGroup.mk' H).ker
    rw [QuotientGroup.ker_mk']
    exact hHTF
  have hFinite : IsOfFinOrder (ellipticElement σ k) := by
    rw [← orderOf_pos_iff]
    rw [compactPresentationHomToProfinite_elliptic_order Δ hCompact hPeriods k]
    exact lt_of_lt_of_le (by decide : 0 < 2) (Δ.signature.period_ge_two k)
  calc
    orderOf
        (compactDiscreteNormalQuotientGeneratorImageCore
          Δ hCompact hPeriods H
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) =
        orderOf (q (ellipticElement σ k)) := by
          rfl
    _ = orderOf (ellipticElement σ k) :=
        orderOf_map_eq_of_torsionFree_ker q hKerTF hFinite
    _ = Δ.signature.periods k :=
        compactPresentationHomToProfinite_elliptic_order Δ hCompact hPeriods k

private theorem compactDiscreteNormalQuotientGeneratorImage_lifted_inertia_order
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (H : Subgroup
      (FuchsianPresentedGroup
        (compactFuchsianSignature Δ.signature hCompact hPeriods)))
    [H.Normal]
    (hHTF : IsTorsionFreeGroup H)
    (k : Fin Δ.signature.numPeriods) :
    orderOf
        (compactDiscreteNormalQuotientGeneratorImage
          Δ hCompact hPeriods H
          (ULift.up (ProfiniteFenchelGenerator.inertia k))) =
      Δ.signature.periods k := by
  have horder :=
    orderOf_injective
      ((MulEquiv.ulift :
        ULift.{u, 0}
          (FuchsianPresentedGroup
            (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H) ≃*
          FuchsianPresentedGroup
            (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H).toMonoidHom)
      (MulEquiv.ulift :
        ULift.{u, 0}
          (FuchsianPresentedGroup
            (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H) ≃*
          FuchsianPresentedGroup
            (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H).injective
      (compactDiscreteNormalQuotientGeneratorImage Δ hCompact hPeriods H
        (ULift.up (ProfiniteFenchelGenerator.inertia k)))
  rw [← horder]
  exact
    compactDiscreteNormalQuotientGeneratorImage_inertia_order
      Δ hCompact hPeriods H hHTF k

private noncomputable def compactDiscreteNormalQuotientSmoothData
    (Δ : ProfiniteFGroup.{u})
    (hCompact : Δ.signature.IsCompact)
    (hPeriods : 3 ≤ Δ.signature.numPeriods)
    (H : Subgroup
      (FuchsianPresentedGroup
        (compactFuchsianSignature Δ.signature hCompact hPeriods)))
    (hHFiniteIndex : H.FiniteIndex)
    (hHNormal : H.Normal)
    (hHTF : IsTorsionFreeGroup H)
    (hHQuot : SubgroupQuotientHasDerivedLengthAtMost H 3) :
    ProfiniteSmoothQuotientData Δ 3 := by
  letI : H.Normal := hHNormal
  letI : H.FiniteIndex := hHFiniteIndex
  letI :
      TopologicalSpace
        (ULift.{u, 0}
          (FuchsianPresentedGroup
            (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H)) :=
    ⊥
  letI :
      DiscreteTopology
        (ULift.{u, 0}
          (FuchsianPresentedGroup
            (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H)) :=
    ⟨rfl⟩
  letI :
      Finite
        (ULift.{u, 0}
          (FuchsianPresentedGroup
            (compactFuchsianSignature Δ.signature hCompact hPeriods) ⧸ H)) := by
    infer_instance
  exact
    ProfiniteSmoothQuotientData.ofPresentationLiftToFiniteOfRelationsOfDerivedSeries
      Δ (compactDiscreteNormalQuotientGeneratorImage Δ hCompact hPeriods H)
      (compactDiscreteNormalQuotientGeneratorImage_lifted_total_relation
        Δ hCompact hPeriods H)
      (compactDiscreteNormalQuotientGeneratorImage_lifted_period_relation
        Δ hCompact hPeriods H)
      (derivedSeries_ulift_eq_bot_of
        (compactDiscreteNormalQuotient_derivedLength
          Δ hCompact hPeriods H hHQuot))
      (compactDiscreteNormalQuotientGeneratorImage_lifted_inertia_order
        Δ hCompact hPeriods H hHTF)

private theorem compactDiscrete_sourceSubgroup_exists_of_isNonPerfect_zeroGenus
    (Δ : ProfiniteFGroup.{u})
    (hNonPerfect : Δ.IsNonPerfect)
    (hCompact : Δ.signature.IsCompact)
    (hZero : Δ.signature.orbitGenus = 0)
    (hPeriods : 3 ≤ Δ.signature.numPeriods) :
    ∃ H : Subgroup
        (FuchsianPresentedGroup
          (compactFuchsianSignature Δ.signature hCompact hPeriods)),
      H.FiniteIndex ∧ IsTorsionFreeGroup H ∧
        SubgroupQuotientHasDerivedLengthAtMost H 3 := by
  classical
  let σ := compactFuchsianSignature Δ.signature hCompact hPeriods
  have hZeroσ : σ.orbitGenus = 0 := by
    simpa [σ, compactFuchsianSignature] using hZero
  rcases
    exists_prime_dvd_two_periods_of_isNonPerfect_zeroGenus_noCusps
      Δ hNonPerfect hZero hCompact with
    ⟨p, hpPrime, i, j, hij, hpi, hpj⟩
  let D : FirstReductionPeriodData σ :=
    firstReductionPeriodDataOfPrimePair σ hpPrime hij
      (by simpa [σ, compactFuchsianSignature] using hpi)
      (by simpa [σ, compactFuchsianSignature] using hpj)
  exact threeStep_sourceSubgroup_exists_of_zeroGenus_periodData σ hZeroσ D

/-- Compact zero-genus profinite bridge: explicit zero-genus discrete period data transports through
an exact profinite Fenchel presentation to the required profinite open-normal conclusion. -/
theorem compactDiscreteBridge_threeStep_normal_of_isNonPerfect
    (Δ : ProfiniteFGroup.{u})
    (hNonPerfect : Δ.IsNonPerfect)
    (hCompact : Δ.signature.IsCompact)
    (hZero : Δ.signature.orbitGenus = 0)
    (hPeriods : 3 ≤ Δ.signature.numPeriods) :
    HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost
      Δ.carrier 3 := by
  classical
  let σ := compactFuchsianSignature Δ.signature hCompact hPeriods
  rcases compactDiscrete_sourceSubgroup_exists_of_isNonPerfect_zeroGenus
      Δ hNonPerfect hCompact hZero hPeriods with
    ⟨Hsource, hHsourceFiniteIndex, hHsourceTF, hHsourceQuot⟩
  haveI : Hsource.FiniteIndex := hHsourceFiniteIndex
  rcases
    hasFiniteIndexTorsionFreeNormalSubgroupWithDerivedLengthAtMost_of_subgroup
      Hsource hHsourceTF hHsourceQuot with
    ⟨H, hHFiniteIndex, hHNormal, hHTF, hHQuot⟩
  exact
    (compactDiscreteNormalQuotientSmoothData
      Δ hCompact hPeriods H hHFiniteIndex hHNormal hHTF hHQuot
    ).has_torsionFreeOpenNormal_quotient_derivedLengthAtMost

end ProfiniteFGroup

end FenchelNielsen
