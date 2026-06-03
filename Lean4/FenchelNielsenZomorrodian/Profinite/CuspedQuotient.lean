import FenchelNielsenZomorrodian.Discrete.Coordinates.FenchelPeriodCoordinate
import FenchelNielsenZomorrodian.Profinite.SmoothQuotient

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Profinite/CuspedQuotient.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Cusped finite abelian quotients

Constructs direct finite abelian quotients for profinite Fenchel groups with cusps, preserving every inertia order and giving derived length one.
-/

namespace FenchelNielsen

universe u v

namespace ProfiniteFGroup

open scoped BigOperators

private theorem ulift_list_prod_down {α : Type v} [Monoid α]
    (xs : List (ULift.{u, v} α)) :
    xs.prod.down = (xs.map (fun x => x.down)).prod := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.prod_cons, ULift.mul_down, ih, List.map_cons]

/-- Private witness: the distinguished cusp used to cancel the total relation in the direct cusped
quotient. -/
private def firstCusp (σ : FenchelSignature) (hCusps : σ.HasCusps) : Fin σ.numCusps :=
  ⟨0, hCusps⟩

/-- The finite abelian target used in the cusped one-step quotient. -/
abbrev CuspedSmoothQuotient (σ : FenchelSignature) :=
  Multiplicative (FenchelPeriodCoordinate σ)

instance instTopologicalSpaceCuspedSmoothQuotient (σ : FenchelSignature) :
    TopologicalSpace (CuspedSmoothQuotient σ) :=
  ⊥

instance instDiscreteTopologyCuspedSmoothQuotient (σ : FenchelSignature) :
    DiscreteTopology (CuspedSmoothQuotient σ) :=
  ⟨rfl⟩

noncomputable instance instFiniteULiftCuspedSmoothQuotient (σ : FenchelSignature) :
    Finite (ULift.{u, 0} (CuspedSmoothQuotient σ)) := by
  letI : Finite (FenchelPeriodCoordinate σ) :=
    zmodCoordinateFamily_finite σ.periods
      (fun i => lt_of_lt_of_le (by decide : 0 < 2) (σ.period_ge_two i))
  infer_instance

/-- Direct cusped quotient on profinite Fenchel generators.

This replaces the previous detour through the general discrete cusped presentation.  The cusped
branch only needs the finite abelian target and the generator assignment; no presented discrete
homomorphism is used downstream. -/
def cuspedSmoothGeneratorImageCore
    (σ : FenchelSignature) (hCusps : σ.HasCusps) :
    ProfiniteFenchelGeneratorIndex.{u} σ → CuspedSmoothQuotient σ
  | ULift.up (.surfaceA _) => 1
  | ULift.up (.surfaceB _) => 1
  | ULift.up (.cusp j) =>
      if j = firstCusp σ hCusps then
        Multiplicative.ofAdd (-(fenchelPeriodBasisSum σ))
      else
        1
  | ULift.up (.inertia k) =>
      Multiplicative.ofAdd (fenchelPeriodBasisVector σ k)

/-- The direct cusped quotient, universe-lifted to match `Δ.carrier`. -/
def cuspedSmoothGeneratorImage
    (Δ : ProfiniteFGroup.{u}) (hCusps : Δ.signature.HasCusps) :
    ProfiniteFenchelGeneratorIndex.{u} Δ.signature →
      ULift.{u, 0} (CuspedSmoothQuotient Δ.signature) :=
  fun x => ULift.up (cuspedSmoothGeneratorImageCore Δ.signature hCusps x)

private theorem cuspedSmooth_inertia_list_product
    (σ : FenchelSignature) (hCusps : σ.HasCusps) :
    (List.map
        (fun k : Fin σ.numPeriods =>
          cuspedSmoothGeneratorImageCore (σ := σ) hCusps
            (ULift.up.{u, 0} (ProfiniteFenchelGenerator.inertia k)))
        (List.finRange σ.numPeriods)).prod =
      Multiplicative.ofAdd (fenchelPeriodBasisSum σ) := by
  rw [show
      (fun k : Fin σ.numPeriods =>
          cuspedSmoothGeneratorImageCore (σ := σ) hCusps
            (ULift.up.{u, 0} (ProfiniteFenchelGenerator.inertia k))) =
        fun k : Fin σ.numPeriods =>
          Multiplicative.ofAdd (fenchelPeriodBasisVector σ k) by
        funext k
        simp only [cuspedSmoothGeneratorImageCore]]
  calc
    (List.map
        (fun k : Fin σ.numPeriods =>
          Multiplicative.ofAdd (fenchelPeriodBasisVector σ k))
        (List.finRange σ.numPeriods)).prod =
        ∏ k : Fin σ.numPeriods,
          Multiplicative.ofAdd (fenchelPeriodBasisVector σ k) := by
      simpa using
        (Fin.prod_univ_def
          (f := fun k : Fin σ.numPeriods =>
            Multiplicative.ofAdd (fenchelPeriodBasisVector σ k))).symm
    _ = Multiplicative.ofAdd (fenchelPeriodBasisSum σ) := by
      symm
      exact ofAdd_sum
        (s := Finset.univ)
        (f := fun k : Fin σ.numPeriods => fenchelPeriodBasisVector σ k)

private theorem cuspedSmooth_cusp_list_product
    (σ : FenchelSignature) (hCusps : σ.HasCusps) :
    (List.map
        (fun j : Fin σ.numCusps =>
          cuspedSmoothGeneratorImageCore (σ := σ) hCusps
            (ULift.up.{u, 0} (ProfiniteFenchelGenerator.cusp j)))
        (List.finRange σ.numCusps)).prod =
      Multiplicative.ofAdd (-(fenchelPeriodBasisSum σ)) := by
  classical
  calc
    (List.map
        (fun j : Fin σ.numCusps =>
          cuspedSmoothGeneratorImageCore (σ := σ) hCusps
            (ULift.up.{u, 0} (ProfiniteFenchelGenerator.cusp j)))
        (List.finRange σ.numCusps)).prod =
        ∏ j : Fin σ.numCusps,
          cuspedSmoothGeneratorImageCore (σ := σ) hCusps
            (ULift.up.{u, 0} (ProfiniteFenchelGenerator.cusp j)) := by
      simpa using
        (Fin.prod_univ_def
          (f := fun j : Fin σ.numCusps =>
            cuspedSmoothGeneratorImageCore (σ := σ) hCusps
              (ULift.up.{u, 0} (ProfiniteFenchelGenerator.cusp j)))).symm
    _ = Multiplicative.ofAdd (-(fenchelPeriodBasisSum σ)) := by
      rw [Finset.prod_eq_single (firstCusp σ hCusps)]
      · simp only [cuspedSmoothGeneratorImageCore, ↓reduceIte, ofAdd_neg]
      · intro j _hj hj
        simp only [cuspedSmoothGeneratorImageCore, hj, ↓reduceIte]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))

private theorem cuspedSmoothGeneratorImage_total_relation
    (Δ : ProfiniteFGroup.{u}) (hCusps : Δ.signature.HasCusps) :
    profiniteFenchelTotalRelation
        (fun i => cuspedSmoothGeneratorImageCore Δ.signature hCusps
          (ULift.up.{u, 0} (ProfiniteFenchelGenerator.surfaceA i)))
        (fun i => cuspedSmoothGeneratorImageCore Δ.signature hCusps
          (ULift.up.{u, 0} (ProfiniteFenchelGenerator.surfaceB i)))
      (fun j => cuspedSmoothGeneratorImageCore Δ.signature hCusps
        (ULift.up.{u, 0} (ProfiniteFenchelGenerator.cusp j)))
      (fun k => cuspedSmoothGeneratorImageCore Δ.signature hCusps
        (ULift.up.{u, 0} (ProfiniteFenchelGenerator.inertia k))) = 1 := by
  dsimp [profiniteFenchelTotalRelation]
  rw [cuspedSmooth_cusp_list_product, cuspedSmooth_inertia_list_product]
  simp only [cuspedSmoothGeneratorImageCore, commutatorElement_self, List.map_const', List.length_finRange,
  List.prod_replicate, one_pow, ofAdd_neg, one_mul, inv_mul_cancel]

private theorem cuspedSmoothGeneratorImage_lifted_total_relation
    (Δ : ProfiniteFGroup.{u}) (hCusps : Δ.signature.HasCusps) :
    profiniteFenchelTotalRelation
        (fun i => cuspedSmoothGeneratorImage Δ hCusps
          (ULift.up.{u, 0} (ProfiniteFenchelGenerator.surfaceA i)))
        (fun i => cuspedSmoothGeneratorImage Δ hCusps
          (ULift.up.{u, 0} (ProfiniteFenchelGenerator.surfaceB i)))
      (fun j => cuspedSmoothGeneratorImage Δ hCusps
        (ULift.up.{u, 0} (ProfiniteFenchelGenerator.cusp j)))
      (fun k => cuspedSmoothGeneratorImage Δ hCusps
        (ULift.up.{u, 0} (ProfiniteFenchelGenerator.inertia k))) = 1 := by
  let e :
      ULift.{u, 0} (CuspedSmoothQuotient Δ.signature) ≃*
        CuspedSmoothQuotient Δ.signature :=
    MulEquiv.ulift
  apply e.injective
  simp only [MulEquiv.ulift, profiniteFenchelTotalRelation, cuspedSmoothGeneratorImage, MulEquiv.coe_mk,
  Equiv.ulift_apply, ULift.mul_down, ULift.one_down, e]
  rw [ulift_list_prod_down, ulift_list_prod_down, ulift_list_prod_down]
  have h := cuspedSmoothGeneratorImage_total_relation Δ hCusps
  dsimp [profiniteFenchelTotalRelation] at h
  simpa [List.map_map, Function.comp_def, commutatorElement,
    cuspedSmoothGeneratorImageCore] using h

private theorem cuspedSmoothGeneratorImage_period_relation
    (Δ : ProfiniteFGroup.{u}) (hCusps : Δ.signature.HasCusps)
    (k : Fin Δ.signature.numPeriods) :
    cuspedSmoothGeneratorImageCore Δ.signature hCusps
        (ULift.up.{u, 0} (ProfiniteFenchelGenerator.inertia k)) ^
      Δ.signature.periods k = 1 := by
  change
    Multiplicative.ofAdd (fenchelPeriodBasisVector Δ.signature k) ^
      Δ.signature.periods k = 1
  rw [← ofAdd_nsmul]
  rw [show
      Δ.signature.periods k • fenchelPeriodBasisVector Δ.signature k = 0 by
        simpa [fenchelPeriodBasisVector] using
          zmodBasisVector_nsmul_eq_zero Δ.signature.periods k]
  rfl

private theorem cuspedSmoothGeneratorImage_lifted_period_relation
    (Δ : ProfiniteFGroup.{u}) (hCusps : Δ.signature.HasCusps)
    (k : Fin Δ.signature.numPeriods) :
    cuspedSmoothGeneratorImage Δ hCusps
        (ULift.up.{u, 0} (ProfiniteFenchelGenerator.inertia k)) ^
      Δ.signature.periods k = 1 := by
  let e :
      ULift.{u, 0} (CuspedSmoothQuotient Δ.signature) ≃*
        CuspedSmoothQuotient Δ.signature :=
    MulEquiv.ulift
  apply e.injective
  simp only [MulEquiv.ulift, cuspedSmoothGeneratorImage, MulEquiv.coe_mk, Equiv.ulift_apply, ULift.pow_down,
  ULift.one_down, e]
  exact cuspedSmoothGeneratorImage_period_relation Δ hCusps k

private theorem cuspedSmoothGeneratorImage_inertia_order
    (Δ : ProfiniteFGroup.{u}) (hCusps : Δ.signature.HasCusps)
    (k : Fin Δ.signature.numPeriods) :
    orderOf
        (cuspedSmoothGeneratorImageCore Δ.signature hCusps
          (ULift.up.{u, 0} (ProfiniteFenchelGenerator.inertia k))) =
      Δ.signature.periods k := by
  rw [cuspedSmoothGeneratorImageCore, orderOf_ofAdd_eq_addOrderOf]
  exact zmodBasisVector_addOrderOf Δ.signature.periods k

private theorem cuspedSmoothGeneratorImage_lifted_inertia_order
    (Δ : ProfiniteFGroup.{u}) (hCusps : Δ.signature.HasCusps)
    (k : Fin Δ.signature.numPeriods) :
    orderOf
        (cuspedSmoothGeneratorImage Δ hCusps
          (ULift.up.{u, 0} (ProfiniteFenchelGenerator.inertia k))) =
      Δ.signature.periods k := by
  let e :
      ULift.{u, 0} (CuspedSmoothQuotient Δ.signature) ≃*
        CuspedSmoothQuotient Δ.signature :=
    MulEquiv.ulift
  have horder :=
    orderOf_injective
      e.toMonoidHom
      e.injective
      (cuspedSmoothGeneratorImage Δ hCusps
        (ULift.up.{u, 0} (ProfiniteFenchelGenerator.inertia k)))
  have hcore :
      orderOf
          (e.toMonoidHom (cuspedSmoothGeneratorImage Δ hCusps
            (ULift.up.{u, 0} (ProfiniteFenchelGenerator.inertia k)))) =
        Δ.signature.periods k := by
    exact cuspedSmoothGeneratorImage_inertia_order Δ hCusps k
  exact horder.symm.trans hcore

noncomputable def cuspedSmoothQuotientData
    (Δ : ProfiniteFGroup.{u}) (hCusps : Δ.signature.HasCusps) :
    ProfiniteSmoothQuotientData Δ 1 :=
  ProfiniteSmoothQuotientData.ofPresentationLiftToFiniteOfRelations
    Δ (cuspedSmoothGeneratorImage Δ hCusps)
    (cuspedSmoothGeneratorImage_lifted_total_relation Δ hCusps)
    (cuspedSmoothGeneratorImage_lifted_period_relation Δ hCusps)
    (profiniteDerivedSeries_one_eq_bot_of_commGroup
      (ULift.{u, 0} (CuspedSmoothQuotient Δ.signature)))
    (cuspedSmoothGeneratorImage_lifted_inertia_order Δ hCusps)

end ProfiniteFGroup

end FenchelNielsen
