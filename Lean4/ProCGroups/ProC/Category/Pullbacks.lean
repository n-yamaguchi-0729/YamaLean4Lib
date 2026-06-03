import ProCGroups.Categorical.ProfinitePullbacks
import ProCGroups.ProC.Category.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/ProC/Category/Pullbacks.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Pro-C groups and open normal quotients

Defines pro-C conditions from finite group classes, C-open normal subgroups, pro-C categories, products, pullbacks, pushouts, and maximal pro-C quotients.
-/

open CategoryTheory

universe u

namespace ProCGrp

variable {ProC : ProCGroups.ProC.ProCGroupPredicate.{u}}
variable {G G' H H1 H2 : ProCGrp ProC}

/-- A pullback square in the bundled category `ProCGrp ProC`. -/
def IsPullbackSquare
    (alpha1 : G ⟶ H1) (alpha2 : G ⟶ H2)
    (beta1 : H1 ⟶ H) (beta2 : H2 ⟶ H) : Prop :=
  alpha1 ≫ beta1 = alpha2 ≫ beta2 ∧
    ∀ ⦃K : ProCGrp ProC⦄ (phi1 : K ⟶ H1) (phi2 : K ⟶ H2),
      phi1 ≫ beta1 = phi2 ≫ beta2 →
        ∃! phi : K ⟶ G, phi ≫ alpha1 = phi1 ∧ phi ≫ alpha2 = phi2

/-- Chosen morphism induced by a pro-`C` pullback universal property. -/
noncomputable def pullbackLift
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {beta1 : H1 ⟶ H} {beta2 : H2 ⟶ H}
    {K : ProCGrp ProC}
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    (phi1 : K ⟶ H1) (phi2 : K ⟶ H2)
    (hphi : phi1 ≫ beta1 = phi2 ≫ beta2) : K ⟶ G :=
  Classical.choose (ExistsUnique.exists (hpb.2 phi1 phi2 hphi))

/-- The chosen pullback lift has the prescribed composites. -/
theorem pullbackLift_spec
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {beta1 : H1 ⟶ H} {beta2 : H2 ⟶ H}
    {K : ProCGrp ProC}
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    (phi1 : K ⟶ H1) (phi2 : K ⟶ H2)
    (hphi : phi1 ≫ beta1 = phi2 ≫ beta2) :
    pullbackLift hpb phi1 phi2 hphi ≫ alpha1 = phi1 ∧
      pullbackLift hpb phi1 phi2 hphi ≫ alpha2 = phi2 :=
  Classical.choose_spec (ExistsUnique.exists (hpb.2 phi1 phi2 hphi))

/-- The pullback lift has the prescribed left projection. -/
@[simp] theorem pullbackLift_left
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {beta1 : H1 ⟶ H} {beta2 : H2 ⟶ H}
    {K : ProCGrp ProC}
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    (phi1 : K ⟶ H1) (phi2 : K ⟶ H2)
    (hphi : phi1 ≫ beta1 = phi2 ≫ beta2) :
    pullbackLift hpb phi1 phi2 hphi ≫ alpha1 = phi1 :=
  (pullbackLift_spec hpb phi1 phi2 hphi).1

/-- The pullback lift has the prescribed right projection. -/
@[simp] theorem pullbackLift_right
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {beta1 : H1 ⟶ H} {beta2 : H2 ⟶ H}
    {K : ProCGrp ProC}
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    (phi1 : K ⟶ H1) (phi2 : K ⟶ H2)
    (hphi : phi1 ≫ beta1 = phi2 ≫ beta2) :
    pullbackLift hpb phi1 phi2 hphi ≫ alpha2 = phi2 :=
  (pullbackLift_spec hpb phi1 phi2 hphi).2

/-- Uniqueness of the chosen pullback lift. -/
theorem pullbackLift_unique
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {beta1 : H1 ⟶ H} {beta2 : H2 ⟶ H}
    {K : ProCGrp ProC}
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    (phi1 : K ⟶ H1) (phi2 : K ⟶ H2)
    (hphi : phi1 ≫ beta1 = phi2 ≫ beta2)
    {psi : K ⟶ G}
    (hpsi : psi ≫ alpha1 = phi1 ∧ psi ≫ alpha2 = phi2) :
    psi = pullbackLift hpb phi1 phi2 hphi := by
  rcases hpb.2 phi1 phi2 hphi with ⟨u, hu, huniq⟩
  have hpsi' : psi = u := huniq _ hpsi
  have hchosen : pullbackLift hpb phi1 phi2 hphi = u :=
    huniq _ (pullbackLift_spec hpb phi1 phi2 hphi)
  exact hpsi'.trans hchosen.symm

/-- The self-lift of a pullback object is the identity morphism. -/
@[simp] theorem pullbackLift_self
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {beta1 : H1 ⟶ H} {beta2 : H2 ⟶ H}
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2) :
    pullbackLift hpb alpha1 alpha2 hpb.1 = 𝟙 G := by
  symm
  exact pullbackLift_unique hpb alpha1 alpha2 hpb.1 (psi := 𝟙 G) (by simp only [Category.id_comp, and_self])

/-- Extensionality of morphisms into a pro-`C` pullback object. -/
theorem pullback_hom_ext
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {beta1 : H1 ⟶ H} {beta2 : H2 ⟶ H}
    {K : ProCGrp ProC}
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    {psi psi' : K ⟶ G}
    (h1 : psi ≫ alpha1 = psi' ≫ alpha1)
    (h2 : psi ≫ alpha2 = psi' ≫ alpha2) :
    psi = psi' := by
  have hphi : (psi ≫ alpha1) ≫ beta1 = (psi ≫ alpha2) ≫ beta2 := by
    calc
      (psi ≫ alpha1) ≫ beta1 = psi ≫ (alpha1 ≫ beta1) := by simp only [Category.assoc]
      _ = psi ≫ (alpha2 ≫ beta2) := by rw [hpb.1]
      _ = (psi ≫ alpha2) ≫ beta2 := by simp only [Category.assoc]
  have hpsi :
      psi = pullbackLift hpb (psi ≫ alpha1) (psi ≫ alpha2) hphi := by
    exact pullbackLift_unique hpb (psi ≫ alpha1) (psi ≫ alpha2) hphi
      (psi := psi) ⟨rfl, rfl⟩
  have hpsi' :
      psi' = pullbackLift hpb (psi ≫ alpha1) (psi ≫ alpha2) hphi := by
    exact pullbackLift_unique hpb (psi ≫ alpha1) (psi ≫ alpha2) hphi
      (psi := psi') ⟨h1.symm, h2.symm⟩
  exact hpsi.trans hpsi'.symm

/-- Canonical comparison map from one pro-`C` pullback object to another. -/
noncomputable def pullbackMapOfIsPullback
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {alpha1' : G' ⟶ H1} {alpha2' : G' ⟶ H2}
    (beta1 : H1 ⟶ H) (beta2 : H2 ⟶ H)
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    (hpb' : IsPullbackSquare alpha1' alpha2' beta1 beta2) :
    G' ⟶ G :=
  pullbackLift hpb alpha1' alpha2' hpb'.1

/-- The comparison map from a pullback object to itself is the identity. -/
@[simp] theorem pullbackMapOfIsPullback_self
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    (beta1 : H1 ⟶ H) (beta2 : H2 ⟶ H)
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2) :
    pullbackMapOfIsPullback beta1 beta2 hpb hpb = 𝟙 G := by
  exact pullbackLift_self (hpb := hpb)

/-- The comparison map between pullback objects respects the left projection. -/
@[simp] theorem pullbackMapOfIsPullback_left
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {alpha1' : G' ⟶ H1} {alpha2' : G' ⟶ H2}
    (beta1 : H1 ⟶ H) (beta2 : H2 ⟶ H)
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    (hpb' : IsPullbackSquare alpha1' alpha2' beta1 beta2) :
    pullbackMapOfIsPullback beta1 beta2 hpb hpb' ≫ alpha1 = alpha1' :=
  pullbackLift_left hpb alpha1' alpha2' hpb'.1

/-- The comparison map between pullback objects respects the right projection. -/
@[simp] theorem pullbackMapOfIsPullback_right
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {alpha1' : G' ⟶ H1} {alpha2' : G' ⟶ H2}
    (beta1 : H1 ⟶ H) (beta2 : H2 ⟶ H)
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    (hpb' : IsPullbackSquare alpha1' alpha2' beta1 beta2) :
    pullbackMapOfIsPullback beta1 beta2 hpb hpb' ≫ alpha2 = alpha2' :=
  pullbackLift_right hpb alpha1' alpha2' hpb'.1

/-- Any two pro-`C` pullback objects of the same cospan are canonically isomorphic. -/
noncomputable def pullbackIsoOfIsPullback
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {alpha1' : G' ⟶ H1} {alpha2' : G' ⟶ H2}
    (beta1 : H1 ⟶ H) (beta2 : H2 ⟶ H)
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    (hpb' : IsPullbackSquare alpha1' alpha2' beta1 beta2) :
    G ≅ G' where
  hom := pullbackMapOfIsPullback beta1 beta2 hpb' hpb
  inv := pullbackMapOfIsPullback beta1 beta2 hpb hpb'
  hom_inv_id := by
    apply pullback_hom_ext hpb
    · calc
        (pullbackMapOfIsPullback beta1 beta2 hpb' hpb ≫
            pullbackMapOfIsPullback beta1 beta2 hpb hpb') ≫ alpha1 =
              pullbackMapOfIsPullback beta1 beta2 hpb' hpb ≫ alpha1' := by
          rw [Category.assoc, pullbackMapOfIsPullback_left]
        _ = alpha1 := pullbackMapOfIsPullback_left beta1 beta2 hpb' hpb
    · calc
        (pullbackMapOfIsPullback beta1 beta2 hpb' hpb ≫
            pullbackMapOfIsPullback beta1 beta2 hpb hpb') ≫ alpha2 =
              pullbackMapOfIsPullback beta1 beta2 hpb' hpb ≫ alpha2' := by
          rw [Category.assoc, pullbackMapOfIsPullback_right]
        _ = alpha2 := pullbackMapOfIsPullback_right beta1 beta2 hpb' hpb
  inv_hom_id := by
    apply pullback_hom_ext hpb'
    · calc
        (pullbackMapOfIsPullback beta1 beta2 hpb hpb' ≫
            pullbackMapOfIsPullback beta1 beta2 hpb' hpb) ≫ alpha1' =
              pullbackMapOfIsPullback beta1 beta2 hpb hpb' ≫ alpha1 := by
          rw [Category.assoc, pullbackMapOfIsPullback_left]
        _ = alpha1' := pullbackMapOfIsPullback_left beta1 beta2 hpb hpb'
    · calc
        (pullbackMapOfIsPullback beta1 beta2 hpb hpb' ≫
            pullbackMapOfIsPullback beta1 beta2 hpb' hpb) ≫ alpha2' =
              pullbackMapOfIsPullback beta1 beta2 hpb hpb' ≫ alpha2 := by
          rw [Category.assoc, pullbackMapOfIsPullback_right]
        _ = alpha2' := pullbackMapOfIsPullback_right beta1 beta2 hpb hpb'

/-- The canonical pullback isomorphism respects the left projection. -/
@[simp] theorem pullbackIsoOfIsPullback_hom_left
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {alpha1' : G' ⟶ H1} {alpha2' : G' ⟶ H2}
    (beta1 : H1 ⟶ H) (beta2 : H2 ⟶ H)
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    (hpb' : IsPullbackSquare alpha1' alpha2' beta1 beta2) :
    (pullbackIsoOfIsPullback beta1 beta2 hpb hpb').hom ≫ alpha1' = alpha1 :=
  pullbackMapOfIsPullback_left beta1 beta2 hpb' hpb

/-- The canonical pullback isomorphism respects the right projection. -/
@[simp] theorem pullbackIsoOfIsPullback_hom_right
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {alpha1' : G' ⟶ H1} {alpha2' : G' ⟶ H2}
    (beta1 : H1 ⟶ H) (beta2 : H2 ⟶ H)
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2)
    (hpb' : IsPullbackSquare alpha1' alpha2' beta1 beta2) :
    (pullbackIsoOfIsPullback beta1 beta2 hpb hpb').hom ≫ alpha2' = alpha2 :=
  pullbackMapOfIsPullback_right beta1 beta2 hpb' hpb

/-- A concrete continuous profinite pullback square is a pullback in `ProCGrp`. -/
theorem isPullbackSquare_of_hasProfiniteTestPullbackProperty
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {beta1 : H1 ⟶ H} {beta2 : H2 ⟶ H}
    (hpb : ProCGroups.Categorical.HasProfiniteTestPullbackProperty
      alpha1.hom alpha2.hom beta1.hom beta2.hom) :
    IsPullbackSquare alpha1 alpha2 beta1 beta2 := by
  refine ⟨?_, ?_⟩
  · apply hom_ext
    change beta1.hom.comp alpha1.hom = beta2.hom.comp alpha2.hom
    exact hpb.1
  · intro K phi1 phi2 hphi
    have hK : ProCGroups.IsProfiniteGroup K :=
      ProCGroups.ProC.ProCGroup.profiniteGroup ProC K
    have hphi' : beta1.hom.comp phi1.hom = beta2.hom.comp phi2.hom := by
      simpa using congrArg (fun f : K ⟶ H => f.hom) hphi
    rcases hpb.2 (K := K) hK phi1.hom phi2.hom hphi' with ⟨psi, hpsi, huniq⟩
    let psi' : K ⟶ G := ConcreteCategory.ofHom (C := ProCGrp ProC) psi
    refine ⟨psi', ?_, ?_⟩
    · constructor
      · apply hom_ext
        change alpha1.hom.comp psi = phi1.hom
        exact hpsi.1
      · apply hom_ext
        change alpha2.hom.comp psi = phi2.hom
        exact hpsi.2
    · intro theta htheta
      apply hom_ext
      change theta.hom = psi
      apply huniq
      constructor
      · simpa using congrArg (fun f : K ⟶ H1 => f.hom) htheta.1
      · simpa using congrArg (fun f : K ⟶ H2 => f.hom) htheta.2

/-- For the all-finite predicate, the bundled `ProCGrp` pullback property is equivalent to the
concrete profinite pullback property. -/
theorem hasProfiniteTestPullbackProperty_of_isPullbackSquare_allFinite
    {G H H1 H2 : ProCGrp ProCGroups.ProC.allFiniteProC}
    {alpha1 : G ⟶ H1} {alpha2 : G ⟶ H2}
    {beta1 : H1 ⟶ H} {beta2 : H2 ⟶ H}
    (hpb : IsPullbackSquare alpha1 alpha2 beta1 beta2) :
    ProCGroups.Categorical.HasProfiniteTestPullbackProperty
      alpha1.hom alpha2.hom beta1.hom beta2.hom := by
  refine ⟨?_, ?_⟩
  · change (alpha1 ≫ beta1).hom = (alpha2 ≫ beta2).hom
    exact congrArg (fun f : G ⟶ H => f.hom) hpb.1
  · intro K _ _ _ hK phi1 phi2 hphi
    letI : ProCGroups.ProC.ProCGroup ProCGroups.ProC.allFiniteProC K :=
      ProCGroups.ProC.ProCGroup.of_isProCGroup ProCGroups.ProC.allFiniteProC K
        (ProCGroups.ProC.allFiniteProC_isProCGroup_of_profinite hK)
    let Kc : ProCGrp ProCGroups.ProC.allFiniteProC :=
      ProCGrp.of ProCGroups.ProC.allFiniteProC K
    let phi1' : Kc ⟶ H1 := ConcreteCategory.ofHom (C := ProCGrp ProCGroups.ProC.allFiniteProC) phi1
    let phi2' : Kc ⟶ H2 := ConcreteCategory.ofHom (C := ProCGrp ProCGroups.ProC.allFiniteProC) phi2
    have hphi' : phi1' ≫ beta1 = phi2' ≫ beta2 := by
      apply hom_ext
      exact hphi
    rcases hpb.2 phi1' phi2' hphi' with ⟨psi, hpsi, huniq⟩
    refine ⟨psi.hom, ?_, ?_⟩
    · constructor
      · simpa using congrArg (fun f : Kc ⟶ H1 => f.hom) hpsi.1
      · simpa using congrArg (fun f : Kc ⟶ H2 => f.hom) hpsi.2
    · intro theta htheta
      let theta' : Kc ⟶ G :=
        ConcreteCategory.ofHom (C := ProCGrp ProCGroups.ProC.allFiniteProC) theta
      have htheta' : theta' ≫ alpha1 = phi1' ∧ theta' ≫ alpha2 = phi2' := by
        constructor
        · apply hom_ext
          exact htheta.1
        · apply hom_ext
          exact htheta.2
      have hthetaEq : theta' = psi := huniq theta' htheta'
      simpa using congrArg (fun f : Kc ⟶ G => f.hom) hthetaEq

end ProCGrp
