import ProCGroups.FreeProducts.UniversalProperty
import ProCGroups.ProC.InverseLimits.Limits
import ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation
import ProCGroups.ProC.OpenNormalSubgroups.Separation

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/ProCGroups/FreeProducts/Concrete.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Free pro-C products

Constructs free pro-C products from finite admissible quotients and proves the universal property and comparison isomorphisms.
-/

open scoped Monoid.Coprod Topology

namespace ProCGroups.FreeProducts

universe u

namespace Concrete

variable {A B : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
variable [Group B] [TopologicalSpace B] [IsTopologicalGroup B]

/-- The abstract group underlying the binary free product of the two factors. -/
abbrev AbstractFreeProduct (A B : Type u) [Group A] [Group B] :=
  A ∗ B

variable {C : ProCGroups.FiniteGroupClass.{u}}

/-- An admissible finite quotient of the abstract free product: the quotient lies in `C`, and the
two factor maps into that quotient are continuous. -/
structure AdmissibleQuotient (C : ProCGroups.FiniteGroupClass.{u})
    (A B : Type u) [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] where
  toSubgroup : Subgroup (AbstractFreeProduct A B)
  normal' : toSubgroup.Normal
  quotient_mem' : C (AbstractFreeProduct A B ⧸ toSubgroup)
  inl_continuous' :
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸ toSubgroup) := ⊥
    Continuous ((QuotientGroup.mk' toSubgroup).comp
      (Monoid.Coprod.inl : A →* AbstractFreeProduct A B))
  inr_continuous' :
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸ toSubgroup) := ⊥
    Continuous ((QuotientGroup.mk' toSubgroup).comp
      (Monoid.Coprod.inr : B →* AbstractFreeProduct A B))

namespace AdmissibleQuotient

/-- Coerce an admissible quotient to its underlying normal subgroup of the abstract free
product. -/
instance instCoeOutAdmissibleQuotient :
    CoeOut (AdmissibleQuotient C A B) (Subgroup (AbstractFreeProduct A B)) where
  coe U := U.toSubgroup

/-- The subgroup underlying an admissible quotient is normal. -/
instance instNormalCoeAdmissibleQuotient (U : AdmissibleQuotient C A B) :
    (U : Subgroup (AbstractFreeProduct A B)).Normal :=
  U.normal'

/-- Order admissible quotients by reverse inclusion of their kernels. -/
instance instLEAdmissibleQuotient : LE (AdmissibleQuotient C A B) where
  le U V := (V : Subgroup (AbstractFreeProduct A B)) ≤
    (U : Subgroup (AbstractFreeProduct A B))

/-- Admissible quotients form a preorder under reverse inclusion of kernels. -/
instance instPreorderAdmissibleQuotient : Preorder (AdmissibleQuotient C A B) where
  le := fun U V => (V : Subgroup (AbstractFreeProduct A B)) ≤
    (U : Subgroup (AbstractFreeProduct A B))
  le_refl U := le_rfl
  le_trans U V W hUV hVW := hVW.trans hUV

/-- The finite admissible quotient attached to an admissible quotient lies in the class `C`. -/
theorem quotient_mem (U : AdmissibleQuotient C A B) :
    C (AbstractFreeProduct A B ⧸ (U : Subgroup (AbstractFreeProduct A B))) :=
  U.quotient_mem'

/-- The left inclusion into an admissible quotient is continuous. -/
theorem inl_continuous (U : AdmissibleQuotient C A B) :
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸ (U : Subgroup (AbstractFreeProduct A B))) :=
      ⊥
    Continuous ((QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))).comp
      (Monoid.Coprod.inl : A →* AbstractFreeProduct A B)) :=
  U.inl_continuous'

/-- The right inclusion into an admissible quotient is continuous. -/
theorem inr_continuous (U : AdmissibleQuotient C A B) :
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸ (U : Subgroup (AbstractFreeProduct A B))) :=
      ⊥
    Continuous ((QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))).comp
      (Monoid.Coprod.inr : B →* AbstractFreeProduct A B)) :=
  U.inr_continuous'

/-- The canonical transition map between admissible free-product quotients. -/
def map {U V : AdmissibleQuotient C A B}
    (hUV : (V : Subgroup (AbstractFreeProduct A B)) ≤
      (U : Subgroup (AbstractFreeProduct A B))) :
    AbstractFreeProduct A B ⧸ (V : Subgroup (AbstractFreeProduct A B)) →*
      AbstractFreeProduct A B ⧸ (U : Subgroup (AbstractFreeProduct A B)) :=
  QuotientGroup.map _ _ (MonoidHom.id (AbstractFreeProduct A B)) hUV

/-- Transition maps between admissible quotients are surjective. -/
theorem map_surjective {U V : AdmissibleQuotient C A B}
    (hUV : (V : Subgroup (AbstractFreeProduct A B)) ≤
      (U : Subgroup (AbstractFreeProduct A B))) :
    Function.Surjective (map (C := C) (A := A) (B := B) hUV) := by
  intro x
  rcases QuotientGroup.mk'_surjective
      (U : Subgroup (AbstractFreeProduct A B)) x with ⟨g, rfl⟩
  exact ⟨QuotientGroup.mk' (V : Subgroup (AbstractFreeProduct A B)) g, rfl⟩

/-- The transition map from an admissible quotient to itself is the identity. -/
theorem map_id (U : AdmissibleQuotient C A B) :
    map (C := C) (A := A) (B := B)
      (le_rfl : (U : Subgroup (AbstractFreeProduct A B)) ≤
        (U : Subgroup (AbstractFreeProduct A B))) = MonoidHom.id _ := by
  simp only [map, QuotientGroup.map_id]

/-- Transition maps between admissible quotients compose along refinements. -/
theorem map_comp {U V W : AdmissibleQuotient C A B}
    (hUV : (V : Subgroup (AbstractFreeProduct A B)) ≤
      (U : Subgroup (AbstractFreeProduct A B)))
    (hVW : (W : Subgroup (AbstractFreeProduct A B)) ≤
      (V : Subgroup (AbstractFreeProduct A B))) :
    (map (C := C) (A := A) (B := B) hUV).comp
        (map (C := C) (A := A) (B := B) hVW) =
      map (C := C) (A := A) (B := B) (hVW.trans hUV) := by
  simpa [map] using QuotientGroup.map_comp_map
    (N := (W : Subgroup (AbstractFreeProduct A B)))
    (M := (V : Subgroup (AbstractFreeProduct A B)))
    (O := (U : Subgroup (AbstractFreeProduct A B)))
    (f := MonoidHom.id (AbstractFreeProduct A B))
    (g := MonoidHom.id (AbstractFreeProduct A B)) hVW hUV

/-- The top quotient, used as a nonempty index. -/
noncomputable def quotientTopMulEquivPUnit (G : Type u) [Group G] :
    G ⧸ (⊤ : Subgroup G) ≃* PUnit where
  toFun := fun _ => PUnit.unit
  invFun := fun _ => 1
  left_inv := by
    intro x
    refine Quotient.inductionOn' x ?_
    intro g
    apply QuotientGroup.eq.2
    simp only [inv_one, one_mul, Subgroup.mem_top]
  right_inv := by
    intro x
    cases x
    rfl
  map_mul' := by
    intro x y
    rfl

/-- The trivial admissible quotient. -/
noncomputable def top (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    AdmissibleQuotient C A B where
  toSubgroup := ⊤
  normal' := inferInstance
  quotient_mem' :=
    hForm.isomClosed ⟨(quotientTopMulEquivPUnit (AbstractFreeProduct A B)).symm⟩
      hForm.one_mem
  inl_continuous' := by
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸
        (⊤ : Subgroup (AbstractFreeProduct A B))) := ⊥
    refine (continuous_const : Continuous fun _ : A =>
      (1 : AbstractFreeProduct A B ⧸
        (⊤ : Subgroup (AbstractFreeProduct A B)))).congr ?_
    intro a
    apply QuotientGroup.eq.2
    simp only [inv_one, one_mul, Subgroup.mem_top]
  inr_continuous' := by
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸
        (⊤ : Subgroup (AbstractFreeProduct A B))) := ⊥
    refine (continuous_const : Continuous fun _ : B =>
      (1 : AbstractFreeProduct A B ⧸
        (⊤ : Subgroup (AbstractFreeProduct A B)))).congr ?_
    intro b
    apply QuotientGroup.eq.2
    simp only [inv_one, one_mul, Subgroup.mem_top]

private theorem isOpen_ker_of_continuous_quotient_inl (U : AdmissibleQuotient C A B) :
    IsOpen ((((QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))).comp
      (Monoid.Coprod.inl : A →* AbstractFreeProduct A B)).ker : Subgroup A) : Set A) := by
  letI : TopologicalSpace (AbstractFreeProduct A B ⧸ (U : Subgroup (AbstractFreeProduct A B))) :=
    ⊥
  letI : DiscreteTopology (AbstractFreeProduct A B ⧸
      (U : Subgroup (AbstractFreeProduct A B))) := ⟨rfl⟩
  have hcont := U.inl_continuous
  simpa [MonoidHom.mem_ker] using (isOpen_discrete ({1} :
    Set (AbstractFreeProduct A B ⧸ (U : Subgroup (AbstractFreeProduct A B))))).preimage hcont

private theorem isOpen_ker_of_continuous_quotient_inr (U : AdmissibleQuotient C A B) :
    IsOpen ((((QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))).comp
      (Monoid.Coprod.inr : B →* AbstractFreeProduct A B)).ker : Subgroup B) : Set B) := by
  letI : TopologicalSpace (AbstractFreeProduct A B ⧸ (U : Subgroup (AbstractFreeProduct A B))) :=
    ⊥
  letI : DiscreteTopology (AbstractFreeProduct A B ⧸
      (U : Subgroup (AbstractFreeProduct A B))) := ⟨rfl⟩
  have hcont := U.inr_continuous
  simpa [MonoidHom.mem_ker] using (isOpen_discrete ({1} :
    Set (AbstractFreeProduct A B ⧸ (U : Subgroup (AbstractFreeProduct A B))))).preimage hcont

/-- Intersections of admissible quotients are admissible for a formation. -/
noncomputable def inf (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (U V : AdmissibleQuotient C A B) : AdmissibleQuotient C A B where
  toSubgroup := (U : Subgroup (AbstractFreeProduct A B)) ⊓
    (V : Subgroup (AbstractFreeProduct A B))
  normal' := inferInstance
  quotient_mem' :=
    ProCGroups.FiniteGroupClass.Formation.quotient_inf_mem
      (C := C) (G := AbstractFreeProduct A B) hForm
      (U : Subgroup (AbstractFreeProduct A B))
      (V : Subgroup (AbstractFreeProduct A B)) U.quotient_mem V.quotient_mem
  inl_continuous' := by
    let N : Subgroup (AbstractFreeProduct A B) :=
      (U : Subgroup (AbstractFreeProduct A B)) ⊓
        (V : Subgroup (AbstractFreeProduct A B))
    let fN : A →* AbstractFreeProduct A B ⧸ N :=
      (QuotientGroup.mk' N).comp (Monoid.Coprod.inl : A →* AbstractFreeProduct A B)
    let fU : A →* AbstractFreeProduct A B ⧸ (U : Subgroup (AbstractFreeProduct A B)) :=
      (QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))).comp
        (Monoid.Coprod.inl : A →* AbstractFreeProduct A B)
    let fV : A →* AbstractFreeProduct A B ⧸ (V : Subgroup (AbstractFreeProduct A B)) :=
      (QuotientGroup.mk' (V : Subgroup (AbstractFreeProduct A B))).comp
        (Monoid.Coprod.inl : A →* AbstractFreeProduct A B)
    have hker :
        IsOpen (((fN.ker : Subgroup A) : Set A)) := by
      have hEq : ((fN.ker : Subgroup A) : Set A) =
          ((fU.ker : Subgroup A) : Set A) ∩ ((fV.ker : Subgroup A) : Set A) := by
        ext x
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
  QuotientGroup.eq_one_iff, Subgroup.mem_inf, Set.mem_inter_iff, N, fN, fU, fV]
      rw [hEq]
      exact (isOpen_ker_of_continuous_quotient_inl (C := C) (A := A) (B := B) U).inter
        (isOpen_ker_of_continuous_quotient_inl (C := C) (A := A) (B := B) V)
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸ N) := ⊥
    letI : DiscreteTopology (AbstractFreeProduct A B ⧸ N) := ⟨rfl⟩
    exact fN.continuous_of_isOpen_ker_to_discrete hker
  inr_continuous' := by
    let N : Subgroup (AbstractFreeProduct A B) :=
      (U : Subgroup (AbstractFreeProduct A B)) ⊓
        (V : Subgroup (AbstractFreeProduct A B))
    let fN : B →* AbstractFreeProduct A B ⧸ N :=
      (QuotientGroup.mk' N).comp (Monoid.Coprod.inr : B →* AbstractFreeProduct A B)
    let fU : B →* AbstractFreeProduct A B ⧸ (U : Subgroup (AbstractFreeProduct A B)) :=
      (QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))).comp
        (Monoid.Coprod.inr : B →* AbstractFreeProduct A B)
    let fV : B →* AbstractFreeProduct A B ⧸ (V : Subgroup (AbstractFreeProduct A B)) :=
      (QuotientGroup.mk' (V : Subgroup (AbstractFreeProduct A B))).comp
        (Monoid.Coprod.inr : B →* AbstractFreeProduct A B)
    have hker :
        IsOpen (((fN.ker : Subgroup B) : Set B)) := by
      have hEq : ((fN.ker : Subgroup B) : Set B) =
          ((fU.ker : Subgroup B) : Set B) ∩ ((fV.ker : Subgroup B) : Set B) := by
        ext x
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
  QuotientGroup.eq_one_iff, Subgroup.mem_inf, Set.mem_inter_iff, N, fN, fU, fV]
      rw [hEq]
      exact (isOpen_ker_of_continuous_quotient_inr (C := C) (A := A) (B := B) U).inter
        (isOpen_ker_of_continuous_quotient_inr (C := C) (A := A) (B := B) V)
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸ N) := ⊥
    letI : DiscreteTopology (AbstractFreeProduct A B ⧸ N) := ⟨rfl⟩
    exact fN.continuous_of_isOpen_ker_to_discrete hker

/-- Admissible quotients form a directed preorder under refinement. -/
theorem directed (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    Directed (α := AdmissibleQuotient C A B) (· ≤ ·) fun U => U := by
  intro U V
  refine ⟨inf (C := C) (A := A) (B := B) hForm U V, ?_, ?_⟩
  · show (((inf (C := C) (A := A) (B := B) hForm U V :
        AdmissibleQuotient C A B) : Subgroup (AbstractFreeProduct A B)) ≤
        (U : Subgroup (AbstractFreeProduct A B)))
    exact inf_le_left
  · show (((inf (C := C) (A := A) (B := B) hForm U V :
        AdmissibleQuotient C A B) : Subgroup (AbstractFreeProduct A B)) ≤
        (V : Subgroup (AbstractFreeProduct A B)))
    exact inf_le_right

section OfHom

variable {Q : Type u} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]

/-- The admissible quotient cut out by a homomorphism from the abstract free product to a finite
`C`-group, provided the two restrictions to the factors are continuous. -/
noncomputable def ofHom (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hQ : C Q) (φ : AbstractFreeProduct A B →* Q)
    (hφl : Continuous (φ.comp (Monoid.Coprod.inl : A →* AbstractFreeProduct A B)))
    (hφr : Continuous (φ.comp (Monoid.Coprod.inr : B →* AbstractFreeProduct A B))) :
    AdmissibleQuotient C A B where
  toSubgroup := φ.ker
  normal' := inferInstance
  quotient_mem' := by
    let e : AbstractFreeProduct A B ⧸ φ.ker ≃* φ.range :=
      QuotientGroup.quotientKerEquivRange φ
    let f : AbstractFreeProduct A B ⧸ φ.ker →* Q :=
      φ.range.subtype.comp e.toMonoidHom
    have hf : Function.Injective f := by
      intro x y hxy
      apply e.injective
      apply Subtype.val_injective
      exact hxy
    exact hHer.of_injective hQ f hf
  inl_continuous' := by
    let fN : A →* AbstractFreeProduct A B ⧸ φ.ker :=
      (QuotientGroup.mk' φ.ker).comp
        (Monoid.Coprod.inl : A →* AbstractFreeProduct A B)
    have hker : IsOpen ((fN.ker : Subgroup A) : Set A) := by
      have hEq : ((fN.ker : Subgroup A) : Set A) =
          (((φ.comp (Monoid.Coprod.inl :
            A →* AbstractFreeProduct A B)).ker : Subgroup A) : Set A) := by
        ext x
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
  QuotientGroup.eq_one_iff, fN]
      rw [hEq]
      simpa [MonoidHom.mem_ker] using (isOpen_discrete ({1} : Set Q)).preimage hφl
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸ φ.ker) := ⊥
    letI : DiscreteTopology (AbstractFreeProduct A B ⧸ φ.ker) := ⟨rfl⟩
    exact fN.continuous_of_isOpen_ker_to_discrete hker
  inr_continuous' := by
    let fN : B →* AbstractFreeProduct A B ⧸ φ.ker :=
      (QuotientGroup.mk' φ.ker).comp
        (Monoid.Coprod.inr : B →* AbstractFreeProduct A B)
    have hker : IsOpen ((fN.ker : Subgroup B) : Set B) := by
      have hEq : ((fN.ker : Subgroup B) : Set B) =
          (((φ.comp (Monoid.Coprod.inr :
            B →* AbstractFreeProduct A B)).ker : Subgroup B) : Set B) := by
        ext x
        simp only [SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.coe_comp, QuotientGroup.coe_mk', Function.comp_apply,
  QuotientGroup.eq_one_iff, fN]
      rw [hEq]
      simpa [MonoidHom.mem_ker] using (isOpen_discrete ({1} : Set Q)).preimage hφr
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸ φ.ker) := ⊥
    letI : DiscreteTopology (AbstractFreeProduct A B ⧸ φ.ker) := ⟨rfl⟩
    exact fN.continuous_of_isOpen_ker_to_discrete hker

/-- The admissible quotient induced by a target homomorphism has the expected kernel subgroup. -/
@[simp] theorem ofHom_toSubgroup (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hQ : C Q) (φ : AbstractFreeProduct A B →* Q)
    (hφl : Continuous (φ.comp (Monoid.Coprod.inl : A →* AbstractFreeProduct A B)))
    (hφr : Continuous (φ.comp (Monoid.Coprod.inr : B →* AbstractFreeProduct A B))) :
    ((ofHom (C := C) (A := A) (B := B) hHer hQ φ hφl hφr :
      AdmissibleQuotient C A B) : Subgroup (AbstractFreeProduct A B)) = φ.ker :=
  rfl

end OfHom

end AdmissibleQuotient

/-- The inverse system of admissible finite quotients of the abstract free product. -/
def admissibleQuotientSystem (C : ProCGroups.FiniteGroupClass.{u})
    (A B : Type u) [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] :
    ProCGroups.InverseSystems.InverseSystem (I := AdmissibleQuotient C A B) where
  X := fun U => AbstractFreeProduct A B ⧸ (U : Subgroup (AbstractFreeProduct A B))
  topologicalSpace := fun _ => ⊥
  map := fun {U V} hUV =>
    AdmissibleQuotient.map (C := C) (A := A) (B := B)
      (U := U) (V := V)
      (show (V : Subgroup (AbstractFreeProduct A B)) ≤
        (U : Subgroup (AbstractFreeProduct A B)) from hUV)
  continuous_map := by
    intro U V hUV
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸
        (V : Subgroup (AbstractFreeProduct A B))) := ⊥
    letI : DiscreteTopology (AbstractFreeProduct A B ⧸
        (V : Subgroup (AbstractFreeProduct A B))) := ⟨rfl⟩
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸
        (U : Subgroup (AbstractFreeProduct A B))) := ⊥
    change Continuous (AdmissibleQuotient.map (C := C) (A := A) (B := B)
      (U := U) (V := V)
      (show (V : Subgroup (AbstractFreeProduct A B)) ≤
        (U : Subgroup (AbstractFreeProduct A B)) from hUV))
    exact continuous_of_discreteTopology
  map_id := by
    intro U
    ext x
    rcases QuotientGroup.mk'_surjective (U : Subgroup (AbstractFreeProduct A B)) x with
      ⟨g, rfl⟩
    rfl
  map_comp := by
    intro U V W hUV hVW
    ext x
    rcases QuotientGroup.mk'_surjective (W : Subgroup (AbstractFreeProduct A B)) x with
      ⟨g, rfl⟩
    rfl

/-- Each admissible quotient stage carries its quotient group structure. -/
instance instGroupAdmissibleQuotientSystemX
    (U : AdmissibleQuotient C A B) :
    Group ((admissibleQuotientSystem C A B).X U) := by
  dsimp [admissibleQuotientSystem]
  infer_instance

/-- Each admissible quotient stage carries the discrete topology. -/
instance instDiscreteTopologyAdmissibleQuotientSystemX
    (U : AdmissibleQuotient C A B) :
    DiscreteTopology ((admissibleQuotientSystem C A B).X U) := by
  exact ⟨rfl⟩

/-- Each admissible quotient stage is a topological group with the discrete topology. -/
instance instIsTopologicalGroupAdmissibleQuotientSystemX
    (U : AdmissibleQuotient C A B) :
    IsTopologicalGroup ((admissibleQuotientSystem C A B).X U) := by
  infer_instance

/-- The admissible quotient system is a group-valued inverse system. -/
instance instIsGroupSystemAdmissibleQuotientSystem :
    ProCGroups.InverseSystems.IsGroupSystem (admissibleQuotientSystem C A B) where
  map_one := by
    intro U V hUV
    rfl
  map_mul := by
    intro U V hUV x y
    exact (AdmissibleQuotient.map (C := C) (A := A) (B := B)
      (U := U) (V := V) hUV).map_mul x y
  map_inv := by
    intro U V hUV x
    exact (AdmissibleQuotient.map (C := C) (A := A) (B := B)
      (U := U) (V := V) hUV).map_inv x

/-- The concrete binary free pro-`C` product model. -/
abbrev freeProCProduct (C : ProCGroups.FiniteGroupClass.{u})
    (A B : Type u) [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] :=
  (admissibleQuotientSystem C A B).inverseLimit

/-- The concrete free pro-`C` product inherits the inverse-limit group structure. -/
instance instGroupFreeProCProduct : Group (freeProCProduct C A B) := by
  dsimp [freeProCProduct]
  infer_instance

/-- The concrete free pro-`C` product inherits the inverse-limit topological group structure. -/
instance instIsTopologicalGroupFreeProCProduct :
    IsTopologicalGroup (freeProCProduct C A B) := by
  dsimp [freeProCProduct]
  infer_instance

/-- The canonical projection from the concrete free pro-`C` product to an admissible quotient,
bundled as a homomorphism. -/
def freeProCProductπHom (U : AdmissibleQuotient C A B) :
    freeProCProduct C A B →* AbstractFreeProduct A B ⧸
      (U : Subgroup (AbstractFreeProduct A B)) where
  toFun := (admissibleQuotientSystem C A B).projection U
  map_one' := rfl
  map_mul' := by
    intro x y
    rfl

/-- The canonical projection homomorphism from the concrete free pro-`C` product evaluates as the inverse-limit projection. -/
@[simp] theorem freeProCProductπHom_apply
    (U : AdmissibleQuotient C A B) (x : freeProCProduct C A B) :
    freeProCProductπHom (C := C) (A := A) (B := B) U x =
      (admissibleQuotientSystem C A B).projection U x :=
  rfl

private def completionMapFamily (C : ProCGroups.FiniteGroupClass.{u})
    (A B : Type u) [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] :
    ∀ U : AdmissibleQuotient C A B,
      AbstractFreeProduct A B → (admissibleQuotientSystem C A B).X U :=
  fun U g => QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B)) g

private theorem completionMapFamily_compatible :
    (admissibleQuotientSystem C A B).CompatibleMaps
      (completionMapFamily C A B) := by
  intro U V hUV
  funext g
  rfl

/-- The canonical abstract map from the free product to its admissible pro-`C` completion. -/
noncomputable def completionMap :
    AbstractFreeProduct A B →* freeProCProduct C A B where
  toFun g :=
    ⟨fun U => QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B)) g, by
      intro U V hUV
      rfl⟩
  map_one' := by
    apply (admissibleQuotientSystem C A B).ext
    intro U
    change QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
      (1 : AbstractFreeProduct A B) = 1
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_one]
  map_mul' := by
    intro x y
    apply (admissibleQuotientSystem C A B).ext
    intro U
    change QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B)) (x * y) =
      QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B)) x *
        QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B)) y
    simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul]

/-- The completion map followed by a finite admissible quotient projection is the quotient map. -/
@[simp] theorem π_completionMap (U : AdmissibleQuotient C A B)
    (g : AbstractFreeProduct A B) :
    (admissibleQuotientSystem C A B).projection U (completionMap (C := C) (A := A) (B := B) g) =
      QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B)) g :=
  rfl

private theorem denseRange_completionMap_of_formation
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    DenseRange (completionMap (C := C) (A := A) (B := B)) := by
  let S := admissibleQuotientSystem C A B
  letI : Nonempty (AdmissibleQuotient C A B) :=
    ⟨AdmissibleQuotient.top (C := C) (A := A) (B := B) hForm⟩
  letI : TopologicalSpace (AbstractFreeProduct A B) := ⊥
  simpa [completionMap, S] using
    S.denseRange_lift
      (completionMapFamily C A B)
      (completionMapFamily_compatible (C := C) (A := A) (B := B))
      (fun U => QuotientGroup.mk'_surjective (U : Subgroup (AbstractFreeProduct A B)))
      (AdmissibleQuotient.directed (C := C) (A := A) (B := B) hForm)

private def inlFamily (C : ProCGroups.FiniteGroupClass.{u})
    (A B : Type u) [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] :
    ∀ U : AdmissibleQuotient C A B,
      A → (admissibleQuotientSystem C A B).X U :=
  fun U a => QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
    ((Monoid.Coprod.inl : A →* AbstractFreeProduct A B) a)

private theorem inlFamily_compatible :
    (admissibleQuotientSystem C A B).CompatibleMaps
      (inlFamily C A B) := by
  intro U V hUV
  funext a
  rfl

private def inrFamily (C : ProCGroups.FiniteGroupClass.{u})
    (A B : Type u) [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] :
    ∀ U : AdmissibleQuotient C A B,
      B → (admissibleQuotientSystem C A B).X U :=
  fun U b => QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
    ((Monoid.Coprod.inr : B →* AbstractFreeProduct A B) b)

private theorem inrFamily_compatible :
    (admissibleQuotientSystem C A B).CompatibleMaps
      (inrFamily C A B) := by
  intro U V hUV
  funext b
  rfl

section TargetQuotients

variable {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- The abstract free-product homomorphism induced by a pair of maps to an open normal quotient of a
target group. -/
noncomputable def targetQuotientHom
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K) :
    AbstractFreeProduct A B →* K ⧸ (U.1 : Subgroup K) :=
  Monoid.Coprod.lift
    ((ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U).comp φ₁).toMonoidHom
    ((ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U).comp φ₂).toMonoidHom

omit [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup K] in
/-- The target quotient homomorphism agrees with the left input homomorphism on the left factor. -/
@[simp] theorem targetQuotientHom_comp_inl
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K) :
    (targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ U).comp
        (Monoid.Coprod.inl : A →* AbstractFreeProduct A B) =
      ((ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U).comp
        φ₁).toMonoidHom :=
  Monoid.Coprod.lift_comp_inl _ _

omit [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup K] in
/-- The target quotient homomorphism agrees with the right input homomorphism on the right factor. -/
@[simp] theorem targetQuotientHom_comp_inr
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K) :
    (targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ U).comp
        (Monoid.Coprod.inr : B →* AbstractFreeProduct A B) =
      ((ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U).comp
        φ₂).toMonoidHom :=
  Monoid.Coprod.lift_comp_inr _ _

omit [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup K] in
/-- Target quotient homomorphisms are compatible with admissible-quotient transition maps. -/
theorem targetQuotientHom_transition
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    {U V : ProCGroups.ProC.OpenNormalSubgroupInClass C K}
    (hUV : (V.1 : Subgroup K) ≤ (U.1 : Subgroup K)) :
    (ProCGroups.ProC.OpenNormalSubgroupInClass.map (C := C) (G := K) hUV).comp
        (targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ V) =
      targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ U := by
  apply Monoid.Coprod.hom_ext
  · ext a
    rfl
  · ext b
    rfl

/-- The admissible quotient of the abstract free product induced by an open normal quotient of a
pro-`C` target. Heredity is used because the image in the target quotient may be a proper subgroup. -/
noncomputable def targetAdmissible
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K) :
    AdmissibleQuotient C A B := by
  letI : DiscreteTopology (K ⧸ (U.1 : Subgroup K)) :=
    QuotientGroup.discreteTopology
      (openNormalSubgroup_isOpen (G := K) (U.1 : OpenNormalSubgroup K))
  refine AdmissibleQuotient.ofHom (C := C) (A := A) (B := B)
    hHer U.2 (targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ U) ?_ ?_
  · rw [targetQuotientHom_comp_inl]
    exact ((ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U).comp
      φ₁).continuous_toFun
  · rw [targetQuotientHom_comp_inr]
    exact ((ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U).comp
      φ₂).continuous_toFun

/-- The target admissible quotient has the expected defining subgroup. -/
theorem targetAdmissible_toSubgroup
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K) :
    ((targetAdmissible (C := C) (A := A) (B := B) hHer φ₁ φ₂ U :
      AdmissibleQuotient C A B) : Subgroup (AbstractFreeProduct A B)) =
      (targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ U).ker := by
  dsimp [targetAdmissible]

/-- Map from the admissible quotient induced by a target quotient to that target quotient. -/
noncomputable def targetAdmissibleQuotientMap
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K) :
    AbstractFreeProduct A B ⧸
        (targetAdmissible (C := C) (A := A) (B := B) hHer φ₁ φ₂ U :
          Subgroup (AbstractFreeProduct A B)) →*
      K ⧸ (U.1 : Subgroup K) :=
  QuotientGroup.lift
    (targetAdmissible (C := C) (A := A) (B := B) hHer φ₁ φ₂ U :
      Subgroup (AbstractFreeProduct A B))
    (targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ U)
    (by
      intro g hg
      have hg' :
          g ∈ (targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ U).ker := by
        simpa [targetAdmissible_toSubgroup (C := C) (A := A) (B := B)
          hHer φ₁ φ₂ U] using hg
      exact hg')

/-- The target admissible quotient map evaluates on representatives as expected. -/
@[simp] theorem targetAdmissibleQuotientMap_mk
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K)
    (g : AbstractFreeProduct A B) :
    targetAdmissibleQuotientMap (C := C) (A := A) (B := B) hHer φ₁ φ₂ U
      (QuotientGroup.mk'
        (targetAdmissible (C := C) (A := A) (B := B) hHer φ₁ φ₂ U :
          Subgroup (AbstractFreeProduct A B)) g) =
      targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ U g :=
  rfl

/-- Coordinate map from the concrete free pro-`C` product to one finite quotient of a pro-`C`
target. -/
noncomputable def targetCoordinate
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K) :
    freeProCProduct C A B →ₜ* K ⧸ (U.1 : Subgroup K) where
  toMonoidHom :=
    (targetAdmissibleQuotientMap (C := C) (A := A) (B := B) hHer φ₁ φ₂ U).comp
      (freeProCProductπHom (C := C) (A := A) (B := B)
        (targetAdmissible (C := C) (A := A) (B := B) hHer φ₁ φ₂ U))
  continuous_toFun := by
    let S := admissibleQuotientSystem C A B
    let N := targetAdmissible (C := C) (A := A) (B := B) hHer φ₁ φ₂ U
    letI : TopologicalSpace (AbstractFreeProduct A B ⧸
        (N : Subgroup (AbstractFreeProduct A B))) := ⊥
    letI : DiscreteTopology (AbstractFreeProduct A B ⧸
        (N : Subgroup (AbstractFreeProduct A B))) := ⟨rfl⟩
    letI : DiscreteTopology (S.X N) :=
      instDiscreteTopologyAdmissibleQuotientSystemX (C := C) (A := A) (B := B) N
    have hq : Continuous
        (targetAdmissibleQuotientMap (C := C) (A := A) (B := B) hHer φ₁ φ₂ U) :=
      continuous_of_discreteTopology
    exact hq.comp (S.continuous_projection N)

/-- The target coordinate map agrees with the completion map after projection to a finite quotient. -/
theorem targetCoordinate_completionMap
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K)
    (g : AbstractFreeProduct A B) :
    targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂ U
      (completionMap (C := C) (A := A) (B := B) g) =
      targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ U g := by
  change targetAdmissibleQuotientMap (C := C) (A := A) (B := B) hHer φ₁ φ₂ U
      (QuotientGroup.mk'
        (targetAdmissible (C := C) (A := A) (B := B) hHer φ₁ φ₂ U :
          Subgroup (AbstractFreeProduct A B)) g) =
    targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ U g
  rw [targetAdmissibleQuotientMap_mk]

/-- The family of target-coordinate maps into the finite quotients of a pro-`C` target. -/
noncomputable def targetCoordinateFamily
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K) :
    ∀ U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C K),
      freeProCProduct C A B →
        (ProCGroups.ProC.openNormalSubgroupInClassSystem C K).X U :=
  fun U x => targetCoordinate (C := C) (A := A) (B := B)
    hHer φ₁ φ₂ (OrderDual.ofDual U) x

/-- The target coordinate maps form a compatible family over admissible quotients. -/
theorem targetCoordinateFamily_compatible
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K) :
    (ProCGroups.ProC.openNormalSubgroupInClassSystem C K).CompatibleMaps
      (targetCoordinateFamily (C := C) (A := A) (B := B) hHer φ₁ φ₂) := by
  let T := ProCGroups.ProC.openNormalSubgroupInClassSystem C K
  intro U V hUV
  funext x
  letI : DiscreteTopology (T.X U) := by
    dsimp [T, ProCGroups.ProC.openNormalSubgroupInClassSystem]
    exact QuotientGroup.discreteTopology
      (openNormalSubgroup_isOpen (G := K)
        ((OrderDual.ofDual U).1 : OpenNormalSubgroup K))
  letI : T2Space (T.X U) := by infer_instance
  have hEqFun :
      (T.map hUV ∘ targetCoordinateFamily (C := C) (A := A) (B := B) hHer φ₁ φ₂ V) =
        targetCoordinateFamily (C := C) (A := A) (B := B) hHer φ₁ φ₂ U := by
    apply Continuous.ext_on
      (s := Set.range (completionMap (C := C) (A := A) (B := B)))
      (denseRange_completionMap_of_formation (C := C) (A := A) (B := B) hForm)
    · exact (T.continuous_map hUV).comp
        (targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂
          (OrderDual.ofDual V)).continuous_toFun
    · exact (targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂
        (OrderDual.ofDual U)).continuous_toFun
    · rintro _ ⟨g, rfl⟩
      change T.map hUV
          (targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂
            (OrderDual.ofDual V) g) =
        targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂
          (OrderDual.ofDual U) g
      exact congrArg (fun f : AbstractFreeProduct A B →* T.X U => f g)
        (targetQuotientHom_transition (C := C) (A := A) (B := B)
          φ₁ φ₂ (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
  exact congrFun hEqFun x

/-- The map from the concrete free pro-`C` product to the canonical inverse-limit presentation of a
pro-`C` target induced by maps on the two factors. -/
noncomputable def targetInverseLimitMap
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K) :
    freeProCProduct C A B →ₜ*
      (ProCGroups.ProC.openNormalSubgroupInClassSystem C K).inverseLimit where
  toFun :=
    (ProCGroups.ProC.openNormalSubgroupInClassSystem C K).inverseLimitLift
      (targetCoordinateFamily (C := C) (A := A) (B := B) hHer φ₁ φ₂)
      (targetCoordinateFamily_compatible (C := C) (A := A) (B := B)
        hForm hHer φ₁ φ₂)
  map_one' := by
    apply (ProCGroups.ProC.openNormalSubgroupInClassSystem C K).ext
    intro U
    change targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂
        (OrderDual.ofDual U) 1 = 1
    simp only [map_one]
  map_mul' := by
    intro x y
    apply (ProCGroups.ProC.openNormalSubgroupInClassSystem C K).ext
    intro U
    change targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂
        (OrderDual.ofDual U) (x * y) =
      targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂
        (OrderDual.ofDual U) x *
      targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂
        (OrderDual.ofDual U) y
    simp only [map_mul]
  continuous_toFun := by
    let T := ProCGroups.ProC.openNormalSubgroupInClassSystem C K
    exact T.continuous_inverseLimitLift
      (targetCoordinateFamily (C := C) (A := A) (B := B) hHer φ₁ φ₂)
      (fun U => (targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂
        (OrderDual.ofDual U)).continuous_toFun)
      (targetCoordinateFamily_compatible (C := C) (A := A) (B := B)
        hForm hHer φ₁ φ₂)

theorem openNormalSubgroupInClassMulEquivInverseLimit_π
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hK : ProCGroups.ProC.IsProCGroup C K)
    (U : OrderDual (ProCGroups.ProC.OpenNormalSubgroupInClass C K)) (x : K) :
    (ProCGroups.ProC.openNormalSubgroupInClassSystem C K).projection U
      ((ProCGroups.ProC.IsProCGroup.openNormalSubgroupInClassMulEquivInverseLimit
        (C := C) (G := K) hForm hK) x) =
      ProCGroups.ProC.openNormalSubgroupInClassProj (C := C) (G := K) U x := by
  rfl

/-- The continuous homomorphism to a pro-`C` target induced by maps from the two factors. -/
noncomputable def liftToTarget
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hK : ProCGroups.ProC.IsProCGroup C K)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K) :
    freeProCProduct C A B →ₜ* K :=
  (ContinuousMulEquiv.toContinuousMonoidHom
    (ProCGroups.ProC.IsProCGroup.openNormalSubgroupInClassMulEquivInverseLimit
      (C := C) (G := K) hForm hK).symm).comp
    (targetInverseLimitMap (C := C) (A := A) (B := B) hForm hHer φ₁ φ₂)

/-- The lift to a target has the prescribed finite quotient coordinates. -/
theorem quotientProj_liftToTarget
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hK : ProCGroups.ProC.IsProCGroup C K)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K) :
    (ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U).comp
        (liftToTarget (C := C) (A := A) (B := B) hForm hHer hK φ₁ φ₂) =
      targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂ U := by
  ext x
  let T := ProCGroups.ProC.openNormalSubgroupInClassSystem C K
  let e :=
    ProCGroups.ProC.IsProCGroup.openNormalSubgroupInClassMulEquivInverseLimit
      (C := C) (G := K) hForm hK
  let θ := targetInverseLimitMap (C := C) (A := A) (B := B) hForm hHer φ₁ φ₂
  have hCoord :
      T.projection (OrderDual.toDual U) (e (e.symm (θ x))) =
        T.projection (OrderDual.toDual U) (θ x) := by
    exact congrArg (fun z : T.inverseLimit => T.projection (OrderDual.toDual U) z)
      (e.apply_symm_apply (θ x))
  rw [openNormalSubgroupInClassMulEquivInverseLimit_π
    (C := C) (K := K) hForm hK (OrderDual.toDual U)] at hCoord
  simpa [liftToTarget, θ, targetInverseLimitMap, targetCoordinateFamily,
    ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj,
    ProCGroups.ProC.openNormalSubgroupInClassProj, e] using hCoord

end TargetQuotients

/-- The left factor map into the concrete free pro-`C` product. -/
noncomputable def inl : A →ₜ* freeProCProduct C A B where
  toFun :=
    (admissibleQuotientSystem C A B).inverseLimitLift
      (inlFamily C A B)
      (inlFamily_compatible (C := C) (A := A) (B := B))
  map_one' := by
    apply (admissibleQuotientSystem C A B).ext
    intro U
    change QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
      ((Monoid.Coprod.inl : A →* AbstractFreeProduct A B) 1) = 1
    simp only [map_one]
  map_mul' := by
    intro x y
    apply (admissibleQuotientSystem C A B).ext
    intro U
    change QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
        ((Monoid.Coprod.inl : A →* AbstractFreeProduct A B) (x * y)) =
      QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
        ((Monoid.Coprod.inl : A →* AbstractFreeProduct A B) x) *
      QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
        ((Monoid.Coprod.inl : A →* AbstractFreeProduct A B) y)
    simp only [map_mul, QuotientGroup.mk'_apply]
  continuous_toFun := by
    let S := admissibleQuotientSystem C A B
    exact S.continuous_inverseLimitLift
      (inlFamily C A B)
      (fun U => U.inl_continuous)
      (inlFamily_compatible (C := C) (A := A) (B := B))

/-- The right factor map into the concrete free pro-`C` product. -/
noncomputable def inr : B →ₜ* freeProCProduct C A B where
  toFun :=
    (admissibleQuotientSystem C A B).inverseLimitLift
      (inrFamily C A B)
      (inrFamily_compatible (C := C) (A := A) (B := B))
  map_one' := by
    apply (admissibleQuotientSystem C A B).ext
    intro U
    change QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
      ((Monoid.Coprod.inr : B →* AbstractFreeProduct A B) 1) = 1
    simp only [map_one]
  map_mul' := by
    intro x y
    apply (admissibleQuotientSystem C A B).ext
    intro U
    change QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
        ((Monoid.Coprod.inr : B →* AbstractFreeProduct A B) (x * y)) =
      QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
        ((Monoid.Coprod.inr : B →* AbstractFreeProduct A B) x) *
      QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
        ((Monoid.Coprod.inr : B →* AbstractFreeProduct A B) y)
    simp only [map_mul, QuotientGroup.mk'_apply]
  continuous_toFun := by
    let S := admissibleQuotientSystem C A B
    exact S.continuous_inverseLimitLift
      (inrFamily C A B)
      (fun U => U.inr_continuous)
      (inrFamily_compatible (C := C) (A := A) (B := B))

/-- The finite projection of the left inclusion is the left inclusion into the admissible quotient. -/
@[simp] theorem π_inl (U : AdmissibleQuotient C A B) (a : A) :
    (admissibleQuotientSystem C A B).projection U (inl (C := C) (A := A) (B := B) a) =
      QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
        ((Monoid.Coprod.inl : A →* AbstractFreeProduct A B) a) :=
  by
    change (admissibleQuotientSystem C A B).projection U
        ((admissibleQuotientSystem C A B).inverseLimitLift
          (inlFamily C A B)
          (inlFamily_compatible (C := C) (A := A) (B := B)) a) =
      QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
        ((Monoid.Coprod.inl : A →* AbstractFreeProduct A B) a)
    rw [(admissibleQuotientSystem C A B).projection_inverseLimitLift_apply]
    rfl

/-- The finite projection of the right inclusion is the right inclusion into the admissible quotient. -/
@[simp] theorem π_inr (U : AdmissibleQuotient C A B) (b : B) :
    (admissibleQuotientSystem C A B).projection U (inr (C := C) (A := A) (B := B) b) =
      QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
        ((Monoid.Coprod.inr : B →* AbstractFreeProduct A B) b) :=
  by
    change (admissibleQuotientSystem C A B).projection U
        ((admissibleQuotientSystem C A B).inverseLimitLift
          (inrFamily C A B)
          (inrFamily_compatible (C := C) (A := A) (B := B)) b) =
      QuotientGroup.mk' (U : Subgroup (AbstractFreeProduct A B))
        ((Monoid.Coprod.inr : B →* AbstractFreeProduct A B) b)
    rw [(admissibleQuotientSystem C A B).projection_inverseLimitLift_apply]
    rfl

/-- The completion map composed with the left inclusion is the left inclusion into the free pro-`C` product. -/
@[simp] theorem completionMap_comp_inl :
    (completionMap (C := C) (A := A) (B := B)).comp
        (Monoid.Coprod.inl : A →* AbstractFreeProduct A B) =
      (inl (C := C) (A := A) (B := B)).toMonoidHom := by
  ext a U
  change (admissibleQuotientSystem C A B).projection U
      (completionMap (C := C) (A := A) (B := B)
        ((Monoid.Coprod.inl : A →* AbstractFreeProduct A B) a)) =
    (admissibleQuotientSystem C A B).projection U
      (inl (C := C) (A := A) (B := B) a)
  rw [π_completionMap, π_inl]

/-- The completion map composed with the right inclusion is the right inclusion into the free pro-`C` product. -/
@[simp] theorem completionMap_comp_inr :
    (completionMap (C := C) (A := A) (B := B)).comp
        (Monoid.Coprod.inr : B →* AbstractFreeProduct A B) =
      (inr (C := C) (A := A) (B := B)).toMonoidHom := by
  ext b U
  change (admissibleQuotientSystem C A B).projection U
      (completionMap (C := C) (A := A) (B := B)
        ((Monoid.Coprod.inr : B →* AbstractFreeProduct A B) b)) =
    (admissibleQuotientSystem C A B).projection U
      (inr (C := C) (A := A) (B := B) b)
  rw [π_completionMap, π_inr]

section TargetCoordinateFactorMaps

variable {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- The target coordinate map sends the left inclusion to the prescribed left homomorphism. -/
@[simp] theorem targetCoordinate_inl
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K) (a : A) :
    targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂ U
      (inl (C := C) (A := A) (B := B) a) =
      ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U (φ₁ a) := by
  simpa [completionMap_comp_inl, targetQuotientHom_comp_inl,
    ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj] using
    targetCoordinate_completionMap (C := C) (A := A) (B := B)
      hHer φ₁ φ₂ U ((Monoid.Coprod.inl : A →* AbstractFreeProduct A B) a)

/-- The target coordinate map sends the right inclusion to the prescribed right homomorphism. -/
@[simp] theorem targetCoordinate_inr
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K) (b : B) :
    targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂ U
      (inr (C := C) (A := A) (B := B) b) =
      ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U (φ₂ b) := by
  simpa [completionMap_comp_inr, targetQuotientHom_comp_inr,
    ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj] using
    targetCoordinate_completionMap (C := C) (A := A) (B := B)
      hHer φ₁ φ₂ U ((Monoid.Coprod.inr : B →* AbstractFreeProduct A B) b)

/-- The constructed lift has the prescribed left composite. -/
theorem liftToTarget_comp_inl
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hK : ProCGroups.ProC.IsProCGroup C K)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K) :
    (liftToTarget (C := C) (A := A) (B := B) hForm hHer hK φ₁ φ₂).comp
        (inl (C := C) (A := A) (B := B)) = φ₁ := by
  apply ProCGroups.ProC.continuousMonoidHom_ext_openNormalQuotients hK.1
  intro U
  let Uc : ProCGroups.ProC.OpenNormalSubgroupInClass C K :=
    ⟨U, ProCGroups.ProC.IsProCGroup.quotient_mem hForm hK U⟩
  ext a
  have hq := congrArg (fun f : freeProCProduct C A B →ₜ* K ⧸ (U : Subgroup K) =>
      f (inl (C := C) (A := A) (B := B) a))
    (quotientProj_liftToTarget (C := C) (A := A) (B := B)
      hForm hHer hK φ₁ φ₂ Uc)
  simpa [Uc, ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj] using hq

/-- The constructed lift has the prescribed right composite. -/
theorem liftToTarget_comp_inr
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (hK : ProCGroups.ProC.IsProCGroup C K)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K) :
    (liftToTarget (C := C) (A := A) (B := B) hForm hHer hK φ₁ φ₂).comp
        (inr (C := C) (A := A) (B := B)) = φ₂ := by
  apply ProCGroups.ProC.continuousMonoidHom_ext_openNormalQuotients hK.1
  intro U
  let Uc : ProCGroups.ProC.OpenNormalSubgroupInClass C K :=
    ⟨U, ProCGroups.ProC.IsProCGroup.quotient_mem hForm hK U⟩
  ext b
  have hq := congrArg (fun f : freeProCProduct C A B →ₜ* K ⧸ (U : Subgroup K) =>
      f (inr (C := C) (A := A) (B := B) b))
    (quotientProj_liftToTarget (C := C) (A := A) (B := B)
      hForm hHer hK φ₁ φ₂ Uc)
  simpa [Uc, ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj] using hq

/-- Equality after all quotient projections follows from equality of the corresponding target coordinates. -/
theorem quotientProj_comp_eq_targetCoordinate_of_comp
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ₁ : A →ₜ* K) (φ₂ : B →ₜ* K)
    (Ψ : freeProCProduct C A B →ₜ* K)
    (hΨ₁ : Ψ.comp (inl (C := C) (A := A) (B := B)) = φ₁)
    (hΨ₂ : Ψ.comp (inr (C := C) (A := A) (B := B)) = φ₂)
    (U : ProCGroups.ProC.OpenNormalSubgroupInClass C K) :
    (ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U).comp Ψ =
      targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂ U := by
  let qU := ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj (C := C) U
  letI : DiscreteTopology (K ⧸ (U.1 : Subgroup K)) :=
    QuotientGroup.discreteTopology
      (openNormalSubgroup_isOpen (G := K) (U.1 : OpenNormalSubgroup K))
  letI : T2Space (K ⧸ (U.1 : Subgroup K)) := by infer_instance
  ext x
  have hfun :
      ((qU.comp Ψ : freeProCProduct C A B →ₜ* K ⧸ (U.1 : Subgroup K)) :
          freeProCProduct C A B → K ⧸ (U.1 : Subgroup K)) =
        targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂ U := by
    apply Continuous.ext_on
      (s := Set.range (completionMap (C := C) (A := A) (B := B)))
      (denseRange_completionMap_of_formation (C := C) (A := A) (B := B) hForm)
    · exact (qU.comp Ψ).continuous_toFun
    · exact (targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂ U).continuous_toFun
    · rintro _ ⟨g, rfl⟩
      have hhom :
          ((qU.comp Ψ).toMonoidHom.comp
              (completionMap (C := C) (A := A) (B := B))) =
            targetQuotientHom (C := C) (A := A) (B := B) φ₁ φ₂ U := by
        apply Monoid.Coprod.hom_ext
        · ext a
          have ha := congrArg (fun f : A →ₜ* K => qU (f a)) hΨ₁
          simpa [qU] using ha
        · ext b
          have hb := congrArg (fun f : B →ₜ* K => qU (f b)) hΨ₂
          simpa [qU] using hb
      simpa using congrArg (fun f : AbstractFreeProduct A B →*
          K ⧸ (U.1 : Subgroup K) => f g) hhom
  exact congrFun hfun x

end TargetCoordinateFactorMaps

/-- The completion map into the concrete free pro-`C` product has dense range. -/
theorem denseRange_completionMap
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    DenseRange (completionMap (C := C) (A := A) (B := B)) := by
  let S := admissibleQuotientSystem C A B
  letI : Nonempty (AdmissibleQuotient C A B) :=
    ⟨AdmissibleQuotient.top (C := C) (A := A) (B := B) hForm⟩
  letI : TopologicalSpace (AbstractFreeProduct A B) := ⊥
  simpa [completionMap, S] using
    S.denseRange_lift
      (completionMapFamily C A B)
      (completionMapFamily_compatible (C := C) (A := A) (B := B))
      (fun U => QuotientGroup.mk'_surjective (U : Subgroup (AbstractFreeProduct A B)))
      (AdmissibleQuotient.directed (C := C) (A := A) (B := B) hForm)

/-- The concrete free product model is pro-`C`. -/
theorem isProCGroup
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    ProCGroups.ProC.IsProCGroup C (freeProCProduct C A B) := by
  let S := admissibleQuotientSystem C A B
  letI : Nonempty (AdmissibleQuotient C A B) :=
    ⟨AdmissibleQuotient.top (C := C) (A := A) (B := B) hForm⟩
  have hX : ∀ U : AdmissibleQuotient C A B, ProCGroups.ProC.IsProCGroup C (S.X U) := by
    intro U
    letI : Finite (S.X U) := hForm.finiteOnly U.quotient_mem
    letI : DiscreteTopology (S.X U) :=
      instDiscreteTopologyAdmissibleQuotientSystemX (C := C) (A := A) (B := B) U
    exact ProCGroups.ProC.IsProCGroup.of_finite_discrete
      (C := C) (G := S.X U) hForm.quotientClosed U.quotient_mem
  simpa [freeProCProduct, S] using
    ProCGroups.ProC.inverseLimit
      (C := C) (S := S) hForm.isomClosed
      hForm.quotientClosed
      (AdmissibleQuotient.directed (C := C) (A := A) (B := B) hForm)
      hX

/-- The concrete inverse-limit model satisfies the binary free pro-`C` product universal property
for hereditary formations. -/
theorem isFreeProCProduct
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C) :
    IsFreeProCProduct
      (ProC := ProCGroups.ProC.finiteGroupClassProCPredicate C)
      (inl (C := C) (A := A) (B := B))
      (inr (C := C) (A := A) (B := B)) := by
  refine ⟨?_, ?_⟩
  · exact isProCGroup (C := C) (A := A) (B := B) hForm
  · intro K _ _ _ hK φ₁ φ₂
    have hK' : ProCGroups.ProC.IsProCGroup C K := by
      simpa [ProCGroups.ProC.finiteGroupClassProCPredicate_holds_iff] using hK
    let Φ := liftToTarget (C := C) (A := A) (B := B) hForm hHer hK' φ₁ φ₂
    refine ⟨Φ, ?_, ?_⟩
    · exact ⟨liftToTarget_comp_inl (C := C) (A := A) (B := B)
          hForm hHer hK' φ₁ φ₂,
        liftToTarget_comp_inr (C := C) (A := A) (B := B)
          hForm hHer hK' φ₁ φ₂⟩
    · intro Ψ hΨ
      apply ProCGroups.ProC.continuousMonoidHom_ext_openNormalQuotients hK'.1
      intro U
      let Uc : ProCGroups.ProC.OpenNormalSubgroupInClass C K :=
        ⟨U, ProCGroups.ProC.IsProCGroup.quotient_mem hForm hK' U⟩
      calc
        (ProCGroups.ProC.OpenNormalSubgroup.quotientProj U).comp Ψ =
            targetCoordinate (C := C) (A := A) (B := B) hHer φ₁ φ₂ Uc := by
              simpa [Uc, ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj] using
                quotientProj_comp_eq_targetCoordinate_of_comp
                  (C := C) (A := A) (B := B) hForm hHer φ₁ φ₂ Ψ hΨ.1 hΨ.2 Uc
        _ = (ProCGroups.ProC.OpenNormalSubgroup.quotientProj U).comp Φ := by
              symm
              simpa [Uc, ProCGroups.ProC.OpenNormalSubgroupInClass.quotientProj, Φ] using
                quotientProj_liftToTarget
                  (C := C) (A := A) (B := B) hForm hHer hK' φ₁ φ₂ Uc

end Concrete

end ProCGroups.FreeProducts
