import FoxDifferential.Completed.Continuous.Topology
import ProCGroups.ProC.Kernels

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Completed/Continuous/TopologicalGeneration.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Continuous crossed differentials

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

noncomputable section

open scoped BigOperators
open ProCGroups.Generation
open ProCGroups.ProC

universe u v

namespace IsCrossedDifferential

variable {R G A : Type*} [Semiring R] [Group G] [AddCommGroup A] [Module R A]
variable {coeff : G →* R} {delta epsilon : G → A}

variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [TopologicalSpace A] [T2Space A]

/-- Continuous crossed differentials with the same coefficients are determined by a topological
generating set. -/
theorem eq_of_continuous_of_topologicallyGenerates
    (hdelta : IsCrossedDifferential coeff delta)
    (hepsilon : IsCrossedDifferential coeff epsilon)
    (hdelta_continuous : Continuous delta) (hepsilon_continuous : Continuous epsilon)
    {s : Set G} (hsgen : TopologicallyGenerates (G := G) s)
    (hs : Set.EqOn delta epsilon s) :
    delta = epsilon := by
  let K : Subgroup G :=
    { carrier := {g | delta g = epsilon g}
      one_mem' := by
        change delta 1 = epsilon 1
        rw [hdelta.one, hepsilon.one]
      mul_mem' := by
        intro a b ha hb
        change delta (a * b) = epsilon (a * b)
        rw [hdelta.mul a b, hepsilon.mul a b, ha, hb]
      inv_mem' := by
        intro a ha
        change delta a⁻¹ = epsilon a⁻¹
        rw [hdelta.inv a, hepsilon.inv a, ha] }
  have hKclosed : IsClosed ((K : Subgroup G) : Set G) := by
    change IsClosed {g | delta g = epsilon g}
    exact isClosed_eq hdelta_continuous hepsilon_continuous
  have hsub : Subgroup.closure s ≤ K := by
    rw [Subgroup.closure_le]
    intro x hx
    exact hs hx
  have htop : (⊤ : Subgroup G) ≤ K := by
    have hcl : (Subgroup.closure s).topologicalClosure ≤ K :=
      Subgroup.topologicalClosure_minimal _ hsub hKclosed
    rw [TopologicallyGenerates] at hsgen
    simpa [hsgen] using hcl
  funext g
  simpa [K] using htop (show g ∈ (⊤ : Subgroup G) from by simp only [Subgroup.mem_top])

section FreeProC

variable {ProC : ProCGroups.ProC.ProCGroupPredicate.{u}}
variable {X F : Type u}
variable [TopologicalSpace X]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {R A : Type*} [Semiring R] [AddCommGroup A] [Module R A]
variable [TopologicalSpace A] [T2Space A]

/-- Continuous crossed differentials on a free pro-`C` source are determined by their values on
the free pro-`C` generators. -/
theorem eq_of_freeProC_of_continuous
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    {coeff : F →* R} {delta epsilon : F → A}
    (hdelta : IsCrossedDifferential coeff delta)
    (hepsilon : IsCrossedDifferential coeff epsilon)
    (hdelta_continuous : Continuous delta) (hepsilon_continuous : Continuous epsilon)
    (hbasis : ∀ x : X, delta (ι x) = epsilon (ι x)) :
    delta = epsilon := by
  refine
    eq_of_continuous_of_topologicallyGenerates
      hdelta hepsilon hdelta_continuous hepsilon_continuous hι.generates_range ?_
  rintro _ ⟨x, rfl⟩
  exact hbasis x

end FreeProC

end IsCrossedDifferential

section UniversalKernelCriterion

variable (C : ProCGroups.FiniteGroupClass.{u})
variable {G H A : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]

/-- To prove the universal completed Magnus-kernel criterion, it is enough to prove it for any
crossed differential represented by the completed universal differential. -/
theorem zcUniversalDifferential_kernel_le_closedCommutator_of_crossedDifferential
    (ψ : G →ₜ* H) (D : G → A)
    (hD : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ.toMonoidHom) D)
    (hkerD :
      ∀ n : ProfiniteKernelSubgroup ψ, D n.1 = 0 →
        n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ)) :
    ∀ n : ProfiniteKernelSubgroup ψ,
      zcUniversalDifferential C ψ.toMonoidHom n.1 = 0 →
        n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ) := by
  intro n hn
  exact hkerD n
    (crossedDifferential_eq_zero_of_zcUniversalDifferential_eq_zero
      (C := C) ψ.toMonoidHom D hD hn)

end UniversalKernelCriterion

section KernelAbelianization

variable (C : ProCGroups.FiniteGroupClass.{u})
variable {G H A : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [T1Space A]
variable [Module (ZCCompletedGroupAlgebra C H) A]

instance instT1SpaceMultiplicativeTarget : T1Space (Multiplicative A) := by
  change T1Space A
  infer_instance

/-- The restriction of a completed crossed differential to the kernel of its
coefficient homomorphism, multiplicatively valued in the additive target. -/
def zcCrossedDifferentialKernelHom
    (ψ : G →ₜ* H) (D : G → A)
    (hD : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ.toMonoidHom) D) :
    ProfiniteKernelSubgroup ψ →* Multiplicative A where
  toFun n := Multiplicative.ofAdd (D n.1)
  map_one' := by
    rw [Submonoid.coe_one]
    exact congrArg Multiplicative.ofAdd (IsCrossedDifferential.one hD)
  map_mul' n m := by
    apply Multiplicative.ext
    change D ((n * m : ProfiniteKernelSubgroup ψ) : G) = D n.1 + D m.1
    rw [Submonoid.coe_mul, hD n.1 m.1]
    have hn : ψ n.1 = 1 := n.2
    simp only [ContinuousMonoidHom.coe_toMonoidHom, zcCompletedGroupAlgebraScalar_apply, MonoidHom.coe_coe, hn,
  map_one, one_smul]

omit [IsTopologicalGroup G] [IsTopologicalAddGroup A] [T1Space A] in
theorem continuous_zcCrossedDifferentialKernelHom
    (ψ : G →ₜ* H) (D : G → A)
    (hD : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ.toMonoidHom) D)
    (hcont : Continuous D) :
    Continuous (zcCrossedDifferentialKernelHom (C := C) ψ D hD) := by
  change Continuous fun n : ProfiniteKernelSubgroup ψ => Multiplicative.ofAdd (D n.1)
  exact continuous_ofAdd.comp (hcont.comp continuous_subtype_val)

/-- A continuous crossed differential on `G` descends along the completed kernel
abelianization of its coefficient homomorphism. This is the natural target of
the completed relation-module map. -/
def zcCrossedDifferentialProfiniteKernelAbelianizationHom
    (ψ : G →ₜ* H) (D : G → A)
    (hD : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ.toMonoidHom) D)
    (hcont : Continuous D) :
    ProfiniteKernelAbelianization ψ →* Multiplicative A :=
  (ProCGroups.Abelian.TopologicalAbelianization.lift
    { toMonoidHom := zcCrossedDifferentialKernelHom (C := C) ψ D hD
      continuous_toFun :=
        continuous_zcCrossedDifferentialKernelHom (C := C) ψ D hD hcont }).toMonoidHom

/-- Additive form of `zcCrossedDifferentialProfiniteKernelAbelianizationHom`. -/
def zcCrossedDifferentialProfiniteKernelAbelianizationAddMonoidHom
    (ψ : G →ₜ* H) (D : G → A)
    (hD : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ.toMonoidHom) D)
    (hcont : Continuous D) :
    ProfiniteKernelAbelianizationAdd ψ →+ A :=
  (zcCrossedDifferentialProfiniteKernelAbelianizationHom
    (C := C) ψ D hD hcont).toAdditiveLeft

omit [IsTopologicalAddGroup A] in
@[simp]
theorem zcCrossedDifferentialProfiniteKernelAbelianizationAddMonoidHom_mk
    (ψ : G →ₜ* H) (D : G → A)
    (hD : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ.toMonoidHom) D)
    (hcont : Continuous D) (n : ProfiniteKernelSubgroup ψ) :
    zcCrossedDifferentialProfiniteKernelAbelianizationAddMonoidHom
      (C := C) ψ D hD hcont
        (Additive.ofMul (QuotientGroup.mk' (Subgroup.closedCommutator _) n)) =
      D n.1 := by
  have h :=
    ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk
      ({ toMonoidHom := zcCrossedDifferentialKernelHom (C := C) ψ D hD
         continuous_toFun :=
          continuous_zcCrossedDifferentialKernelHom (C := C) ψ D hD hcont } :
        ProfiniteKernelSubgroup ψ →ₜ* Multiplicative A) n
  simpa [zcCrossedDifferentialProfiniteKernelAbelianizationAddMonoidHom,
    zcCrossedDifferentialProfiniteKernelAbelianizationHom,
    zcCrossedDifferentialKernelHom,
    ProCGroups.Abelian.TopologicalAbelianization.mk] using
    congrArg Multiplicative.toAdd h

omit [IsTopologicalAddGroup A] in
/-- A continuous completed crossed differential kills the closed commutator subgroup of the
kernel of its coefficient homomorphism. -/
theorem zcCrossedDifferential_eq_zero_of_mem_closedCommutator
    (ψ : G →ₜ* H) (D : G → A)
    (hD : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ.toMonoidHom) D)
    (hcont : Continuous D) {n : ProfiniteKernelSubgroup ψ}
    (hn : n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ)) :
    D n.1 = 0 := by
  let F :=
    zcCrossedDifferentialProfiniteKernelAbelianizationAddMonoidHom
      (C := C) ψ D hD hcont
  have hnq :
      QuotientGroup.mk' (Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ)) n = 1 :=
    (QuotientGroup.eq_one_iff
      (N := Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ)) n).2 hn
  have h :=
    congrArg (fun q : ProfiniteKernelAbelianization ψ => F (Additive.ofMul q)) hnq
  simpa [F] using h

omit [IsTopologicalAddGroup A] in
theorem zcCrossedDiffProfiniteKernelAbelianizationAddMonoidHom_inj_of_kernel_le_closedCommutator
    (ψ : G →ₜ* H) (D : G → A)
    (hD : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ.toMonoidHom) D)
    (hcont : Continuous D)
    (hker :
      ∀ n : ProfiniteKernelSubgroup ψ, D n.1 = 0 →
        n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ)) :
    Function.Injective
      (zcCrossedDifferentialProfiniteKernelAbelianizationAddMonoidHom
        (C := C) ψ D hD hcont) := by
  intro x y hxy
  suffices x - y = 0 by exact sub_eq_zero.mp this
  let F :=
    zcCrossedDifferentialProfiniteKernelAbelianizationAddMonoidHom
      (C := C) ψ D hD hcont
  have hmap : F (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hzero_of_map_zero :
      ∀ z : ProfiniteKernelAbelianizationAdd ψ, F z = 0 → z = 0 := by
    intro z hz
    apply Additive.toMul.injective
    change (Additive.toMul z : ProfiniteKernelAbelianization ψ) = 1
    revert hz
    change
      (fun q : ProfiniteKernelAbelianization ψ =>
        F (Additive.ofMul q) = 0 → q = 1) (Additive.toMul z)
    refine QuotientGroup.induction_on (Additive.toMul z) ?_
    intro n hn
    change QuotientGroup.mk' (Subgroup.closedCommutator _) n = 1
    exact (QuotientGroup.eq_one_iff
      (N := Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ)) n).2
        (hker n (by simpa [F] using hn))
  exact hzero_of_map_zero (x - y) hmap

omit [IsTopologicalAddGroup A] in
/-- Injectivity of the induced map on the topological kernel abelianization is exactly the
continuous Magnus-kernel criterion. -/
theorem zcCrossedDifferentialProfiniteKernelAbelianizationAddMonoidHom_injective_iff
    (ψ : G →ₜ* H) (D : G → A)
    (hD : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ.toMonoidHom) D)
    (hcont : Continuous D) :
    Function.Injective
        (zcCrossedDifferentialProfiniteKernelAbelianizationAddMonoidHom
          (C := C) ψ D hD hcont) ↔
      ∀ n : ProfiniteKernelSubgroup ψ, D n.1 = 0 →
        n ∈ Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ) := by
  constructor
  · intro hinj n hn
    let F :=
      zcCrossedDifferentialProfiniteKernelAbelianizationAddMonoidHom
        (C := C) ψ D hD hcont
    have hzero :
        F (Additive.ofMul
            (QuotientGroup.mk' (Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ)) n)) =
          F 0 := by
      simpa [F, hn]
    have hclass :
        Additive.ofMul
            (QuotientGroup.mk' (Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ)) n) =
          0 := hinj hzero
    have hmk :
        QuotientGroup.mk' (Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ)) n = 1 := by
      simpa using congrArg Additive.toMul hclass
    exact (QuotientGroup.eq_one_iff
      (N := Subgroup.closedCommutator (ProfiniteKernelSubgroup ψ)) n).1 hmk
  · intro hker
    exact
      zcCrossedDiffProfiniteKernelAbelianizationAddMonoidHom_inj_of_kernel_le_closedCommutator
        (C := C) ψ D hD hcont hker

end KernelAbelianization

section CompletedFundamentalFormula

variable (C : ProCGroups.FiniteGroupClass.{u})
variable [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)]
variable {X : Type u} [Fintype X] [DecidableEq X]
variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- Source-shaped completed Fox boundary formula from continuity and topological generation.

This is the abstract form of the completed Fox fundamental formula: no free pro-`C` universal
property is needed once the source generators topologically generate the source. -/
theorem freeProCZCBoundary_of_topologicalGeneration
    {ι : X → G}
    (hgen : TopologicallyGenerates (G := G) (Set.range ι))
    (ψ : G →* H) (delta : G → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta)
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) = Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (g : G) :
    freeProCZCCompletedFoxBoundary C (fun x : X => ψ (ι x)) (delta g) =
      zcCompletedGroupAlgebraBoundary C ψ g := by
  let beta : G → ZCCompletedGroupAlgebra C H :=
    fun g => freeProCZCCompletedFoxBoundary C (fun x : X => ψ (ι x)) (delta g)
  have hbeta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) beta :=
    IsCrossedDifferential.map_linear hdelta
      (freeProCZCCompletedFoxBoundary C (fun x : X => ψ (ι x)))
  have hboundary :
      IsCrossedDifferential
        (zcCompletedGroupAlgebraScalar C ψ) (zcCompletedGroupAlgebraBoundary C ψ) :=
    zcCompletedGroupAlgebraBoundary_isCrossedDifferential C ψ
  have hbeta_continuous : Continuous beta :=
    (continuous_freeProCZCCompletedFoxBoundary C (fun x : X => ψ (ι x))).comp hdelta_continuous
  have hboundary_continuous : Continuous (zcCompletedGroupAlgebraBoundary C ψ) :=
    continuous_zcCompletedGroupAlgebraBoundary (C := C) (G := H) ψ hψ_continuous
  have hEqOn :
      Set.EqOn beta (zcCompletedGroupAlgebraBoundary C ψ) (Set.range ι) := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    simp only [hbasis x, freeProCZCCompletedFoxBoundary_single, zcCompletedGroupAlgebraBoundary, beta]
  have hEq :=
    IsCrossedDifferential.eq_of_continuous_of_topologicallyGenerates
      hbeta hboundary hbeta_continuous hboundary_continuous hgen hEqOn
  exact congrFun hEq g

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [DecidableEq X] [TopologicalSpace G]
  [IsTopologicalGroup G] in
/-- Exactness at the finite completed Fox-coordinate term from a surjective semidirect graph.

The hypothesis says that the crossed-differential graph
`g ↦ (delta g, ψ g)` fills `Z_C[[H]]^X ⋊ H`.  Then every vector killed by the
source-shaped Fox boundary is the derivative of an element of `ker ψ`. -/
theorem exact_zcCrossedDiffKernelAddMonoidHom_freeProCZCCompletedFoxBoundary_of_surj_semi
    (φ : X → H)
    (ψ : G →* H) (delta : G → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta)
    (hboundary :
      ∀ g : G,
        freeProCZCCompletedFoxBoundary C φ (delta g) =
          zcCompletedGroupAlgebraBoundary C ψ g)
    (hgraph :
      Function.Surjective
        (fun g : G =>
          ({ left := delta g, right := ψ g } :
            ZCCompletedFoxSemidirect C X H))) :
    Function.Exact
      (zcCrossedDifferentialKernelAddMonoidHom C ψ delta hdelta)
      (freeProCZCCompletedFoxBoundary C φ) := by
  intro v
  constructor
  · intro hv
    rcases hgraph
        ({ left := v, right := 1 } :
          ZCCompletedFoxSemidirect C X H) with
      ⟨g, hg⟩
    have hdelta_g : delta g = v := congrArg ZCCompletedFoxSemidirect.left hg
    have hψ_g : ψ g = 1 := congrArg ZCCompletedFoxSemidirect.right hg
    refine ⟨Additive.ofMul (⟨g, hψ_g⟩ : ψ.ker), ?_⟩
    simp only [zcCrossedDifferentialKernelAddMonoidHom_apply, hdelta_g]
  · rintro ⟨n, hn⟩
    rw [← hn]
    change
      freeProCZCCompletedFoxBoundary C φ
        (delta (((Additive.toMul n : ψ.ker) : G))) = 0
    rw [hboundary (((Additive.toMul n : ψ.ker) : G))]
    exact zcCompletedGroupAlgebraBoundary_eq_zero_of_mem_ker
      (C := C) (ψ := ψ) (g := ((Additive.toMul n : ψ.ker) : G))
      (Additive.toMul n).2

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] [TopologicalSpace G]
  [IsTopologicalGroup G] in
/-- If a completed semidirect Fox lift onto `Z_C[[H]]^X ⋊ H` is actually
surjective, then every generator boundary `[φ x] - 1` must vanish.

This is a useful diagnostic obstruction: the graph generators of a free source
cannot generally topologically generate the whole semidirect product. -/
theorem zcCompletedFoxSemidirect_surjective_forces_generator_boundary_zero
    (φ : X → H)
    (ψ : G →* H) (delta : G → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hboundary :
      ∀ g : G,
        freeProCZCCompletedFoxBoundary C φ (delta g) =
          zcCompletedGroupAlgebraBoundary C ψ g)
    (hgraph :
      Function.Surjective
        (fun g : G =>
          ({ left := delta g, right := ψ g } :
            ZCCompletedFoxSemidirect C X H))) (x : X) :
    zcGroupLike C H (φ x) - 1 = 0 := by
  rcases hgraph
      ({ left := Pi.single x (1 : ZCCompletedGroupAlgebra C H), right := 1 } :
        ZCCompletedFoxSemidirect C X H) with
    ⟨g, hg⟩
  have hdelta_g : delta g = Pi.single x (1 : ZCCompletedGroupAlgebra C H) :=
    congrArg ZCCompletedFoxSemidirect.left hg
  have hψ_g : ψ g = 1 := congrArg ZCCompletedFoxSemidirect.right hg
  calc
    zcGroupLike C H (φ x) - 1 =
        freeProCZCCompletedFoxBoundary C φ
          (Pi.single x (1 : ZCCompletedGroupAlgebra C H)) := by
      rw [freeProCZCCompletedFoxBoundary_single]
    _ = freeProCZCCompletedFoxBoundary C φ (delta g) := by rw [hdelta_g]
    _ = zcCompletedGroupAlgebraBoundary C ψ g := hboundary g
    _ = 0 := by simp only [zcCompletedGroupAlgebraBoundary, hψ_g, map_one, sub_self]

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- Exactness at the finite completed Fox-coordinate term, with the boundary identity supplied by
continuity and topological generation of the source generators. -/
theorem exact_zcKernelAdd_freeProCZCFoxBoundary_of_topGen
    {ι : X → G}
    (hgen : TopologicallyGenerates (G := G) (Set.range ι))
    (ψ : G →* H) (delta : G → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta)
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) = Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (hgraph :
      Function.Surjective
        (fun g : G =>
          ({ left := delta g, right := ψ g } :
            ZCCompletedFoxSemidirect C X H))) :
    Function.Exact
      (zcCrossedDifferentialKernelAddMonoidHom C ψ delta hdelta)
      (freeProCZCCompletedFoxBoundary C (fun x : X => ψ (ι x))) := by
  exact
    exact_zcCrossedDiffKernelAddMonoidHom_freeProCZCCompletedFoxBoundary_of_surj_semi
      (C := C) (X := X) (G := G) (H := H)
      (fun x : X => ψ (ι x)) ψ delta hdelta
      (freeProCZCBoundary_of_topologicalGeneration
        (C := C) (X := X) (G := G) (H := H)
        hgen ψ delta hdelta hdelta_continuous hψ_continuous hbasis)
      hgraph

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- Source-shaped completed Fox fundamental formula from continuity and topological generation. -/
theorem freeProCZCFundamentalFormula_of_topologicalGeneration
    {ι : X → G}
    (hgen : TopologicallyGenerates (G := G) (Set.range ι))
    (ψ : G →* H) (delta : G → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta)
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) = Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (g : G) :
    zcCompletedGroupAlgebraBoundary C ψ g =
      ∑ x : X, delta g x * (zcGroupLike C H (ψ (ι x)) - 1) := by
  simpa [freeProCZCCompletedFoxBoundary_apply] using
    (freeProCZCBoundary_of_topologicalGeneration
      (X := X) (G := G) (H := H) C hgen ψ delta hdelta hdelta_continuous hψ_continuous hbasis g).symm

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- Finite-stage projection of the source-shaped completed Fox formula obtained from continuity
and topological generation. -/
theorem freeProCZCFundamentalFormula_stage_of_topologicalGeneration
    {ι : X → G}
    (hgen : TopologicallyGenerates (G := G) (Set.range ι))
    (ψ : G →* H) (delta : G → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta)
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) = Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (j : ZCCompletedGroupAlgebraIndex C H) (g : G) :
    zcCompletedGroupAlgebraProjection C H j
        (zcCompletedGroupAlgebraBoundary C ψ g) =
      zcCompletedGroupAlgebraProjection C H j
        (∑ x : X, delta g x * (zcGroupLike C H (ψ (ι x)) - 1)) := by
  exact congrArg (zcCompletedGroupAlgebraProjection C H j)
    (freeProCZCFundamentalFormula_of_topologicalGeneration
      (X := X) (G := G) (H := H) C hgen ψ delta hdelta hdelta_continuous hψ_continuous hbasis g)

omit [Fact (ProCGroups.FiniteGroupClass.FiniteOnly C)] in
/-- Explicit Euler-sum form from continuity and topological generation. -/
theorem freeProCZCEulerFormula_of_topologicalGeneration
    {ι : X → G}
    (hgen : TopologicallyGenerates (G := G) (Set.range ι))
    (ψ : G →* H) (delta : G → ZCFreeFoxCoordinates C (X := X) (H := H))
    (hdelta : IsCrossedDifferential (zcCompletedGroupAlgebraScalar C ψ) delta)
    (hdelta_continuous : Continuous delta) (hψ_continuous : Continuous ψ)
    (hbasis :
      ∀ x : X, delta (ι x) = Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (g : G) :
    zcGroupLike C H (ψ g) - 1 =
      ∑ x : X, delta g x * (zcGroupLike C H (ψ (ι x)) - 1) := by
  simpa [zcCompletedGroupAlgebraBoundary] using
    freeProCZCFundamentalFormula_of_topologicalGeneration
      (X := X) (G := G) (H := H) C hgen ψ delta hdelta hdelta_continuous hψ_continuous hbasis g

end CompletedFundamentalFormula

section FreeProCCompletedExt

variable {ProC : ProCGroups.ProC.ProCGroupPredicate.{u}}
variable {X F H : Type u}
variable [TopologicalSpace X]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Extensionality for continuous completed crossed differentials on a free pro-`C` source,
using continuity of the coordinate-valued maps themselves. -/
theorem freeProCZCCompletedCrossedDifferential_ext_of_continuous
    {ι : X → F} (hι : ProCGroups.FreeProC.IsFreeProCGroup (ProC := ProC) ι)
    (ψ : F →* H)
    (delta epsilon :
      F → ZCFreeFoxCoordinates ProC.finiteQuotientClass (X := X) (H := H))
    (hdelta :
      IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) delta)
    (hepsilon :
      IsCrossedDifferential (zcCompletedGroupAlgebraScalar ProC.finiteQuotientClass ψ) epsilon)
    (hdelta_continuous : Continuous delta) (hepsilon_continuous : Continuous epsilon)
    (hbasis : ∀ x : X, delta (ι x) = epsilon (ι x)) :
    delta = epsilon := by
  exact IsCrossedDifferential.eq_of_freeProC_of_continuous
    (ProC := ProC) hι hdelta hepsilon hdelta_continuous hepsilon_continuous hbasis

end FreeProCCompletedExt

end

end FoxDifferential
