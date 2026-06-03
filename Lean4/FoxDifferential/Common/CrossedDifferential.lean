import Mathlib.Algebra.Group.Commutator
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.LinearMap.Basic

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Common/CrossedDifferential.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Universal Fox calculus

Crossed differentials, universal differential modules, Fox boundaries, Euler formulas, and Jacobians are the common algebraic layer used by Crowell and metabelian applications.
-/
namespace FoxDifferential

open scoped BigOperators

/-- A crossed differential with coefficient homomorphism `coeff : G ->* R`.

The rule is the Fox Leibniz rule
`delta (g * h) = delta g + coeff g • delta h`. -/
def IsCrossedDifferential
    {R G A : Type*} [Semiring R] [Group G] [AddCommMonoid A] [Module R A]
    (coeff : G →* R) (delta : G → A) : Prop :=
  ∀ g h, delta (g * h) = delta g + coeff g • delta h

namespace IsCrossedDifferential

variable {R G A : Type*} [Semiring R] [Group G] [AddCommGroup A] [Module R A]
variable {coeff : G →* R} {delta : G → A}

/-- The zero map is a crossed differential. -/
theorem zero :
    IsCrossedDifferential coeff (fun _ : G => (0 : A)) := by
  intro g h
  simp only [smul_zero, add_zero]

/-- Crossed differentials with the same coefficient homomorphism are closed under addition. -/
theorem add {delta epsilon : G → A}
    (hdelta : IsCrossedDifferential coeff delta)
    (hepsilon : IsCrossedDifferential coeff epsilon) :
    IsCrossedDifferential coeff (fun g => delta g + epsilon g) := by
  intro g h
  change delta (g * h) + epsilon (g * h) =
    delta g + epsilon g + coeff g • (delta h + epsilon h)
  rw [hdelta g h, hepsilon g h]
  simp only [add_left_comm, add_assoc, smul_add]

/-- Crossed differentials are closed under negation. -/
theorem neg (hdelta : IsCrossedDifferential coeff delta) :
    IsCrossedDifferential coeff (fun g => -delta g) := by
  intro g h
  change -delta (g * h) = -delta g + coeff g • -delta h
  rw [hdelta g h]
  simp only [neg_add_rev, add_comm, smul_neg]

/-- Crossed differentials with the same coefficient homomorphism are closed under subtraction. -/
theorem sub {delta epsilon : G → A}
    (hdelta : IsCrossedDifferential coeff delta)
    (hepsilon : IsCrossedDifferential coeff epsilon) :
    IsCrossedDifferential coeff (fun g => delta g - epsilon g) := by
  simpa [sub_eq_add_neg] using add hdelta (neg hepsilon)

/-- A linear map sends crossed differentials to crossed differentials. -/
theorem map_linear {B : Type*} [AddCommGroup B] [Module R B]
    (hdelta : IsCrossedDifferential coeff delta) (f : A →ₗ[R] B) :
    IsCrossedDifferential coeff (fun g => f (delta g)) := by
  intro g h
  change f (delta (g * h)) = f (delta g) + coeff g • f (delta h)
  rw [hdelta g h]
  simp only [map_add, map_smul]

/-- Pulling a crossed differential back along a group homomorphism is a crossed differential. -/
theorem comp_monoidHom {K : Type*} [Group K]
    (hdelta : IsCrossedDifferential coeff delta) (φ : K →* G) :
    IsCrossedDifferential (coeff.comp φ) (fun k : K => delta (φ k)) := by
  intro g h
  simpa [MonoidHom.comp_apply, map_mul] using hdelta (φ g) (φ h)

/-- Restricting a crossed differential to any subgroup on which the coefficient homomorphism is
trivial gives an ordinary additive homomorphism. -/
def restrictTrivialSubgroupAddMonoidHom
    (hdelta : IsCrossedDifferential coeff delta) (N : Subgroup G)
    (hN : ∀ n : N, coeff n = 1) :
    Additive N →+ A where
  toFun x := delta ((Additive.toMul x : N) : G)
  map_zero' := by
    change delta (1 : G) = 0
    have h := hdelta 1 1
    rw [map_one, one_smul] at h
    have h' := congrArg (fun z : A => z - delta 1) h
    have hzero : 0 = delta 1 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
    simpa using hzero.symm
  map_add' x y := by
    change delta (((Additive.toMul x : N) * (Additive.toMul y : N) : N) : G) =
      delta ((Additive.toMul x : N) : G) + delta ((Additive.toMul y : N) : G)
    have h :=
      hdelta ((Additive.toMul x : N) : G) ((Additive.toMul y : N) : G)
    simpa [hN (Additive.toMul x)] using h

@[simp]
theorem restrictTrivialSubgroupAddMonoidHom_apply
    (hdelta : IsCrossedDifferential coeff delta) (N : Subgroup G)
    (hN : ∀ n : N, coeff n = 1) (g : N) :
    restrictTrivialSubgroupAddMonoidHom hdelta N hN (Additive.ofMul g) = delta g :=
  rfl

/-- A crossed differential vanishes at the identity. -/
theorem one (hdelta : IsCrossedDifferential coeff delta) :
    delta 1 = 0 := by
  have h := hdelta 1 1
  rw [map_one, one_smul] at h
  have h' := congrArg (fun z : A => z - delta 1) h
  have hzero : 0 = delta 1 := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h'
  simpa using hzero.symm

/-- Inverse rule for a crossed differential. -/
theorem inv (hdelta : IsCrossedDifferential coeff delta) (g : G) :
    delta g⁻¹ = -(coeff g⁻¹ • delta g) := by
  have h := hdelta g⁻¹ g
  rw [inv_mul_cancel, one hdelta] at h
  rw [eq_neg_iff_add_eq_zero]
  exact h.symm

/-- Product rule, restated as a theorem for namespaced rewriting. -/
theorem mul (hdelta : IsCrossedDifferential coeff delta) (g h : G) :
    delta (g * h) = delta g + coeff g • delta h :=
  hdelta g h

/-- Formula for multiplying by an inverse on the left. -/
theorem inv_mul (hdelta : IsCrossedDifferential coeff delta) (g h : G) :
    delta (g⁻¹ * h) =
      -(coeff g⁻¹ • delta g) + coeff g⁻¹ • delta h := by
  rw [mul hdelta, inv hdelta]

/-- Formula for multiplying by an inverse on the right. -/
theorem mul_inv (hdelta : IsCrossedDifferential coeff delta) (g h : G) :
    delta (g * h⁻¹) =
      delta g - coeff (g * h⁻¹) • delta h := by
  rw [mul hdelta, inv hdelta]
  simp only [smul_neg, smul_smul, map_mul, sub_eq_add_neg]

/-- Division rule for a crossed differential. -/
theorem div (hdelta : IsCrossedDifferential coeff delta) (g h : G) :
    delta (g / h) =
      delta g - coeff (g / h) • delta h := by
  simpa [div_eq_mul_inv] using mul_inv hdelta g h

/-- Conjugation rule for a crossed differential. -/
theorem conj (hdelta : IsCrossedDifferential coeff delta) (g h : G) :
    delta (g * h * g⁻¹) =
      delta g + coeff g • delta h - coeff (g * h * g⁻¹) • delta g := by
  rw [mul_inv hdelta (g * h) g, mul hdelta g h]

/-- Commutator rule for a crossed differential. -/
theorem commutator (hdelta : IsCrossedDifferential coeff delta) (g h : G) :
    delta ⁅g, h⁆ =
      delta g + coeff g • delta h -
        coeff (g * h * g⁻¹) • delta g -
        coeff ⁅g, h⁆ • delta h := by
  rw [commutatorElement_def, mul_inv hdelta (g * h * g⁻¹) h,
    conj hdelta g h]

/-- Two crossed differentials with the same coefficients that agree on a set agree on the
abstract subgroup generated by that set. -/
theorem eqOn_closure {delta epsilon : G → A}
    (hdelta : IsCrossedDifferential coeff delta)
    (hepsilon : IsCrossedDifferential coeff epsilon)
    {s : Set G} (hs : Set.EqOn delta epsilon s) :
    Set.EqOn delta epsilon ((Subgroup.closure s : Subgroup G) : Set G) := by
  intro g hg
  exact
    Subgroup.closure_induction
      (p := fun g _ => delta g = epsilon g)
      (fun x hx => hs hx)
      (by
        change delta 1 = epsilon 1
        rw [hdelta.one, hepsilon.one])
      (fun x y _ _ hx hy => by
        change delta (x * y) = epsilon (x * y)
        rw [hdelta.mul x y, hepsilon.mul x y, hx, hy])
      (fun x _ hx => by
        change delta x⁻¹ = epsilon x⁻¹
        rw [hdelta.inv x, hepsilon.inv x, hx])
      hg

/-- Crossed differentials with the same coefficients are determined by a generating set. -/
theorem eq_of_closure_eq_top {delta epsilon : G → A}
    (hdelta : IsCrossedDifferential coeff delta)
    (hepsilon : IsCrossedDifferential coeff epsilon)
    {s : Set G} (hsgen : Subgroup.closure s = ⊤)
    (hs : Set.EqOn delta epsilon s) :
    delta = epsilon := by
  funext g
  exact (eqOn_closure hdelta hepsilon hs) (by simp only [hsgen, Subgroup.coe_top, Set.mem_univ])

/-- Positive power rule for a crossed differential. -/
theorem pow (hdelta : IsCrossedDifferential coeff delta) (g : G) (n : ℕ) :
    delta (g ^ n) =
      (Finset.range n).sum (fun k => coeff (g ^ k) • delta g) := by
  induction n with
  | zero =>
      simp only [pow_zero, one hdelta, Finset.range_zero, map_pow, Finset.sum_empty]
  | succ n ih =>
      rw [pow_succ, hdelta, ih]
      simp only [map_pow, Finset.sum_range_succ]

/-- Positive power rule with the coefficient sum factored out. -/
theorem pow_smul_sum (hdelta : IsCrossedDifferential coeff delta) (g : G) (n : ℕ) :
    delta (g ^ n) =
      ((Finset.range n).sum (fun k => coeff (g ^ k))) • delta g := by
  rw [pow hdelta g n]
  simp only [map_pow, Finset.sum_smul]

/-- Positive power rule applied to the inverse element. -/
theorem inv_pow (hdelta : IsCrossedDifferential coeff delta) (g : G) (n : ℕ) :
    delta (g⁻¹ ^ n) =
      (Finset.range n).sum (fun k =>
        coeff (g⁻¹ ^ k) • (-(coeff g⁻¹ • delta g))) := by
  rw [pow hdelta g⁻¹ n, inv hdelta]

end IsCrossedDifferential

end FoxDifferential
