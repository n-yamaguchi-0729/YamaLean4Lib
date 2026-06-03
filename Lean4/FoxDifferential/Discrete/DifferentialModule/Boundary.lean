import FoxDifferential.Discrete.DifferentialModule.Universal

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FoxDifferential/Discrete/DifferentialModule/Boundary.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Discrete group-ring Fox calculus

The completed differential module is organized separately from coefficient algebras; its universal and quotient maps are used by completed crossed differentials.
-/
namespace FoxDifferential

noncomputable section

variable {H G : Type*} [Group H] [Group G]

/-- The standard map `G → ℤ[H]`, `g ↦ ψ(g) - 1`, viewed as a differential map. -/
def groupRingBoundary (ψ : G →* H) (g : G) : GroupRing H :=
  MonoidAlgebra.of ℤ H (ψ g) - 1

/-- The Fox boundary vanishes at the identity. -/
@[simp]
theorem groupRingBoundary_one (ψ : G →* H) :
    groupRingBoundary ψ (1 : G) = 0 := by
  simp only [groupRingBoundary, map_one, groupRing_of_one (H := H), sub_self]

/-- The Fox boundary is zero on elements in the kernel of `ψ`. -/
@[simp]
theorem groupRingBoundary_eq_zero_of_mem_ker (ψ : G →* H) {g : G} (hg : ψ g = 1) :
    groupRingBoundary ψ g = 0 := by
  rw [groupRingBoundary, hg, groupRing_of_one (H := H)]
  simp only [sub_self]

/-- The Fox boundary vanishes on the kernel subgroup of `ψ`. -/
@[simp]
theorem groupRingBoundary_subtype_ker (ψ : G →* H) (g : ψ.ker) :
    groupRingBoundary ψ g = 0 :=
  groupRingBoundary_eq_zero_of_mem_ker (ψ := ψ) g.2

/-- The Fox boundary is itself a crossed differential. -/
theorem groupRingBoundary_isDifferential (ψ : G →* H) :
    IsDifferentialMap (A := GroupRing H) ψ (groupRingBoundary ψ) := by
  intro g₁ g₂
  simp only [groupRingBoundary, map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one,
  sub_eq_add_neg, add_comm, groupRingScalar_apply, smul_eq_mul, mul_add, mul_neg, add_assoc,
  add_neg_cancel_comm_assoc]

/-- Group-ring functoriality carries Fox boundaries to Fox boundaries. -/
@[simp]
theorem groupRingMap_groupRingBoundary {K : Type*} [Group K]
    (φ : H →* K) (ψ : G →* H) (g : G) :
    groupRingMap φ (groupRingBoundary ψ g) = groupRingBoundary (φ.comp ψ) g := by
  simp only [groupRingBoundary, MonoidAlgebra.of_apply, map_sub, groupRingMap_single, map_one,
  MonoidHom.coe_comp, Function.comp_apply]

/-- The universal boundary map `A_ψ → ℤ[H]`, `universalDifferential(g) ↦ ψ(g) - 1`. -/
def toGroupRing (ψ : G →* H) : DifferentialModule ψ →ₗ[GroupRing H] GroupRing H :=
  lift (A := GroupRing H) ψ (groupRingBoundary ψ) (groupRingBoundary_isDifferential ψ)

/-- The universal boundary sends `universalDifferential g` to `[ψ g] - 1`. -/
theorem toGroupRing_d (ψ : G →* H) (g : G) :
    toGroupRing ψ (universalDifferential ψ g) = groupRingBoundary ψ g := by
  simpa [toGroupRing] using
    lift_d (A := GroupRing H) ψ (groupRingBoundary ψ) (groupRingBoundary_isDifferential ψ) g


/-- The standard group-ring generator `h - 1` appearing in Fox boundary formulas. -/
def augmentationGenerator (H : Type*) [Group H] (h : H) : GroupRing H :=
  MonoidAlgebra.of Int H h - 1

/-- The standard augmentation generator at the identity is zero. -/
@[simp]
theorem augmentationGenerator_one (H : Type*) [Group H] :
    augmentationGenerator H (1 : H) = 0 := by
  simp only [augmentationGenerator, groupRing_of_one (H := H), sub_self]

/-- The augmentation generator is the identity-coefficient Fox boundary. -/
@[simp]
theorem augmentationGenerator_eq_groupRingBoundary (H : Type*) [Group H] (h : H) :
    augmentationGenerator H h = groupRingBoundary (MonoidHom.id H) h :=
  rfl

/-- Group-ring functoriality carries augmentation generators to augmentation generators. -/
@[simp]
theorem groupRingMap_augmentationGenerator {K : Type*} [Group K]
    (φ : H →* K) (h : H) :
    groupRingMap φ (augmentationGenerator H h) = augmentationGenerator K (φ h) := by
  simp only [augmentationGenerator, MonoidAlgebra.of_apply, map_sub, groupRingMap_single, map_one]


end

end FoxDifferential
