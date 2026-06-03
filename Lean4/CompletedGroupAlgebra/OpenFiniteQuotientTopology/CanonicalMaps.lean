import CompletedGroupAlgebra.Basic.ClassComparison

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/CompletedGroupAlgebra/OpenFiniteQuotientTopology/CanonicalMaps.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Completed group algebras

The completed group algebra is presented as an inverse limit of finite group algebras, together with canonical augmentation, augmentation ideal, finite-stage maps, functoriality, and profinite module universal properties.
-/
open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The quotient map from the abstract group algebra `R[G]` to one `C`-indexed finite stage. -/
def completedGroupAlgebraStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (R : Type u) (G : Type v) [CommRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    MonoidAlgebra R G →+* CompletedGroupAlgebraStageInClass C R G U :=
  MonoidAlgebra.mapDomainRingHom R
    (openNormalSubgroupInClassProj (C := C) (G := G) U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraStageMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (g : G) :
    completedGroupAlgebraStageMapInClass C R G U (MonoidAlgebra.of R G g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1 := by
  classical
  simp only [completedGroupAlgebraStageMapInClass, MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk,
  OneHom.coe_mk, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]
  rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraStageMapInClass_single
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (g : G) (r : R) :
    completedGroupAlgebraStageMapInClass C R G U (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) r := by
  classical
  simp only [completedGroupAlgebraStageMapInClass, MonoidAlgebra.single, MonoidAlgebra.mapDomainRingHom_apply,
  Finsupp.mapDomain_single]
  rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraStageMapInClass_smul
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (r : R) (x : MonoidAlgebra R G) :
    completedGroupAlgebraStageMapInClass C R G U (r • x) =
      r • completedGroupAlgebraStageMapInClass C R G U x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  simp only [completedGroupAlgebraStageMapInClass, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one]

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraStageMapInClass_algebraMap
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (r : R) :
    completedGroupAlgebraStageMapInClass C R G U (algebraMap R (MonoidAlgebra R G) r) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r := by
  simp only [completedGroupAlgebraStageMapInClass, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one]

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraStageMapInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C) :
    Function.Surjective (completedGroupAlgebraStageMapInClass C R G U) := by
  classical
  intro x
  induction x using Finsupp.induction with
  | zero =>
      exact ⟨0, map_zero (completedGroupAlgebraStageMapInClass C R G U)⟩
  | single_add q r x _ _ ih =>
      rcases openNormalSubgroupInClassProj_surjective (C := C) (G := G) U q with ⟨g, hg⟩
      rcases ih with ⟨y, hy⟩
      refine ⟨(MonoidAlgebra.single g r : MonoidAlgebra R G) + y, ?_⟩
      rw [map_add, completedGroupAlgebraStageMapInClass_single, hy, hg]

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraStageMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (completedGroupAlgebraTransitionInClass C R G hUV).comp
        (completedGroupAlgebraStageMapInClass C R G V) =
      completedGroupAlgebraStageMapInClass C R G U := by
  rw [completedGroupAlgebraTransitionInClass, completedGroupAlgebraStageMapInClass,
    completedGroupAlgebraStageMapInClass, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1

/-- The `C`-indexed finite-stage quotient maps form a compatible family. -/
theorem completedGroupAlgebraStageMapInClass_compatibleMaps
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    (completedGroupAlgebraSystemInClass C hC R G).CompatibleMaps
      (fun U => completedGroupAlgebraStageMapInClass C R G U) := by
  intro U V hUV
  funext x
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageMapInClass_compatible (R := R) (G := G) C hUV))
    x

/-- The canonical map `R[G] -> [[R G]]_C`, obtained from all `C`-indexed quotient maps. -/
def toCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : MonoidAlgebra R G) : CompletedGroupAlgebraInClass C hC R G :=
  ⟨fun U => completedGroupAlgebraStageMapInClass C R G U x, by
    intro U V hUV
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraStageMapInClass_compatible (R := R) (G := G) C hUV))
      x⟩

@[simp]
theorem completedGroupAlgebraProjectionInClass_toCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) (x : MonoidAlgebra R G) :
    completedGroupAlgebraProjectionInClass C hC R G U
        (toCompletedGroupAlgebraInClass C hC R G x) =
      completedGroupAlgebraStageMapInClass C R G U x :=
  rfl

@[simp]
theorem toCompletedGroupAlgebraInClass_smul
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (r : R) (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraInClass C hC R G (r • x) =
      r • toCompletedGroupAlgebraInClass C hC R G x := by
  apply (completedGroupAlgebraSystemInClass C hC R G).ext
  intro U
  change completedGroupAlgebraStageMapInClass C R G U (r • x) =
    r • completedGroupAlgebraStageMapInClass C R G U x
  exact completedGroupAlgebraStageMapInClass_smul (R := R) (G := G) C U r x

/-- The canonical map `R[G] -> [[R G]]_C`, as a ring homomorphism. -/
def toCompletedGroupAlgebraInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    MonoidAlgebra R G →+* CompletedGroupAlgebraInClass C hC R G where
  toFun := toCompletedGroupAlgebraInClass C hC R G
  map_zero' := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    exact map_zero (completedGroupAlgebraStageMapInClass C R G U)
  map_one' := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    exact map_one (completedGroupAlgebraStageMapInClass C R G U)
  map_add' x y := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    exact map_add (completedGroupAlgebraStageMapInClass C R G U) x y
  map_mul' x y := by
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    exact map_mul (completedGroupAlgebraStageMapInClass C R G U) x y

@[simp]
theorem toCompletedGroupAlgebraInClassRingHom_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraInClassRingHom C hC R G x =
      toCompletedGroupAlgebraInClass C hC R G x :=
  rfl

/-- The canonical map `R[G] -> [[R G]]_C`, as an algebra homomorphism. -/
def toCompletedGroupAlgebraInClassAlgHom
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    MonoidAlgebra R G →ₐ[R] CompletedGroupAlgebraInClass C hC R G where
  toRingHom := toCompletedGroupAlgebraInClassRingHom C hC R G
  commutes' := by
    intro r
    apply (completedGroupAlgebraSystemInClass C hC R G).ext
    intro U
    change completedGroupAlgebraStageMapInClass C R G U
        (algebraMap R (MonoidAlgebra R G) r) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r
    exact completedGroupAlgebraStageMapInClass_algebraMap (R := R) (G := G) C U r

@[simp]
theorem toCompletedGroupAlgebraInClassAlgHom_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraInClassAlgHom C hC R G x =
      toCompletedGroupAlgebraInClass C hC R G x :=
  rfl

/-- The canonical map `R[G] -> [[R G]]_C`, as a linear map. -/
def toCompletedGroupAlgebraInClassLinearMap
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    MonoidAlgebra R G →ₗ[R] CompletedGroupAlgebraInClass C hC R G where
  toFun := toCompletedGroupAlgebraInClass C hC R G
  map_add' := by
    intro x y
    exact map_add (toCompletedGroupAlgebraInClassRingHom C hC R G) x y
  map_smul' := toCompletedGroupAlgebraInClass_smul (R := R) (G := G) C hC

@[simp]
theorem toCompletedGroupAlgebraInClassLinearMap_apply
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraInClassLinearMap C hC R G x =
      toCompletedGroupAlgebraInClass C hC R G x :=
  rfl

@[simp]
theorem completedGAProjRingHomInClass_comp_toCompletedGAInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    (completedGroupAlgebraProjectionRingHomInClass C hC R G U).comp
        (toCompletedGroupAlgebraInClassRingHom C hC R G) =
      completedGroupAlgebraStageMapInClass C R G U := by
  apply RingHom.ext
  intro x
  rfl

/-- The abstract group algebra is dense in the `C`-indexed completed group algebra when `G` is
pro-`C` and `C` is a formation. -/
theorem denseRange_toCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    DenseRange (toCompletedGroupAlgebraInClass C hC R G) := by
  let S := completedGroupAlgebraSystemInClass C hC R G
  letI : Nonempty (OpenNormalSubgroupInClass C G) :=
    IsProCGroup.openNormalSubgroupInClass_nonempty hG
  letI : Nonempty (CompletedGroupAlgebraIndexInClass G C) := inferInstance
  have hdir :
      Directed (α := CompletedGroupAlgebraIndexInClass G C) (· ≤ ·) fun U => U :=
    directed_openNormalSubgroupInClass (C := C) (G := G) hForm
  have hdense :
      DenseRange
        (S.inverseLimitLift
          (fun U : CompletedGroupAlgebraIndexInClass G C =>
            completedGroupAlgebraStageMapInClass C R G U)
          (completedGroupAlgebraStageMapInClass_compatibleMaps (R := R) (G := G) C hC)) :=
    S.denseRange_lift
      (fun U : CompletedGroupAlgebraIndexInClass G C =>
        completedGroupAlgebraStageMapInClass C R G U)
      (completedGroupAlgebraStageMapInClass_compatibleMaps (R := R) (G := G) C hC)
      (fun U => completedGroupAlgebraStageMapInClass_surjective (R := R) (G := G) C U)
      hdir
  simpa [S, toCompletedGroupAlgebraInClass] using hdense

@[simp]
theorem completedGroupAlgebraTransition_comp_projectionRingHom
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (completedGroupAlgebraTransition R G hUV).comp
        (completedGroupAlgebraProjectionRingHom R G V) =
      completedGroupAlgebraProjectionRingHom R G U := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraProjection_compatible (R := R) (G := G) x hUV

/-- The quotient map from the abstract group algebra `R[G]` to one finite stage `R[G/U]`. -/
def completedGroupAlgebraStageMap (R : Type u) (G : Type v) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    MonoidAlgebra R G →+* CompletedGroupAlgebraStage R G U :=
  MonoidAlgebra.mapDomainRingHom R
    (openNormalSubgroupInClassProj
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraStageMap_of
    (U : CompletedGroupAlgebraIndex G) (g : G) :
    completedGroupAlgebraStageMap R G U (MonoidAlgebra.of R G g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) 1 := by
  classical
  simp only [completedGroupAlgebraStageMap, MonoidAlgebra.of, MonoidAlgebra.single, MonoidHom.coe_mk,
  OneHom.coe_mk, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single]
  rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraStageMap_single
    (U : CompletedGroupAlgebraIndex G) (g : G) (r : R) :
    completedGroupAlgebraStageMap R G U (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) r := by
  classical
  simp only [completedGroupAlgebraStageMap, MonoidAlgebra.single, MonoidAlgebra.mapDomainRingHom_apply,
  Finsupp.mapDomain_single]
  rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraStageMap_smul
    (U : CompletedGroupAlgebraIndex G) (r : R) (x : MonoidAlgebra R G) :
    completedGroupAlgebraStageMap R G U (r • x) =
      r • completedGroupAlgebraStageMap R G U x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  simp only [completedGroupAlgebraStageMap, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one]

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraStageMap_algebraMap
    (U : CompletedGroupAlgebraIndex G) (r : R) :
    completedGroupAlgebraStageMap R G U (algebraMap R (MonoidAlgebra R G) r) =
      algebraMap R (CompletedGroupAlgebraStage R G U) r := by
  simp only [completedGroupAlgebraStageMap, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, MonoidAlgebra.mapDomainRingHom_apply, Finsupp.mapDomain_single, map_one]

omit [TopologicalSpace R] [IsTopologicalRing R] in
theorem completedGroupAlgebraStageMap_surjective (U : CompletedGroupAlgebraIndex G) :
    Function.Surjective (completedGroupAlgebraStageMap R G U) := by
  classical
  intro x
  induction x using Finsupp.induction with
  | zero =>
      exact ⟨0, map_zero (completedGroupAlgebraStageMap R G U)⟩
  | single_add q r x _ _ ih =>
      rcases openNormalSubgroupInClassProj_surjective
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U q with
        ⟨g, hg⟩
      rcases ih with ⟨y, hy⟩
      refine ⟨(MonoidAlgebra.single g r : MonoidAlgebra R G) + y, ?_⟩
      rw [map_add, completedGroupAlgebraStageMap_single, hy, hg]

omit [TopologicalSpace R] [IsTopologicalRing R] in
@[simp]
theorem completedGroupAlgebraStageMap_compatible
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (completedGroupAlgebraTransition R G hUV).comp (completedGroupAlgebraStageMap R G V) =
      completedGroupAlgebraStageMap R G U := by
  rw [completedGroupAlgebraTransition, completedGroupAlgebraStageMap,
    completedGroupAlgebraStageMap, ← MonoidAlgebra.mapDomainRingHom_comp]
  congr 1

/-- The finite-stage quotient maps form a compatible family into the completed group algebra
system. -/
theorem completedGroupAlgebraStageMap_compatibleMaps :
    (completedGroupAlgebraSystem R G).CompatibleMaps
      (fun U => completedGroupAlgebraStageMap R G U) := by
  intro U V hUV
  funext x
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageMap_compatible (R := R) (G := G) (U := U) (V := V) hUV))
    x

/-- The canonical map `R[G] -> [[R G]]`, obtained from all quotient maps `R[G] -> R[G/U]`. -/
def toCompletedGroupAlgebra (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : MonoidAlgebra R G) : Carrier R G :=
  ⟨fun U => completedGroupAlgebraStageMap R G U x, by
    intro U V hUV
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraStageMap_compatible (R := R) (G := G) (U := U) (V := V) hUV))
      x⟩

@[simp]
theorem completedGroupAlgebraProjection_toCompletedGroupAlgebra
    (U : CompletedGroupAlgebraIndex G) (x : MonoidAlgebra R G) :
    completedGroupAlgebraProjection R G U (toCompletedGroupAlgebra R G x) =
      completedGroupAlgebraStageMap R G U x := rfl

@[simp]
theorem toCompletedGroupAlgebra_smul (r : R) (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebra R G (r • x) =
      r • toCompletedGroupAlgebra R G x := by
  apply (completedGroupAlgebraSystem R G).ext
  intro U
  change completedGroupAlgebraProjection R G U (toCompletedGroupAlgebra R G (r • x)) =
    completedGroupAlgebraProjection R G U (r • toCompletedGroupAlgebra R G x)
  rw [completedGroupAlgebraProjection_toCompletedGroupAlgebra,
    completedGroupAlgebraProjection_smul,
    completedGroupAlgebraProjection_toCompletedGroupAlgebra,
    completedGroupAlgebraStageMap_smul]

/-- The canonical map `R[G] -> [[R G]]` as a ring homomorphism. -/
def toCompletedGroupAlgebraRingHom (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    MonoidAlgebra R G →+* Carrier R G where
  toFun := toCompletedGroupAlgebra R G
  map_zero' := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    exact map_zero (completedGroupAlgebraStageMap R G U)
  map_one' := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    exact map_one (completedGroupAlgebraStageMap R G U)
  map_add' x y := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    exact map_add (completedGroupAlgebraStageMap R G U) x y
  map_mul' x y := by
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    exact map_mul (completedGroupAlgebraStageMap R G U) x y

@[simp]
theorem completedGroupAlgebraToInClass_comp_toCompletedGroupAlgebra
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C) :
    (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C hC).comp
        (toCompletedGroupAlgebraRingHom R G) =
      toCompletedGroupAlgebraInClassRingHom C hC R G := by
  apply RingHom.ext
  intro x
  apply (completedGroupAlgebraSystemInClass C hC R G).ext
  intro U
  rfl

@[simp]
theorem completedGroupAlgebraFromInClassRingHom_comp_toCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hC : ProCGroups.FiniteGroupClass.FiniteOnly C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : IsProCGroup C G) :
    (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hC hForm hG).comp
        (toCompletedGroupAlgebraInClassRingHom C hC R G) =
      toCompletedGroupAlgebraRingHom R G := by
  rw [← completedGroupAlgebraToInClass_comp_toCompletedGroupAlgebra (R := R) (G := G) C hC,
    ← RingHom.comp_assoc, completedGroupAlgebraFromInClassRingHom_comp_toInClassRingHom]
  rfl

/-- The canonical map `R[G] -> [[R G]]` as an `R`-algebra homomorphism. -/
def toCompletedGroupAlgebraAlgHom (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    MonoidAlgebra R G →ₐ[R] Carrier R G where
  toRingHom := toCompletedGroupAlgebraRingHom R G
  commutes' := by
    intro r
    apply (completedGroupAlgebraSystem R G).ext
    intro U
    change completedGroupAlgebraStageMap R G U (algebraMap R (MonoidAlgebra R G) r) =
      algebraMap R (CompletedGroupAlgebraStage R G U) r
    exact completedGroupAlgebraStageMap_algebraMap (R := R) (G := G) U r

/-- The canonical map `R[G] -> [[R G]]` as an `R`-linear map. -/
def toCompletedGroupAlgebraLinearMap (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    MonoidAlgebra R G →ₗ[R] Carrier R G where
  toFun := toCompletedGroupAlgebra R G
  map_add' := by
    intro x y
    exact map_add (toCompletedGroupAlgebraRingHom R G) x y
  map_smul' := toCompletedGroupAlgebra_smul (R := R) (G := G)

@[simp]
theorem completedGroupAlgebraProjectionRingHom_comp_toCompletedGroupAlgebra
    (U : CompletedGroupAlgebraIndex G) :
    (completedGroupAlgebraProjectionRingHom R G U).comp
        (toCompletedGroupAlgebraRingHom R G) =
      completedGroupAlgebraStageMap R G U := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraProjection_toCompletedGroupAlgebra (R := R) (G := G) U x

omit G [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
end

end CompletedGroupAlgebra
