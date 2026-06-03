import FenchelNielsenZomorrodian.Profinite.FGroup

/-
PUBLIC_PAGE_SNAPSHOT
generated_at: 2026-05-27T09:47:29+09:00
lean_source: lean4/FenchelNielsenZomorrodian/Profinite/CharacteristicClosure.lean
translation_root: data/translation
purpose: identifies the local data snapshot used to build pages/
placement: after imports, never before imports
-/
/-!
# Characteristic closure of open normal subgroups

Turns torsion-free open normal subgroups, and bounded-derived-length quotient data, into characteristic open subgroups using the finite number of open subgroups of fixed index.
-/

namespace FenchelNielsen

universe u

open scoped Topology
open ProCGroups.FiniteGeneration
open ProCGroups.FiniteStepSolvableQuotients

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Pull an open normal subgroup back along a continuous automorphism. -/
noncomputable def openNormalAutComap (φ : G ≃ₜ* G)
    (U : OpenNormalSubgroup G) : OpenNormalSubgroup G :=
  ProCGroups.OpenNormalSubgroup.comap φ.toContinuousMonoidHom.toMonoidHom
    φ.continuous_toFun U

@[local simp]
theorem mem_openNormalAutComap {φ : G ≃ₜ* G}
    {U : OpenNormalSubgroup G} {x : G} :
    x ∈ openNormalAutComap φ U ↔ φ x ∈ U :=
  Iff.rfl

/-- The automorphic orbit of an open normal subgroup, viewed as ordinary subgroups. -/
noncomputable def openNormalAutComapOrbitSubgroups
    (U : OpenNormalSubgroup G) : Set (Subgroup G) :=
  Set.range fun φ : G ≃ₜ* G =>
    ((openNormalAutComap φ U : OpenNormalSubgroup G) : Subgroup G)

variable [IsTopologicalGroup G] [CompactSpace G]

/-- The automorphic orbit of an open normal subgroup is finite when open subgroups of fixed index
are finite in number. -/
theorem openNormalAutComapOrbitSubgroups_finite
    (hfin : HasFiniteOpenSubgroupsOfIndex G) (U : OpenNormalSubgroup G) :
    (openNormalAutComapOrbitSubgroups U).Finite := by
  classical
  let n := Nat.card (G ⧸ (U : Subgroup G))
  refine (finite_openSubgroupsOfIndexLE_of_hasFiniteOpenSubgroupsOfIndex
      (G := G) hfin n).subset ?_
  intro V hV
  rcases hV with ⟨φ, hφ⟩
  rw [← hφ]
  have hopen :
      IsOpen
        (((openNormalAutComap φ U : OpenNormalSubgroup G) : Subgroup G) :
          Set G) :=
    ProCGroups.openNormalSubgroup_isOpen (G := G) (openNormalAutComap φ U)
  have hfinite :
      Finite
        (G ⧸ ((openNormalAutComap φ U : OpenNormalSubgroup G) :
          Subgroup G)) :=
    Subgroup.quotient_finite_of_isOpen _ hopen
  refine ⟨hopen, hfinite, ?_⟩
  simpa [openNormalAutComap, Subgroup.index_eq_card, n] using
    (Subgroup.index_comap_of_surjective
      (H := (U : Subgroup G)) φ.surjective).le

/-- The intersection of the automorphic orbit of an open normal subgroup is open. -/
theorem openNormalAutComapOrbitSubgroups_open
    (hfin : HasFiniteOpenSubgroupsOfIndex G) (U : OpenNormalSubgroup G) :
    IsOpen ((sInf (openNormalAutComapOrbitSubgroups U) : Subgroup G) :
      Set G) := by
  apply ProCGroups.FiniteGeneration.Subgroup.isOpen_sInf_of_finite
  · exact openNormalAutComapOrbitSubgroups_finite (G := G) hfin U
  · intro V hV
    rcases hV with ⟨φ, hφ⟩
    rw [← hφ]
    exact ProCGroups.openNormalSubgroup_isOpen (G := G) (openNormalAutComap φ U)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The intersection of the automorphic orbit of an open normal subgroup is normal. -/
theorem openNormalAutComapOrbitSubgroups_normal (U : OpenNormalSubgroup G) :
    (sInf (openNormalAutComapOrbitSubgroups U)).Normal := by
  rw [sInf_eq_iInf']
  exact Subgroup.normal_iInf_normal fun V : openNormalAutComapOrbitSubgroups U => by
    rcases V.2 with ⟨φ, hφ⟩
    rw [← hφ]
    exact (openNormalAutComap φ U).isNormal'

/-- The characteristic closure of an open normal subgroup in a finitely generated profinite group. -/
noncomputable def openNormalCharacteristicClosure
    (hfin : HasFiniteOpenSubgroupsOfIndex G) (U : OpenNormalSubgroup G) :
    OpenNormalSubgroup G where
  toOpenSubgroup :=
    { toSubgroup := sInf (openNormalAutComapOrbitSubgroups U)
      isOpen' := openNormalAutComapOrbitSubgroups_open (G := G) hfin U }
  isNormal' := openNormalAutComapOrbitSubgroups_normal (G := G) U

/-- The characteristic closure of an open normal subgroup is contained in the original subgroup. -/
theorem openNormalCharacteristicClosure_le
    (hfin : HasFiniteOpenSubgroupsOfIndex G) (U : OpenNormalSubgroup G) :
    (openNormalCharacteristicClosure (G := G) hfin U : Subgroup G) ≤
      (U : Subgroup G) := by
  intro x hx
  have hx' : x ∈ sInf (openNormalAutComapOrbitSubgroups U) := hx
  rw [Subgroup.mem_sInf] at hx'
  exact hx' _ ⟨ContinuousMulEquiv.refl G, by ext y; simp only [openNormalAutComap, ContinuousMonoidHom.coe_toMonoidHom,
  ProCGroups.OpenNormalSubgroup.toSubgroup_comap, Subgroup.mem_comap, MonoidHom.coe_coe,
  ContinuousMulEquiv.toContinuousMonoidHom_apply, ContinuousMulEquiv.refl_apply, OpenSubgroup.mem_toSubgroup]⟩

/-- The characteristic closure is topologically characteristic. -/
theorem openNormalCharacteristicClosure_characteristic
    (hfin : HasFiniteOpenSubgroupsOfIndex G) (U : OpenNormalSubgroup G) :
    IsTopologicallyCharacteristic G
      (openNormalCharacteristicClosure (G := G) hfin U : Subgroup G) := by
  intro ψ g
  constructor
  · intro hg
    change ψ g ∈ sInf (openNormalAutComapOrbitSubgroups U) at hg
    change g ∈ sInf (openNormalAutComapOrbitSubgroups U)
    rw [Subgroup.mem_sInf] at hg ⊢
    intro V hV
    rcases hV with ⟨φ, hφ⟩
    rw [← hφ]
    have hmem :
        ψ g ∈ (openNormalAutComap (ψ.symm.trans φ) U :
          OpenNormalSubgroup G) :=
      hg _ ⟨ψ.symm.trans φ, rfl⟩
    simpa [openNormalAutComap] using hmem
  · intro hg
    change g ∈ sInf (openNormalAutComapOrbitSubgroups U) at hg
    change ψ g ∈ sInf (openNormalAutComapOrbitSubgroups U)
    rw [Subgroup.mem_sInf] at hg ⊢
    intro V hV
    rcases hV with ⟨φ, hφ⟩
    rw [← hφ]
    have hmem :
        g ∈ (openNormalAutComap (ψ.trans φ) U : OpenNormalSubgroup G) :=
      hg _ ⟨ψ.trans φ, rfl⟩
    simpa [openNormalAutComap] using hmem

/-- The same closure bundled as a profinite open characteristic subgroup. -/
noncomputable def profiniteOpenCharacteristicClosure
    (hfin : HasFiniteOpenSubgroupsOfIndex G) (U : OpenNormalSubgroup G) :
    ProfiniteOpenCharacteristicSubgroup G :=
  ⟨openNormalCharacteristicClosure (G := G) hfin U,
    openNormalCharacteristicClosure_characteristic (G := G) hfin U⟩

theorem profiniteOpenCharacteristicClosure_torsionFree
    (hfin : HasFiniteOpenSubgroupsOfIndex G) (U : OpenNormalSubgroup G)
    (htf : ProfiniteOpenNormalSubgroupTorsionFree G U) :
    ProfiniteOpenNormalSubgroupTorsionFree G
      (profiniteOpenCharacteristicClosure (G := G) hfin U).toOpenNormalSubgroup := by
  intro x hx hfinord
  exact htf x (openNormalCharacteristicClosure_le (G := G) hfin U hx) hfinord


/-- Characteristic-closure existence package: in a finitely generated profinite group, any
torsion-free open normal subgroup can be replaced by a torsion-free open characteristic subgroup. -/
theorem exists_torsionFree_openCharacteristicSubgroup_of_exists_torsionFree_openNormalSubgroup
    (hfin : HasFiniteOpenSubgroupsOfIndex G)
    (h : ∃ U : OpenNormalSubgroup G, ProfiniteOpenNormalSubgroupTorsionFree G U) :
    ∃ U : ProfiniteOpenCharacteristicSubgroup G,
      ProfiniteOpenNormalSubgroupTorsionFree G U.toOpenNormalSubgroup := by
  rcases h with ⟨U, htf⟩
  exact
    ⟨profiniteOpenCharacteristicClosure (G := G) hfin U,
      profiniteOpenCharacteristicClosure_torsionFree (G := G) hfin U htf⟩

theorem profiniteOpenCharacteristicClosure_derivedLength
    (hfin : HasFiniteOpenSubgroupsOfIndex G) (U : OpenNormalSubgroup G) {m : ℕ}
    (hquot : ProfiniteOpenNormalQuotientHasDerivedLengthAtMost G U m) :
    ProfiniteOpenCharacteristicQuotientHasDerivedLengthAtMost G
      (profiniteOpenCharacteristicClosure (G := G) hfin U) m := by
  have hDleU : profiniteDerivedSeries G m ≤ (U : Subgroup G) :=
    ProfiniteOpenNormalQuotientHasDerivedLengthAtMost.topDerived_le U hquot
  apply ProfiniteOpenNormalQuotientHasDerivedLengthAtMost.of_topDerived_le
  intro x hx
  change x ∈ sInf (openNormalAutComapOrbitSubgroups U)
  rw [Subgroup.mem_sInf]
  intro V hV
  rcases hV with ⟨φ, hφ⟩
  rw [← hφ]
  change φ x ∈ U
  exact hDleU ((topDerivedTop_le_comap (f := φ.toContinuousMonoidHom) (m := m)) hx)


theorem hasTorsionFreeOpenCharacteristicSubgroupQuotientDerivedLengthAtMost_of_normal
    (hfin : HasFiniteOpenSubgroupsOfIndex G) {m : ℕ}
    (h :
      HasTorsionFreeOpenNormalSubgroupQuotientDerivedLengthAtMost G m) :
    HasTorsionFreeOpenCharacteristicSubgroupQuotientDerivedLengthAtMost G m := by
  rcases h with ⟨U, htf, hquot⟩
  refine
    ⟨profiniteOpenCharacteristicClosure (G := G) hfin U,
      profiniteOpenCharacteristicClosure_torsionFree (G := G) hfin U htf,
      profiniteOpenCharacteristicClosure_derivedLength (G := G) hfin U hquot⟩

end FenchelNielsen
