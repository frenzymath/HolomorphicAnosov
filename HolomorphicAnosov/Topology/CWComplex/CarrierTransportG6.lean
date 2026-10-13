import Mathlib.Topology.CWComplex.Classical.Subcomplex

namespace HolomorphicAnosov
open _root_.Topology Set Metric

/-- Restrict a characteristic map to the actual CW carrier on its closed disk.
Outside that disk its total forward function uses the supplied carrier point. -/
noncomputable def cwCarrierMapG6
    {X : Type*} [TopologicalSpace X] (C : Set X) [CWComplex C]
    (c0 : C) (n : ℕ) (i : RelCWComplex.cell C n) : PartialEquiv (Fin n → ℝ) C := by
  classical
  let f : (Fin n → ℝ) → C := fun z ↦
    if h : z ∈ closedBall 0 1 then
      ⟨RelCWComplex.map n i z, RelCWComplex.closedCell_subset_complex n i ⟨z, h, rfl⟩⟩
    else c0
  refine {
    toFun := f
    invFun := fun x ↦ (RelCWComplex.map n i).symm x.val
    source := ball 0 1
    target := Subtype.val ⁻¹' (RelCWComplex.map n i).target
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_ }
  · intro z hz
    have hc := ball_subset_closedBall hz
    simp only [mem_preimage, f, dite_eq_left hc]
    exact (RelCWComplex.map n i).map_source ((RelCWComplex.source_eq n i).symm ▸ hz)
  · intro x hx
    exact RelCWComplex.source_eq n i ▸ (RelCWComplex.map n i).map_target hx
  · intro z hz
    have hc := ball_subset_closedBall hz
    simp only [f, dite_eq_left hc]
    exact (RelCWComplex.map n i).left_inv ((RelCWComplex.source_eq n i).symm ▸ hz)
  · intro x hx
    have hz : (RelCWComplex.map n i).symm x.val ∈ closedBall 0 1 :=
      ball_subset_closedBall (RelCWComplex.source_eq n i ▸ (RelCWComplex.map n i).map_target hx)
    apply Subtype.ext
    simp only [f, dite_eq_left hz]
    exact (RelCWComplex.map n i).right_inv hx

theorem cwCarrierMapG6_coe
    {X : Type*} [TopologicalSpace X] (C : Set X) [CWComplex C]
    (c0 : C) (n : ℕ) (i : RelCWComplex.cell C n)
    {z : Fin n → ℝ} (hz : z ∈ closedBall 0 1) :
    (cwCarrierMapG6 C c0 n i z).val = RelCWComplex.map n i z := by
  classical
  simp only [cwCarrierMapG6, PartialEquiv.coe_mk, dite_eq_left hz]

theorem cwCarrierMapG6_image
    {X : Type*} [TopologicalSpace X] (C : Set X) [CWComplex C]
    (c0 : C) (n : ℕ) (i : RelCWComplex.cell C n)
    (S : Set (Fin n → ℝ)) (hS : S ⊆ closedBall 0 1) :
    cwCarrierMapG6 C c0 n i '' S =
      Subtype.val ⁻¹' ((RelCWComplex.map n i) '' S) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (cwCarrierMapG6_coe C c0 n i (hS hz)).symm⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨z, hz, Subtype.ext ((cwCarrierMapG6_coe C c0 n i (hS hz)).trans hzx)⟩

/-- Transport an arbitrary classical CW structure to its literal carrier subtype.
Source: Hatcher, Algebraic Topology, Appendix A.2 p.521 and the closed-cell criterion p.523.
Keep the original cell labels and restrict each characteristic map on its closed disk. Outside
that disk the total map takes the supplied carrier point. The native partial equivalence laws
remain unchanged on their sources. The old finite frontier witnesses transfer by preimage, and
the weak topology transfers through the closed subtype embedding. No finiteness condition is
added, and the carrier retains its original subspace topology. -/
@[instance_reducible]
noncomputable def cwCarrierStructureG6
    {X : Type*} [TopologicalSpace X] [T2Space X] (C : Set X) [CWComplex C]
    (c0 : C) : CWComplex (Set.univ : Set C) := by
  classical
  refine {
    cell := RelCWComplex.cell C
    map := cwCarrierMapG6 C c0
    source_eq := fun _ _ ↦ rfl
    continuousOn := ?_
    continuousOn_symm := ?_
    pairwiseDisjoint' := ?_
    mapsTo' := ?_
    closed' := ?_
    union' := ?_ }
  · intro n i
    apply continuousOn_iff_continuous_domRestrict.mpr
    apply Continuous.subtype_mk
    have h := (RelCWComplex.continuousOn n i).domRestrict
    convert h using 1
    funext z
    exact cwCarrierMapG6_coe C c0 n i z.property
  · intro n i
    exact (RelCWComplex.continuousOn_symm n i).comp
      continuous_subtype_val.continuousOn (fun _ hx ↦ hx)
  · intro a _ b _ hab
    dsimp only [Function.onFun]
    rw [cwCarrierMapG6_image C c0 a.1 a.2 _ ball_subset_closedBall,
      cwCarrierMapG6_image C c0 b.1 b.2 _ ball_subset_closedBall]
    exact (RelCWComplex.disjoint_openCell_of_ne hab).preimage _
  · intro n i
    obtain ⟨J, hJ⟩ := CWComplex.mapsTo n i
    refine ⟨J, ?_⟩
    intro z hz
    have hh := hJ hz
    simp only [mem_iUnion] at hh ⊢
    obtain ⟨m, hm, j, hjJ, hj⟩ := hh
    refine ⟨m, hm, j, hjJ, ?_⟩
    rw [cwCarrierMapG6_image C c0 m j _ (Subset.refl _)]
    change (cwCarrierMapG6 C c0 n i z).val ∈ RelCWComplex.closedCell m j
    rwa [cwCarrierMapG6_coe C c0 n i (sphere_subset_closedBall hz)]
  · intro A _ hA
    have hclosed : IsClosed (Subtype.val '' A : Set X) := by
      apply (CWComplex.closed C (Subtype.val '' A)
        (by rintro _ ⟨x, _, rfl⟩; exact x.property)).mpr
      intro n i
      have h := hA n i
      rw [cwCarrierMapG6_image C c0 n i _ (Subset.refl _)] at h
      have heq : Subtype.val '' (A ∩ Subtype.val ⁻¹' RelCWComplex.closedCell n i) =
          (Subtype.val '' A : Set X) ∩ RelCWComplex.closedCell n i := by
        ext x
        constructor
        · rintro ⟨z, ⟨hzA, hzc⟩, rfl⟩
          exact ⟨⟨z, hzA, rfl⟩, hzc⟩
        · rintro ⟨⟨z, hzA, rfl⟩, hzc⟩
          exact ⟨z, ⟨hzA, hzc⟩, rfl⟩
      rw [← heq]
      exact (RelCWComplex.isClosed (C := C) (D := (∅ : Set X))).isClosedMap_subtype_val _ h
    have hpre : Subtype.val ⁻¹' (Subtype.val '' A : Set X) = A :=
      Set.preimage_image_eq A Subtype.val_injective
    rw [← hpre]
    exact hclosed.preimage continuous_subtype_val
  · ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    have hx : x.val ∈ ⋃ (n : ℕ) (j : RelCWComplex.cell C n), RelCWComplex.closedCell n j := by
      rw [CWComplex.union]
      exact x.property
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hn
    refine ⟨n, i, ?_⟩
    rw [cwCarrierMapG6_image C c0 n i _ (Subset.refl _)]
    exact hi

end HolomorphicAnosov
