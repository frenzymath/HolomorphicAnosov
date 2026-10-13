import HolomorphicAnosov.Topology.DiskChartOpenInteriorBoundary
import HolomorphicAnosov.Topology.HatcherPlanarDiskSphericalSeparation
import HolomorphicAnosov.Topology.OnePointCompactComplement
import HolomorphicAnosov.Topology.ConnectedComponentsTwoOpenRegions

noncomputable section
open Set Metric
namespace HolomorphicAnosov

/-- A planar disk chart identifies the two complementary regions of its boundary.
Source: Hatcher, Proposition 2B.1 and Theorem 2B.3. Invariance of domain
identifies the chart's open disk with the ambient interior. The spherical
nonseparation assertion and compact-complement comparison show that the exterior
is connected. Regular closedness identifies the two common frontiers. -/
theorem diskChart_two_regions (K R C : Set ℂ)
    (hK : IsCompact K) (hregular : closure (interior K) = K)
    (hne : (interior K).Nonempty)
    (hRK : R ⊆ K) (hCK : C ⊆ K)
    (H : K ≃ₜ closedBall (0 : ℂ) 1)
    (hR : H '' {z : K | (z : ℂ) ∈ R} =
      {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ ball (0 : ℂ) 1})
    (hC : H '' {z : K | (z : ℂ) ∈ C} =
      {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ sphere (0 : ℂ) 1}) :
    (fun z : ℂ ↦ connectedComponentIn Cᶜ z) '' Cᶜ = {interior K, Kᶜ} ∧
      IsConnected (interior K) ∧ IsConnected Kᶜ ∧
      IsOpen (interior K) ∧ IsOpen Kᶜ ∧
      Bornology.IsBounded (interior K) ∧ ¬ Bornology.IsBounded Kᶜ ∧
      closure (interior K) = K ∧ frontier (interior K) = C ∧ frontier Kᶜ = C := by
  have hRi (z : K) : (z : ℂ) ∈ R ↔ (H z : ℂ) ∈ ball (0 : ℂ) 1 := by
    change z ∈ {z : K | (z : ℂ) ∈ R} ↔ H z ∈ {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ ball (0 : ℂ) 1}
    rw [← hR, H.injective.mem_set_image]
  have hCi (z : K) : (z : ℂ) ∈ C ↔ (H z : ℂ) ∈ sphere (0 : ℂ) 1 := by
    change z ∈ {z : K | (z : ℂ) ∈ C} ↔ H z ∈ {w : closedBall (0 : ℂ) 1 | (w : ℂ) ∈ sphere (0 : ℂ) 1}
    rw [← hC, H.injective.mem_set_image]
  have hopenR := (disk_chart_open_interior_boundary K R C hRK hCK H hR hC).1
  have hRint : R = interior K := by
    apply le_antisymm (hopenR.subset_interior_iff.mpr hRK)
    let f : interior K → ℂ := fun z ↦ H ⟨z, interior_subset z.property⟩
    have hf : Continuous f := by fun_prop
    have hfi : Function.Injective f := by
      intro x y h
      exact Subtype.ext (congrArg (fun z : K ↦ (z : ℂ)) (H.injective (Subtype.ext h)))
    have hfo : IsOpen (range f) := complex_planar_open_range _ isOpen_interior f hf hfi
    have hsub : range f ⊆ closedBall (0 : ℂ) 1 := by
      rintro w ⟨z, rfl⟩
      exact (H ⟨z, interior_subset z.property⟩).property
    have hsubint := hfo.subset_interior_iff.mpr hsub
    rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hsubint
    intro z hz
    exact (hRi ⟨z, interior_subset hz⟩).mpr (hsubint ⟨⟨z, hz⟩, rfl⟩)
  have hCeq : C = K \ interior K := by
    rw [← hRint]
    ext z
    constructor
    · intro hz
      refine ⟨hCK hz, ?_⟩
      intro hzR
      have hs := (hCi ⟨z, hCK hz⟩).mp hz
      have hb := (hRi ⟨z, hCK hz⟩).mp hzR
      exact (ne_of_lt hb) hs
    · rintro ⟨hzK, hzR⟩
      apply (hCi ⟨z, hzK⟩).mpr
      have hb := (H ⟨z, hzK⟩).property
      have hn : ¬ (H ⟨z, hzK⟩ : ℂ) ∈ ball (0 : ℂ) 1 :=
        fun h ↦ hzR ((hRi ⟨z, hzK⟩).mpr h)
      exact le_antisymm hb (le_of_not_gt hn)
  have hconR : IsConnected R := by
    let f : ball (0 : ℂ) 1 → ℂ := fun z ↦ H.symm ⟨z, ball_subset_closedBall z.property⟩
    have hf : Continuous f := by fun_prop
    have hrange : range f = R := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact (hRi _).mpr (by rw [H.apply_symm_apply]; exact w.property)
      · intro hz
        have hw := (hRi ⟨z, hRK hz⟩).mp hz
        refine ⟨⟨H ⟨z, hRK hz⟩, hw⟩, ?_⟩
        simp [f]
    rw [← hrange]
    have : PreconnectedSpace (ball (0 : ℂ) 1) :=
      isPreconnected_iff_preconnectedSpace.mp (convex_ball _ _).isPreconnected
    exact ⟨by simpa [hrange, hRint] using hne, isPreconnected_range hf⟩
  have hconE : IsPreconnected Kᶜ := by
    let e := Complex.orthonormalBasisOneI.repr.symm
    let g : closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℂ := fun z ↦
      H.symm ⟨e z, by
        simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using z.property⟩
    have hg : Continuous g := by fun_prop
    have hgi : Function.Injective g := by
      intro x y h
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val (H.symm.injective (Subtype.ext h))
    have hgrange : range g = K := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        exact (H.symm _).property
      · intro hz
        refine ⟨⟨e.symm (H ⟨z, hz⟩), ?_⟩, ?_⟩
        · simpa only [mem_closedBall, dist_zero_right, LinearIsometryEquiv.norm_map] using (H ⟨z, hz⟩).property
        · simp [g]
    have hS := (Topology.hatcher_planar_disk_spherical_separation 0 1 (by norm_num) g hg hgi).1
    rw [hgrange] at hS
    apply isPreconnected_of_forall_pair
    intro x hx y hy
    refine ⟨connectedComponentIn Kᶜ x, connectedComponentIn_subset _ _,
      mem_connectedComponentIn hx, ?_, isPreconnected_connectedComponentIn⟩
    apply Topology.onePoint_complex_complement_component hK hx hy
    exact hS.subset_connectedComponentIn (by simpa using hx) subset_rfl (by simpa using hy)
  have hunbounded : ¬ Bornology.IsBounded Kᶜ := by
    intro h
    have hu := hK.isBounded.union h
    rw [union_compl_self] at hu
    exact NormedSpace.unbounded_univ ℝ ℂ hu
  have hEne : Kᶜ.Nonempty := by
    by_contra hn
    exact hunbounded (by simp [Set.not_nonempty_iff_eq_empty.mp hn])
  have hconnI : IsConnected (interior K) := hRint ▸ hconR
  have hconnE : IsConnected Kᶜ := ⟨hEne, hconE⟩
  have hcover : interior K ∪ Kᶜ = Cᶜ := by rw [hCeq]; tauto_set
  have hfrontK : frontier K = C := by rw [frontier, hK.isClosed.closure_eq, hCeq]
  refine ⟨?_, hconnI, hconnE, isOpen_interior, hK.isClosed.isOpen_compl,
    hK.isBounded.subset interior_subset, hunbounded, hregular, ?_, ?_⟩
  · rw [← hcover]
    exact connectedComponentsIn_two_open_regions hconnI hconnE isOpen_interior
      hK.isClosed.isOpen_compl (disjoint_compl_right.mono_left interior_subset)
  · rw [frontier, hregular, interior_interior, ← hCeq]
  · rw [frontier_compl, hfrontK]
end HolomorphicAnosov
