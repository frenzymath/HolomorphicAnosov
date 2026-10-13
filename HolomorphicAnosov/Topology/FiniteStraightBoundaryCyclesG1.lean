import HolomorphicAnosov.Topology.CairnsProjectionStripGeometryG1
import HolomorphicAnosov.Topology.FiniteStraightCarrierG1
import HolomorphicAnosov.Topology.FiniteDegreeTwoLinkListG1

/-!
# Boundary cycles of a finite straight surface

Gallier--Xu, Chapter 3: interval-link endpoints form a graph of degree two.
The exact planar realization identifies its graph components with the connected
components of the ambient frontier. The finite graph lemma then orders each
component into its original simple cycle.
-/
noncomputable section
open Set
namespace HolomorphicAnosov.Topology.CairnsStrip
open GallierXu

/-- Every frontier point of an exact straight surface belongs to a geometric
one-triangle edge. The existing vertex fan charts prove the interior assertion
before boundary edges have been enumerated. -/
theorem straightComplex_frontier_boundaryEdge_cover {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (p : Fin N → ℝ × ℝ)
    (hp : Function.Injective p) (hpure : PureTwo K) (hlinks : SurfaceLinks K)
    (hi : ∀ s ∈ K.faces, AffineIndependent ℝ (fun i : s ↦ p i))
    (hfaces : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))))
    (A : Set (ℝ × ℝ)) (hA : A = ⋃ s ∈ K.faces, convexHull ℝ (p '' (s : Set (Fin N)))) :
    ∀ y ∈ frontier A, ∃ u v, boundaryEdge K u v ∧ y ∈ segment ℝ (p u) (p v) := by
  obtain ⟨H,hH⟩ := straightCarrier_homeomorph K p hp hi hfaces A hA
  let f : C(↥(carrier K), Plane) :=
    ⟨fun x ↦ (shear 0).symm (H x).val,
      (shear 0).symm.continuous.comp (continuous_subtype_val.comp H.continuous)⟩
  have hf : Function.Injective f := (shear 0).symm.injective.comp
    (Subtype.val_injective.comp H.injective)
  have hrange : range f = (shear 0).symm '' A := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨(H x).val,(H x).property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨H.symm ⟨y,hy⟩,by change (shear 0).symm (H (H.symm ⟨y,hy⟩)).val = _; rw [H.apply_symm_apply]⟩
  intro y hy
  have hy' : (shear 0).symm y ∈ frontier (range f) := by
    rw [hrange,← (shear 0).symm.image_frontier]
    exact mem_image_of_mem _ hy
  obtain ⟨u,v,huv,x,hx,hxy⟩ := surface_frontier_boundaryEdges_cover K hpure hlinks f hf _ hy'
  refine ⟨u,v,huv,?_⟩
  have he : straightEval p x.val = y := by
    rw [← hH]
    exact (shear 0).symm.injective hxy
  rw [← he,← straightEval_image_segment]
  exact mem_image_of_mem _ hx

/-- A finite disjoint closed connected partition of the frontier of an exact
straight surface gives precisely its original simplicial boundary cycles,
with an exact geometric edge-union equality for each component. -/
theorem straightComplex_boundaryCycles_of_frontier_components {N b : ℕ}
    (K : AbstractSimplicialComplex (Fin N)) (p : Fin N → ℝ × ℝ)
    (hp : Function.Injective p) (hpure : PureTwo K) (hlinks : SurfaceLinks K)
    (hi : ∀ s ∈ K.faces, AffineIndependent ℝ (fun i : s ↦ p i))
    (hfaces : ∀ s ∈ K.faces, ∀ t ∈ K.faces,
      convexHull ℝ (p '' (s : Set (Fin N))) ∩ convexHull ℝ (p '' (t : Set (Fin N))) =
        convexHull ℝ (p '' ((s ∩ t : Finset (Fin N)) : Set (Fin N))))
    (A : Set (ℝ × ℝ)) (hA : A = ⋃ s ∈ K.faces, convexHull ℝ (p '' (s : Set (Fin N))))
    (C : Fin b → Set (ℝ × ℝ)) (hclosed : ∀ j, IsClosed (C j))
    (hconnected : ∀ j, IsConnected (C j))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hfront : frontier A = ⋃ j, C j) :
    ∃ B : Fin b → List (Fin N), BoundaryCycles K B ∧
      ∀ j, (⋃ u, ⋃ v, ⋃ (_ : cycleEdge (B j) u v), segment ℝ (p u) (p v)) = C j := by
  classical
  have hcover := straightComplex_frontier_boundaryEdge_cover K p hp hpure hlinks hi hfaces A hA
  have hedgesub (u v : Fin N) (huv : boundaryEdge K u v) : segment ℝ (p u) (p v) ⊆ frontier A := by
    rw [hA]
    exact straightComplex_boundaryEdge_frontier K p hp hpure hi hfaces u v huv
  have hcomponent (j : Fin b) (u v : Fin N) (huv : boundaryEdge K u v)
      (hm : (segment ℝ (p u) (p v) ∩ C j).Nonempty) : segment ℝ (p u) (p v) ⊆ C j :=
    finite_closed_partition_connected_subset C hclosed hdisjoint _
      (convex_segment (p u) (p v)).isPreconnected (hfront ▸ hedgesub u v huv) j hm
  let V : Fin b → Finset (Fin N) := fun j ↦ Finset.univ.filter (fun v ↦ p v ∈ C j)
  let R : Fin b → Fin N → Fin N → Prop := fun j u v ↦ boundaryEdge K u v ∧ p u ∈ C j
  have hV (j : Fin b) (v : Fin N) : v ∈ V j ↔ p v ∈ C j := by simp [V]
  have hRmem (j : Fin b) (u v : Fin N) (h : R j u v) : u ∈ V j ∧ v ∈ V j := by
    refine ⟨(hV j u).mpr h.2,(hV j v).mpr ?_⟩
    exact hcomponent j u v h.1 ⟨p u,left_mem_segment ℝ _ _,h.2⟩ (right_mem_segment ℝ _ _)
  have hRsymm (j : Fin b) : ∀ ⦃u v⦄, R j u v → R j v u := fun u v h ↦
    ⟨boundaryEdge_symm_g1 K h.1,(hV j v).mp (hRmem j u v h).2⟩
  have hCcover (j : Fin b) : C j = ⋃ u, ⋃ v, ⋃ (_ : R j u v), segment ℝ (p u) (p v) := by
    ext x
    constructor
    · intro hx
      obtain ⟨u,v,huv,hxseg⟩ := hcover x (hfront.symm ▸ mem_iUnion.mpr ⟨j,hx⟩)
      have hsub := hcomponent j u v huv ⟨x,hxseg,hx⟩
      exact mem_iUnion.mpr ⟨u,mem_iUnion.mpr ⟨v,mem_iUnion.mpr
        ⟨⟨huv,hsub (left_mem_segment ℝ _ _)⟩,hxseg⟩⟩⟩
    · intro hx
      obtain ⟨u,hx⟩ := mem_iUnion.mp hx
      obtain ⟨v,hx⟩ := mem_iUnion.mp hx
      obtain ⟨huv,hx⟩ := mem_iUnion.mp hx
      exact hcomponent j u v huv.1 ⟨p u,left_mem_segment ℝ _ _,huv.2⟩ hx
  have hVne (j : Fin b) : (V j).Nonempty := by
    obtain ⟨x,hx⟩ := (hconnected j).nonempty
    rw [hCcover j] at hx
    obtain ⟨u,hx⟩ := mem_iUnion.mp hx
    obtain ⟨v,hx⟩ := mem_iUnion.mp hx
    obtain ⟨huv,_⟩ := mem_iUnion.mp hx
    exact ⟨u,(hRmem j u v huv).1⟩
  have hneighbor (j : Fin b) (a : Fin N) (ha : a ∈ V j) : ∃ c, R j a c := by
    have hpa := (hV j a).mp ha
    obtain ⟨u,v,huv,hseg⟩ := hcover (p a) (hfront.symm ▸ mem_iUnion.mpr ⟨j,hpa⟩)
    have hae : a ∈ ({u,v} : Finset (Fin N)) := by
      by_contra hae
      apply straightComplex_vertex_notMem_hull K p hfaces a {u,v} huv.2.1 hae
      simpa only [Finset.coe_pair,Set.image_pair,convexHull_pair] using hseg
    rcases Finset.mem_insert.mp hae with rfl | hae
    · exact ⟨v,huv,hpa⟩
    · have he := Finset.mem_singleton.mp hae
      subst a
      exact ⟨u,boundaryEdge_symm_g1 K huv,hpa⟩
  have hdegree (j : Fin b) (a : Fin N) (ha : a ∈ V j) :
      ∃ c d, c ≠ d ∧ ∀ w, R j a w ↔ w = c ∨ w = d := by
    obtain ⟨c,hac⟩ := hneighbor j a ha
    obtain ⟨u,v,huv,he⟩ := surface_boundary_neighbors K hlinks a c hac.1
    exact ⟨u,v,huv,fun w ↦ by change (boundaryEdge K a w ∧ p a ∈ C j) ↔ _; simp only [he w,(hV j a).mp ha,and_true]⟩
  have hcycle (j : Fin b) : ∃ l : List (Fin N), l.Nodup ∧ 3 ≤ l.length ∧
      (∀ a, a ∈ l ↔ a ∈ V j) ∧ ∀ u v, R j u v ↔ cycleEdge l u v := by
    apply finite_degree_two_cycle (V j) (R j) (hVne j) (hRsymm j)
      (fun a h ↦ h.1.1 rfl) (hRmem j) (hdegree j)
    exact straightGraph_chainConnected K p hfaces (V j) (R j) (hRsymm j)
      (fun u v h ↦ h.1.2.1) (hneighbor j) (C j) (hconnected j).isPreconnected (hCcover j)
  choose B hnd hlen hvertices hcycle using hcycle
  refine ⟨B,⟨fun j ↦ ⟨hnd j,hlen j⟩,?_,?_⟩,?_⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro a hai haj
    have hia := (hV i a).mp ((hvertices i a).mp (List.mem_toFinset.mp hai))
    have hja := (hV j a).mp ((hvertices j a).mp (List.mem_toFinset.mp haj))
    exact Set.disjoint_left.mp (hdisjoint i j hij) hia hja
  · intro u v
    constructor
    · intro huv
      have hpu := hedgesub u v huv (left_mem_segment ℝ _ _)
      rw [hfront] at hpu
      obtain ⟨j,hj⟩ := mem_iUnion.mp hpu
      exact ⟨j,(hcycle j u v).mp ⟨huv,hj⟩⟩
    · rintro ⟨j,hj⟩
      exact ((hcycle j u v).mpr hj).1
  · intro j
    rw [hCcover j]
    simp_rw [hcycle j]

end HolomorphicAnosov.Topology.CairnsStrip
