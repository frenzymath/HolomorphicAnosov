import HolomorphicAnosov.Topology.GallierXuOrientableSurfaceNormalForm
import Mathlib.Analysis.InnerProductSpace.PiL2
import HolomorphicAnosov.Topology.FinitePlaneProjection
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Topology.Connected.PathConnected
import HolomorphicAnosov.Topology.CairnsProjectionStripGeometryG1
import HolomorphicAnosov.Topology.FiniteStraightCarrierG1
import HolomorphicAnosov.Topology.FiniteDegreeTwoLinkListG1
import HolomorphicAnosov.Topology.FiniteStraightBoundaryCyclesG1
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusFrontierDecomposition
import HolomorphicAnosov.Topology.CairnsPolygonalAnnulusFrontierDisjoint

/-!
# Finite triangulation of a polygonal exterior annulus

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
preliminary 2(B), printed p.860 (physical pp.2--3). The paper uses the finite
polygonal subdivision implicitly and does not state this carrier-level adapter.
The proposition below records the exact finite simplicial data needed by the
Gallier--Xu normal-form theorem, together with its geometric carrier map.
-/

open Set

namespace HolomorphicAnosov.Topology

open GallierXu

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- A finite straight triangulation of the exterior of `D` inside `R`, with
the two geometric boundary cycles retained as simplicial subcomplexes.

The result is the finite-strip construction: choose a generic projection,
cut into finitely many strips, subdivide all common vertical sides, and fan
triangulate each nondegenerate convex strip cell. The carrier homeomorphism
records that this abstract complex is a triangulation of the literal subtype
`R \ interior D`; the two image equalities retain the polygon and rectangle
boundary components. The construction is the geometric proposition needed by
the subsequent normal-form and quotient-cylinder argument, and is therefore a
named theorem-level proof boundary rather than an anonymous `sorry` in that
consumer.
-/
theorem cairns_polygonal_annulus_triangulation
    (D R : Set Plane)
    (hcompact : IsCompact D)
    (hregular : closure (interior D) = D)
    (_hinterior_nonempty : (interior D).Nonempty)
    (_hinterior_path : IsPathConnected (interior D))
    (hexterior_path : IsPathConnected Dᶜ)
    (hpolygon : ∃ n : ℕ, 3 ≤ n ∧ ∃ P : Polygon Plane n,
      Function.Injective P ∧
      (∀ i j : Fin n, i ≠ j →
        P.edgeSet ℝ i ∩ P.edgeSet ℝ j ⊆
          ({P i, P (finRotate n i)} ∩ {P j, P (finRotate n j)} : Set Plane)) ∧
      frontier D = P.boundary ℝ)
    (hrectangle : ∃ e : Plane ≃ᵃⁱ[ℝ] Plane, ∃ a b : Fin 2 → ℝ,
      (∀ i, a i < b i) ∧
      R = e '' {x : Plane | ∀ i, a i ≤ x i ∧ x i ≤ b i})
    (hcontain : D ⊆ interior R) :
    ∃ N : ℕ, ∃ K : AbstractSimplicialComplex (Fin N),
      ∃ B : Fin 2 → List (Fin N),
      ∃ o : (s : Triangle K) → Fin 3 ≃ ↥s.val,
        PureTwo K ∧
        IsConnected (carrier K) ∧
        (∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2) ∧
        SurfaceLinks K ∧
        BoundaryCycles K B ∧
        Oriented (trianglePresentation K o) ∧
        ∃ H : ↥(R \ interior D) ≃ₜ ↥(carrier K),
          H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier D} =
            cycleCarrier (B 0) ∧
          H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
            cycleCarrier (B 1) := by
  have hpoly : ∃ n : ℕ, 3 ≤ n ∧ ∃ P : Polygon Plane n,
      Function.Injective P ∧ frontier D = P.boundary ℝ := by
    obtain ⟨n,hn,P,hP,_,hfront⟩ := hpolygon
    exact ⟨n,hn,P,hP,hfront⟩
  obtain ⟨t,F,T,hT,hcover⟩ := CairnsStrip.polygonal_annulus_finite_triangle_cover
    D R hcompact.isClosed hpoly hrectangle hcontain
  let τ := CairnsStrip.SelectedTriangle (CairnsStrip.shear t '' D)
    (CairnsStrip.shear t '' R) T F
  let vertices : τ → Fin 3 → ℝ × ℝ := CairnsStrip.selectedTriangleVertices
  have hindependent (s : τ) : AffineIndependent ℝ (vertices s) :=
    CairnsStrip.selectedTriangle_independent s
  have hinter (s u : τ) : convexHull ℝ (Set.range (vertices s)) ∩
      convexHull ℝ (Set.range (vertices u)) =
      convexHull ℝ (Set.range (vertices s) ∩ Set.range (vertices u)) :=
    CairnsStrip.selectedTriangle_inter _ _ T F hT s u
  obtain ⟨N,K,p,hp,hpure,hface,hfaces,hunion,H,hH⟩ :=
    CairnsStrip.finiteTriangleFamily_realization vertices hindependent hinter
  let HA : ↥(carrier K) ≃ₜ ↥(R \ interior D) :=
    (H.trans (Homeomorph.setCongr hcover)).trans ((CairnsStrip.shear t).image (R \ interior D)).symm
  have hAconnected : IsConnected (R \ interior D) :=
    CairnsStrip.polygonal_annulus_connected D R hcompact.isClosed hexterior_path.isConnected hrectangle hcontain
  have hKconnected : IsConnected (carrier K) := by
    have : ConnectedSpace ↥(R \ interior D) := isConnected_iff_connectedSpace.mp hAconnected
    apply isConnected_iff_connectedSpace.mpr
    apply connectedSpace_iff_univ.mpr
    have hc := (isConnected_univ : IsConnected (Set.univ : Set ↥(R \ interior D))).image
      HA.symm HA.symm.continuous.continuousOn
    simpa only [Set.image_univ,HA.symm.surjective.range_eq] using hc
  have hincidence := CairnsStrip.straightComplex_edge_incidence K p hpure hface hfaces
  obtain ⟨o,horiented⟩ := CairnsStrip.straightComplex_exists_orientation K p hface hfaces
  let A := CairnsStrip.shear t '' (R \ interior D)
  have hA : A = ⋃ s ∈ K.faces, convexHull ℝ (p '' (s : Set (Fin N))) :=
    (hunion.trans hcover).symm
  have hlocal := CairnsStrip.punctured_neighborhood_image (CairnsStrip.shear t)
    (R \ interior D) (CairnsStrip.polygonal_annulus_punctured_neighborhood D R
      hcompact.isClosed hregular hpolygon hrectangle hcontain)
  have hvertex (v : Fin N) : p v ∈ A := by
    rw [hA]
    exact mem_iUnion.mpr ⟨{v},mem_iUnion.mpr ⟨K.singleton_mem v,
      subset_convexHull ℝ _ (mem_image_of_mem p (by simp))⟩⟩
  have hconn := CairnsStrip.straightComplex_link_chainConnected K p hp hfaces A hA
    (by
      intro v W hW hvW
      obtain ⟨U,hU,hvU,hUW,hc⟩ := hlocal (p v) (hvertex v) W hW hvW
      exact ⟨U,hU,hvU,hUW,hc.isPreconnected⟩)
  have hlinks : SurfaceLinks K := surfaceLinks_of_link_chainConnected K hpure
    (fun e he ↦ (hincidence e he).elim (fun h ↦ by omega) (fun h ↦ by omega)) hconn
  obtain ⟨e,a,b,hab,hReq⟩ := hrectangle
  have hRcompact : IsCompact R := hReq ▸ CairnsStrip.affine_rectangle_compact e a b
  have hinnerConnected : IsConnected (frontier D) := by
    obtain ⟨n,hn,P,_,_,hf⟩ := hpolygon
    rw [hf]
    exact (CairnsStrip.polygon_boundary_isPathConnected (by omega : 0 < n) P).isConnected
  have houterConnected : IsConnected (frontier R) := by
    obtain ⟨P,_,_,hf⟩ := CairnsStrip.affine_rectangle_polygon e a b hab
    rw [hReq,hf]
    exact (CairnsStrip.polygon_boundary_isPathConnected (by decide : 0 < 4) P).isConnected
  let C : Fin 2 → Set (ℝ × ℝ) :=
    ![CairnsStrip.shear t '' frontier D,CairnsStrip.shear t '' frontier R]
  have hCclosed (j : Fin 2) : IsClosed (C j) := by
    fin_cases j <;> exact (CairnsStrip.shear t).isClosedMap _ isClosed_frontier
  have hCconnected (j : Fin 2) : IsConnected (C j) := by
    fin_cases j
    · exact hinnerConnected.image _ (CairnsStrip.shear t).continuous.continuousOn
    · exact houterConnected.image _ (CairnsStrip.shear t).continuous.continuousOn
  have hC01 : Disjoint (C 0) (C 1) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have he : x = y := (CairnsStrip.shear t).injective (hxz.trans hyz.symm)
    subst y
    exact Set.disjoint_left.mp (cairns_polygonal_annulus_frontier_disjoint D R hcompact hcontain) hx hy
  have hCdisjoint (i j : Fin 2) (hij : i ≠ j) : Disjoint (C i) (C j) := by
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hC01
    · exact hC01.symm
    · exact (hij rfl).elim
  have hCfront : frontier A = ⋃ j, C j := by
    rw [← (CairnsStrip.shear t).image_frontier,
      cairns_polygonal_annulus_frontier_decomposition D R hcompact hRcompact hregular hcontain,
      Set.image_union]
    ext z
    simp [C,Fin.exists_fin_succ]
  obtain ⟨B,hboundary,hcycles⟩ := CairnsStrip.straightComplex_boundaryCycles_of_frontier_components
    K p hp hpure hlinks hface hfaces A hA C hCclosed hCconnected hCdisjoint hCfront
  have hmap (x : ↥(carrier K)) : CairnsStrip.straightEval p x.val =
      CairnsStrip.shear t (HA x).val := by
    change CairnsStrip.straightEval p x.val =
      CairnsStrip.shear t ((CairnsStrip.shear t).symm (H x).val)
    rw [(CairnsStrip.shear t).apply_symm_apply]
    exact (hH x).symm
  have hcycle_mem (j : Fin 2) (x : ↥(carrier K)) :
      x ∈ cycleCarrier (B j) ↔ CairnsStrip.straightEval p x.val ∈ C j := by
    have hedge (u v : Fin N) (h : cycleEdge (B j) u v) : ({u,v} : Finset (Fin N)) ∈ K.faces :=
      ((hboundary.2.2 u v).mpr ⟨j,h⟩).2.1
    have heq := (CairnsStrip.straightEval_cycleCarrier_image K p (B j) hedge).trans (hcycles j)
    rw [← heq]
    exact (CairnsStrip.straightEval_injective K p hp hface hfaces).mem_set_image.symm
  refine ⟨N,K,B,o,hpure,hKconnected,hincidence,hlinks,hboundary,horiented,HA.symm,?_,?_⟩
  · rw [HA.image_symm]
    ext x
    change (HA x).val ∈ frontier D ↔ x ∈ cycleCarrier (B 0)
    rw [hcycle_mem,hmap]
    exact (CairnsStrip.shear t).injective.mem_set_image.symm
  · rw [HA.image_symm]
    ext x
    change (HA x).val ∈ frontier R ↔ x ∈ cycleCarrier (B 1)
    rw [hcycle_mem,hmap]
    exact (CairnsStrip.shear t).injective.mem_set_image.symm

end HolomorphicAnosov.Topology

