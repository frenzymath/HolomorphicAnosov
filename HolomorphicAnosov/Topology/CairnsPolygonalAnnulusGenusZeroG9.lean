import HolomorphicAnosov.Topology.FiniteSurfacePlanarFrontierG9
import HolomorphicAnosov.Topology.PlanarBoundaryLiftG9
import HolomorphicAnosov.Topology.NormalWordHandleCircleG9
import HolomorphicAnosov.Topology.GallierXuOrientableSurfaceNormalForm
import HolomorphicAnosov.Topology.CairnsAnnulusEulerArithmeticG9
import HolomorphicAnosov.Topology.SurfaceEdgeIncidenceCountG9
import HolomorphicAnosov.Topology.BoundaryEdgeCountG9
import HolomorphicAnosov.Topology.BoundaryCycleConeG9

/-!
# Vanishing genus for a planar two-boundary triangulation

Gallier--Xu's orientable normal form gives Euler count `2-2g-b`. A positive
genus supplies an explicit circle map constant on all boundary loops but
without a real lift. The local link charts put the ambient frontier on those
loops. Tietze extension and the exponential covering force every such map on
a planar embedded compact surface to lift, so `g=0`. The proved finite cap
increment then gives capped Euler count two. No Jordan--Schoenflies theorem
or simplicial/singular comparison is needed.
-/

open Set
open scoped BigOperators
namespace HolomorphicAnosov.Topology
open GallierXu
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The explicitly capped finite surface has Euler count two.

Source: Gallier--Xu §6.2, pp.88--90, Lemma 6.1 pp.92--95, and Theorem 6.1
p.96 for the orientable normal word and its Euler identity; Hatcher §1.3
Propositions 1.33--1.34 pp.61--63 for covering lifts, and Theorem 2B.3 p.172 for planar
invariance of domain. The following planar obstruction is agent-written.

The inverse of H embeds the compact carrier K in the plane. Its exact
circular and interval vertex links give local disk or strip charts at every
point away from the listed boundary cycles; invariance of domain makes all
these image points interior. Thus the ambient frontier lies on the two
boundary cycles. Put K in Gallier--Xu normal form, preserving both cycles.
If its genus were positive, the first handle block a b a⁻¹ b⁻¹ admits the
explicit circle map with real boundary values 0,1,1,0,0, exponentiated after
Tietze extension to the polygon disk. It respects every edge identification,
is one on every boundary loop, and carries the closed a-side once around the
circle, so has no real lift. Transport it to K. Set it equal to one outside
the planar image; boundary agreement gives a continuous map on the plane.
The exponential covering and simple connectedness of the plane give a real
lift, a contradiction. Hence the genus is zero and the original Euler count
is 2-0-2=0. Each of the two literal cone caps increases V-E+F by one, giving
the displayed count two.
-/
theorem cairns_polygonal_annulus_capped_sphere_euler_g9
    {N : ℕ} (D R : Set Plane)
    (K : AbstractSimplicialComplex (Fin N))
    (B : Fin 2 → List (Fin N))
    (hpure : PureTwo K)
    (hconnected : IsConnected (carrier K))
    (hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (hlinks : SurfaceLinks K)
    (hboundary : BoundaryCycles K B)
    (H : ↥(R \ interior D) ≃ₜ ↥(carrier K))
    (_hinnerBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier D} =
        cycleCarrier (B 0))
    (_houterBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
        cycleCarrier (B 1))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (horiented : Oriented (trianglePresentation K o)) :
    ((simplices (capTwoBoundaryCycles K B) 0).card : ℤ) -
      ((simplices (capTwoBoundaryCycles K B) 1).card : ℤ) +
      ((simplices (capTwoBoundaryCycles K B) 2).card : ℤ) = 2 := by
  classical
  obtain ⟨g,sequence,H₀,hparameters,⟨σ,hσ⟩,hEuler⟩ :=
    orientable_triangulated_surface_normal_form K (by decide : 1 ≤ 2) hpure hconnected
      hincidence hlinks B hboundary o horiented
  let E : ↥(carrier K) ≃ₜ Realization [normalWord g 2] := H₀.trans sequence.homeomorph
  let f : C(↥(carrier K),Plane) :=
    ⟨fun x ↦ (H.symm x).val,continuous_subtype_val.comp H.symm.continuous⟩
  have hf : Function.Injective f := fun x y h ↦ H.symm.injective (Subtype.ext h)
  let : CompactSpace ↥(carrier K) := isCompact_iff_compactSpace.mp (triangle_carrier_compact K)
  have hgzero : g = 0 := by
    by_contra hg
    obtain ⟨F,hFboundary,hFnolift⟩ := normalWord_circle_obstruction_g9 g 2 (Nat.pos_of_ne_zero hg)
    let G : C(↥(carrier K),Circle) := ⟨fun x ↦ F (E x),F.continuous.comp E.continuous⟩
    have hfront (x : ↥(carrier K)) (hx : f x ∈ frontier (range f)) : G x = 1 := by
      have hm := surface_image_frontier_subset_boundary_g9 K B hpure hlinks hboundary f hf hx
      obtain ⟨j,y,hy,hyx⟩ := mem_iUnion.mp hm
      have he : y = x := hf hyx
      subst y
      apply hFboundary (σ j)
      rw [← hσ j]
      exact mem_image_of_mem E hy
    obtain ⟨a,ha⟩ := circle_lift_of_embedding_frontier_g9 (0 : Plane) f hf G hfront
    apply hFnolift
    refine ⟨⟨fun z ↦ a (E.symm z),a.continuous.comp E.symm.continuous⟩,fun z ↦ ?_⟩
    simpa only [G,ContinuousMap.coe_mk,E.apply_symm_apply] using ha (E.symm z)
  have hχ : ((simplices K 0).card : ℤ) - ((simplices K 1).card : ℤ) +
      ((simplices K 2).card : ℤ) = 0 := by simpa [hgzero] using hEuler
  have hcaps := capTwoBoundaryCycles_euler_count_g9 K B hboundary
  omega

/-- Capping gives the vertex/triangle balance `2V=F+length(B₀)+length(B₁)`.
The capped Euler count two and the cap increment give original Euler count
zero. Combine this with `3F+E_boundary=2E` and the exact boundary edge count.
Source: Gallier--Xu §§6.2,6.6 and the finite incidence count, with the planar
handle obstruction proved in the preceding theorem.
-/
theorem cairns_polygonal_annulus_capping_balance_g9
    {N : ℕ} (D R : Set Plane)
    (K : AbstractSimplicialComplex (Fin N))
    (B : Fin 2 → List (Fin N))
    (hpure : PureTwo K)
    (hconnected : IsConnected (carrier K))
    (hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (hlinks : SurfaceLinks K)
    (hboundary : BoundaryCycles K B)
    (H : ↥(R \ interior D) ≃ₜ ↥(carrier K))
    (hinnerBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier D} =
        cycleCarrier (B 0))
    (houterBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
        cycleCarrier (B 1))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (horiented : Oriented (trianglePresentation K o)) :
    2 * ((simplices K 0).card : ℤ) = ((simplices K 2).card : ℤ) +
      ∑ j : Fin 2, ((B j).length : ℤ) := by
  have hsphere := cairns_polygonal_annulus_capped_sphere_euler_g9 D R K B hpure
    hconnected hincidence hlinks hboundary H hinnerBoundary houterBoundary o horiented
  have hcaps := capTwoBoundaryCycles_euler_count_g9 K B hboundary
  have hi : 3 * ((simplices K 2).card : ℤ) +
      (((simplices K 1).filter fun e ↦ incidence K e = 1).card : ℤ) =
        2 * ((simplices K 1).card : ℤ) := by
    exact_mod_cast surface_edge_incidence_count_g9 K hincidence
  have hb : (((simplices K 1).filter fun e ↦ incidence K e = 1).card : ℤ) =
      ∑ j : Fin 2, ((B j).length : ℤ) := by
    exact_mod_cast boundary_edge_count_eq_cycle_lengths_g9 K B hboundary
  omega

/-- Twice the vertex count is the triangle count plus the number of boundary
edges. Rewrite the proved boundary-edge count in the capping balance.
Source: Gallier--Xu Definition 6.1 and the canonical normal-form Euler count; the planar input
is the explicitly named capped-sphere Euler provider above.
-/
theorem cairns_polygonal_annulus_vertex_face_balance_g9
    {N : ℕ} (D R : Set Plane)
    (K : AbstractSimplicialComplex (Fin N))
    (B : Fin 2 → List (Fin N))
    (hpure : PureTwo K)
    (hconnected : IsConnected (carrier K))
    (hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (hlinks : SurfaceLinks K)
    (hboundary : BoundaryCycles K B)
    (H : ↥(R \ interior D) ≃ₜ ↥(carrier K))
    (hinnerBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier D} =
        cycleCarrier (B 0))
    (houterBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
        cycleCarrier (B 1))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (horiented : Oriented (trianglePresentation K o)) :
    2 * ((simplices K 0).card : ℤ) = ((simplices K 2).card : ℤ) +
      (((simplices K 1).filter fun e ↦ incidence K e = 1).card : ℤ) := by
  classical
  have hc : (((simplices K 1).filter fun e ↦ incidence K e = 1).card : ℤ) =
      ∑ j : Fin 2, ((B j).length : ℤ) := by
    exact_mod_cast boundary_edge_count_eq_cycle_lengths_g9 K B hboundary
  rw [hc]
  exact cairns_polygonal_annulus_capping_balance_g9 D R K B hpure hconnected
    hincidence hlinks hboundary H hinnerBoundary houterBoundary o horiented


/-- The original planar two-boundary complex has Euler count zero.
Subtract the incidence identity `3F + E_boundary = 2E` from the proved
balance `2V = F + E_boundary`. Source: Gallier--Xu §6.2, pp.88--90, with the planar handle obstruction
in the capped-count theorem.
-/
theorem cairns_polygonal_annulus_planar_euler_transport_g9
    {N : ℕ} (D R : Set Plane)
    (K : AbstractSimplicialComplex (Fin N))
    (B : Fin 2 → List (Fin N))
    (hpure : PureTwo K)
    (hconnected : IsConnected (carrier K))
    (hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (hlinks : SurfaceLinks K)
    (hboundary : BoundaryCycles K B)
    (H : ↥(R \ interior D) ≃ₜ ↥(carrier K))
    (hinnerBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier D} =
        cycleCarrier (B 0))
    (houterBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
        cycleCarrier (B 1))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (horiented : Oriented (trianglePresentation K o)) :
    ((simplices K 0).card : ℤ) - ((simplices K 1).card : ℤ) +
        ((simplices K 2).card : ℤ) = 0 := by
  classical
  have hbalance := cairns_polygonal_annulus_vertex_face_balance_g9 D R K B hpure
    hconnected hincidence hlinks hboundary H hinnerBoundary houterBoundary o horiented
  have hcount : 3 * ((simplices K 2).card : ℤ) +
      (((simplices K 1).filter fun e ↦ incidence K e = 1).card : ℤ) =
        2 * ((simplices K 1).card : ℤ) := by
    exact_mod_cast surface_edge_incidence_count_g9 K hincidence
  omega

/-- The normal-form Euler identity forces genus zero once the original
complex has Euler count zero. Source: Gallier--Xu §§6.2 and 6.6,
pp.88--89 and 102--103. This theorem has no local admission; its planar
input is `cairns_polygonal_annulus_capped_sphere_euler_g9`.
-/
theorem cairns_polygonal_annulus_genus_zero_g9
    {N : ℕ} (D R : Set Plane)
    (K : AbstractSimplicialComplex (Fin N))
    (B : Fin 2 → List (Fin N))
    (hpure : PureTwo K)
    (hconnected : IsConnected (carrier K))
    (hincidence : ∀ e ∈ simplices K 1, incidence K e = 1 ∨ incidence K e = 2)
    (hlinks : SurfaceLinks K)
    (hboundary : BoundaryCycles K B)
    (H : ↥(R \ interior D) ≃ₜ ↥(carrier K))
    (hinnerBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier D} =
        cycleCarrier (B 0))
    (houterBoundary :
      H '' {x : ↥(R \ interior D) | (x : Plane) ∈ frontier R} =
        cycleCarrier (B 1))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (horiented : Oriented (trianglePresentation K o))
    (g : ℕ)
    (hEuler : ((simplices K 0).card : ℤ) - ((simplices K 1).card : ℤ) +
        ((simplices K 2).card : ℤ) = (2 : ℤ) - 2 * (g : ℤ) - 2) :
    g = 0 := by
  have hχ := cairns_polygonal_annulus_planar_euler_transport_g9 D R K B hpure
    hconnected hincidence hlinks hboundary H hinnerBoundary houterBoundary o horiented
  exact annulus_euler_zero_genus_zero_g9 hχ hEuler


end HolomorphicAnosov.Topology

