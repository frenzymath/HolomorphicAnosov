import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
noncomputable section
open scoped ContDiff Manifold Topology
open Set Filter _root_.Topology

universe u
namespace HolomorphicAnosov

/-- Two restrictions of the SAME one-box plaque correspondence define the same germ. This is the elementary common-restriction part of Nisoli Remark1.3.5, p.23. -/
theorem same_box_plaque_germ_g10 {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,u} s t M) {x y : M}
    (e e' : LocalPlaqueTransport F x y)
    (hbox : e.box = e'.box) (hfirst : e.first = e'.first)
    (hsecond : e.second = e'.second) :
    (Filter.Germ.ofFun e.map : Filter.Germ (𝓝 (F.uPoint x)) (F.ULeaf y)) =
      Filter.Germ.ofFun e'.map := by
  apply Filter.Germ.coe_eq.mpr
  have he : e.map.source ∈ 𝓝 (F.uPoint x) := e.map.open_source.mem_nhds e.source_point
  have he' : e'.map.source ∈ 𝓝 (F.uPoint x) := e'.map.open_source.mem_nhds e'.source_point
  filter_upwards [he, he'] with z hz hz'
  obtain ⟨w, hw⟩ := e.source_in_plaque z hz
  have hchart (zw : FoliationCoordinateDisk s × FoliationCoordinateDisk t) :
      ((F.box e.box).chart zw).val = ((F.box e'.box).chart zw).val :=
    congrArg (fun i ↦ ((F.box i).chart zw).val) hbox
  have hw' : ((F.box e'.box).chart (e'.first, w)).val = z.val := by
    rw [← hchart, ← hfirst]
    exact hw
  apply Subtype.ext
  rw [e.coordinate_map z w hz hw, e'.coordinate_map z w hz' hw', ← hsecond]
  exact hchart _



end HolomorphicAnosov
