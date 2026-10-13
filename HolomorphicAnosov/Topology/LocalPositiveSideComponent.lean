import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Basic

/-! DAG node: `topo.local_positive_side_component_g10`. -/

open Set Metric
namespace HolomorphicAnosov

/-- Local positive sides along a connected zero set all belong to one component.
Agent expansion of Cairns (1951), Lemma 3.1(C), pp.861–862. Choose a connected
positive half-neighborhood at each point of the zero set. Nearby choices overlap:
the intersection of their neighborhoods contains a zero point, and openness of
the scalar coordinate supplies a positive point there. Their ambient components
therefore agree locally. Connectedness of the zero set makes the component label
constant. -/
theorem local_positive_side_component
    {X : Type*} [MetricSpace X] {S V : Set X} (hS : IsConnected S)
    (F : X → ℝ) (hF : IsOpenMap F) (hz : ∀ z ∈ S, F z = 0)
    (hlocal : ∀ z ∈ S, ∃ r : ℝ, 0 < r ∧
      IsConnected (ball z r ∩ {w | 0 < F w}) ∧
      ball z r ∩ {w | 0 < F w} ⊆ V) :
    ∃ x ∈ V, ∀ z ∈ S, ∃ r : ℝ, 0 < r ∧
      ball z r ∩ {w | 0 < F w} ⊆ connectedComponentIn V x := by
  classical
  let Z := S
  have hchoice (z : Z) := hlocal z z.property
  choose r hr hc hsub using hchoice
  choose x hx using fun z ↦ (hc z).nonempty
  let C (z : Z) := connectedComponentIn V (x z)
  have hPC (z : Z) : ball (z : X) (r z) ∩ {w | 0 < F w} ⊆ C z :=
    (hc z).isPreconnected.subset_connectedComponentIn (hx z) (hsub z)
  have hoverlap (z w : Z) (hw : (w : X) ∈ ball (z : X) (r z)) : C z = C w := by
    let U := ball (z : X) (r z) ∩ ball (w : X) (r w)
    have hU : IsOpen U := isOpen_ball.inter isOpen_ball
    have hwU : (w : X) ∈ U := ⟨hw, mem_ball_self (hr w)⟩
    have hzero : (0 : ℝ) ∈ F '' U := ⟨w, hwU, hz w w.property⟩
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (hF U hU) 0 hzero
    have hhalf : δ/2 ∈ ball (0 : ℝ) δ := by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
      exact half_lt_self hδ
    obtain ⟨u, hu, hFu⟩ := hδsub hhalf
    have huF : 0 < F u := hFu ▸ half_pos hδ
    have huCz : u ∈ C z := hPC z ⟨hu.1, huF⟩
    have huCw : u ∈ C w := hPC w ⟨hu.2, huF⟩
    exact (connectedComponentIn_eq huCz).trans (connectedComponentIn_eq huCw).symm
  have hC : IsLocallyConstant C := by
    apply (IsLocallyConstant.iff_exists_open C).mpr
    intro z
    refine ⟨Subtype.val ⁻¹' ball (z : X) (r z), isOpen_ball.preimage continuous_subtype_val,
      mem_ball_self (hr z), ?_⟩
    intro w hw
    exact (hoverlap z w hw).symm
  have : PreconnectedSpace Z := Subtype.preconnectedSpace hS.isPreconnected
  obtain ⟨z, hzS⟩ := hS.nonempty
  let z₀ : Z := ⟨z, hzS⟩
  refine ⟨x z₀, hsub z₀ (hx z₀), ?_⟩
  intro w hw
  let w₀ : Z := ⟨w, hw⟩
  refine ⟨r w₀, hr w₀, ?_⟩
  change ball w (r w₀) ∩ {w | 0 < F w} ⊆ C z₀
  rw [← show C w₀ = C z₀ from hC.apply_eq_of_preconnectedSpace w₀ z₀]
  exact hPC w₀

end HolomorphicAnosov

