import Mathlib.Topology.VectorBundle.Hom

noncomputable section
namespace HolomorphicAnosov

/-- A continuous graph action in fixed model operator coordinates remains continuous after
composition with continuous varying source and target linear maps (Hirsch–Pugh–Shub, pp. 35,
55–58). -/
theorem parameter_graph_chart_action_continuous
    {Z X Y U V W T : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup T] [NormedSpace ℝ T]
    (Q : Z → X →L[ℝ] Y) (hQ : Continuous Q)
    (ι : Z → U →L[ℝ] X) (hι : Continuous ι)
    (ο : Z → Y →L[ℝ] V) (hο : Continuous ο)
    (ι' : Z → W →L[ℝ] U) (hι' : Continuous ι')
    (ο' : Z → V →L[ℝ] T) (hο' : Continuous ο') :
    Continuous (fun z ↦ (ο' z).comp ((ο z).comp ((Q z).comp ((ι z).comp (ι' z))))) := by
  exact hο'.clm_comp (hο.clm_comp (hQ.clm_comp (hι.clm_comp hι')))

/-- Evaluation version of the preceding chart action. -/
theorem parameter_graph_chart_action_evaluation_continuous
    {Z X Y : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Q : Z → X →L[ℝ] Y) (hQ : Continuous Q)
    (v : Z → X) (hv : Continuous v) :
    Continuous (fun z ↦ Q z (v z)) := hQ.clm_apply hv

end HolomorphicAnosov
