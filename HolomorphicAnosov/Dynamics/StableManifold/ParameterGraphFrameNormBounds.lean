import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- Pointwise norm comparisons in an actual source frame, using the unchanged
original fibre norm. HPS p.8 and the frame preparation in step 1a below.
The operator norm of the coordinate map and its inverse supplies both inequalities,
including a zero-rank fibre. Local uniform bounds require the separate compact-sphere
continuity argument and are not assumed here. -/
theorem parameter_graph_frame_norm_bounds
    {P : Type*} [TopologicalSpace P] {E : P → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [TopologicalSpace (Sigma E)]
    (e : FiniteRankNormedAtlas (E := E)) (i p : P) (hp : p ∈ (e.chart i).baseSet) :
    let L := e.coordinates i p hp
    (∀ v, ‖L.symm v‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖v‖) ∧
    (∀ v, ‖v‖ ≤ ‖L.toContinuousLinearMap‖ * ‖L.symm v‖) := by
  dsimp only
  constructor
  · exact (e.coordinates i p hp).symm.toContinuousLinearMap.le_opNorm
  · intro v
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
      (e.coordinates i p hp).toContinuousLinearMap.le_opNorm
        ((e.coordinates i p hp).symm v)



end HolomorphicAnosov
