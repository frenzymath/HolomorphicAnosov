import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity

noncomputable section
open Set _root_.Topology
namespace HolomorphicAnosov

/-- The actual chart at a parameter makes its original normed fibre complete.
HPS p.8 and pp.53–54: transport finite-dimensionality through the supplied
continuous linear coordinate equivalence, then use completeness of finite-dimensional
real normed spaces. No fibre norm or topology is replaced. -/
theorem parameter_graph_fibre_complete
    {P : Type*} [TopologicalSpace P] {E : P → Type*}
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [TopologicalSpace (Sigma E)]
    (e : FiniteRankNormedAtlas (E := E)) (p : P) : CompleteSpace (E p) := by
  let L := e.coordinates p p (e.mem_baseSet p)
  have : FiniteDimensional ℝ (E p) :=
    FiniteDimensional.of_injective L.toLinearMap L.injective
  exact FiniteDimensional.complete ℝ (E p)


end HolomorphicAnosov
