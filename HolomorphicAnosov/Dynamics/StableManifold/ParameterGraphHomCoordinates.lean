import Mathlib.Topology.VectorBundle.Hom

/-!
# Continuous operator fields in fixed Hom-bundle coordinates

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, LNM 583 (1977), p.35 and
pp.61–62, for continuous derivative sections and their parameter dependence;
pinned Mathlib `Topology/VectorBundle/Hom.lean`, for the actual chart formula.
This lemma is the fixed-model composition calculation within those charts.
-/

noncomputable section
namespace HolomorphicAnosov

/-- Continuity of an operator field after continuous source and target coordinate maps.

Source: the Hom-bundle chart formula in Mathlib
`Bundle.Trivialization.continuousLinearMap_apply`, used for the continuous
Hom sections in HPS p.35 and the parameter construction on pp.61–62.
Here `ι` maps source model coordinates into the source fibre model and `ο`
maps target fibre coordinates into the target model. The displayed statement
only needs their continuity as continuous-linear-map-valued functions; their
being chart inverses is a separate condition of the geometric application.

Proof: continuity of composition of continuous linear maps first gives
continuity of `z ↦ (P z).comp (ι z)`, then composition with `ο` gives the result.
Evaluation on a continuous vector field is the existing Mathlib theorem
`Continuous.clm_apply`. -/
theorem parameter_graph_hom_coordinates_continuous
    {Z X Y U V : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : Z → X →L[ℝ] Y) (hP : Continuous P)
    (ι : Z → U →L[ℝ] X) (hι : Continuous ι)
    (ο : Z → Y →L[ℝ] V) (hο : Continuous ο) :
    Continuous (fun z ↦ (ο z).comp ((P z).comp (ι z))) := by
  exact hο.clm_comp (hP.clm_comp hι)

end HolomorphicAnosov
