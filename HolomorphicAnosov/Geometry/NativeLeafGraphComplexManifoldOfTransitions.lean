import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.IsManifold.Basic

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v

/-! This file constructs a complex manifold structure from complex-smooth transitions in a given
charted space. -/

/-- Pairwise complex-smooth transitions define a complex manifold structure on the supplied charted
space. -/
theorem native_leaf_graph_complex_manifold_of_transitions
    {k : ℕ} {L : Type u}
    [TopologicalSpace L]
    (charts : ChartedSpace (ComplexModel k) L)
    (htransition : ∀ e e' : OpenPartialHomeomorph L (ComplexModel k),
      e ∈ charts.atlas → e' ∈ charts.atlas →
      ContDiffOn ℂ ∞ (e' ∘ e.symm)
        (e.target ∩ e.symm ⁻¹' e'.source)) :
    letI := charts
    IsManifold (complexModel k) ∞ L := by
  let := charts
  apply isManifold_of_contDiffOn
  intro e e' he he'
  simpa only [complexModel, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.preimage_id, Set.range_id, Set.inter_univ,
    OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.symm_source] using htransition e e' he he'

end HolomorphicAnosov
