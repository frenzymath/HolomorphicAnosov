import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Complex.Basic

/-!
# For a real continuous linear equivalence e from E to F and an open subset U of F, coordDomain e
U is the open inverse image of U under e.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.A (2.1)–(2.3),
pp.13–14; formal coordinate/API detail for I (3.29). DAG node:
`analysis.dbar_helper_coord_domain_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
For a real continuous linear equivalence e from E to F and an open subset U of F, coordDomain e U
is the open inverse image of U under e.

Source: Demailly, Complex Analytic and Differential Geometry, June 21, 2012, I §2.A (2.1)–(2.3),
pp.13–14; formal coordinate/API detail for I (3.29).

Proof/construction: The inverse image is open because the continuous linear equivalence is
continuous.
-/
noncomputable def coordDomain
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (U : Opens F) : Opens E :=
  ⟨e ⁻¹' (U : Set F), U.isOpen.preimage e.continuous⟩


end HolomorphicAnosov.Analysis.Distribution
