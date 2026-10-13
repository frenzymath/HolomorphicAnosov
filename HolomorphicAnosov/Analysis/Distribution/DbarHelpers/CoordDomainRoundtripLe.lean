import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import Mathlib.Analysis.Distribution.TestFunction

/-!
# coordDomain_roundtrip_le

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.
DAG node: `analysis.dbar_helper_coord_domain_roundtrip_le_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Pulling an open set back along an equivalence and then along its inverse gives an open domain
included in the original set.

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.

Proof/construction: A membership assertion in the twice-pulled-back domain is membership of e
inverse applied to e(x) in the original set. Cancel the inverse maps.
-/
theorem coordDomain_roundtrip_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (U : Opens E) : coordDomain e (coordDomain e.symm U) ≤ U := by
  intro x hx
  change e.symm (e x) ∈ U at hx
  simpa using hx


end HolomorphicAnosov.Analysis.Distribution
