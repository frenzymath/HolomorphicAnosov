import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullbackCLM
import Mathlib.Analysis.Distribution.TestFunction

/-!
# coordPullbackCLM_apply

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.
DAG node: `analysis.dbar_helper_coord_pullback_c_l_m_apply_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Evaluation of the continuous test pullback at x is evaluation of the original test at e(x).

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.

Proof/construction: Unfold the bundled pullback. Its underlying function is composition, so the
equality is reflexive.
-/
@[simp] theorem coordPullbackCLM_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (e : E ≃L[ℝ] F) (U : Opens F) (φ : TestFunction U ℂ ⊤) (x : E) :
    coordPullbackCLM e U φ x = φ (e x) := rfl


end HolomorphicAnosov.Analysis.Distribution
