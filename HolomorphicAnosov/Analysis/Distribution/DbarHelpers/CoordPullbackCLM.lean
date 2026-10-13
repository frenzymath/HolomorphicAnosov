import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordFixedPullbackCLM
import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordPullback
import Mathlib.Analysis.Distribution.TestFunction

/-!
# coordPullbackCLM

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.
DAG node: `analysis.dbar_helper_coord_pullback_c_l_m_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
Test pullback along a real continuous linear equivalence between Banach spaces is continuous for
the native LF topology.

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.

Proof/construction: The LF universal property reduces continuity to each fixed compact support. On
that space the pullback is the already continuous fixed-support pullback followed by the
continuous inclusion of its preimage support into the inverse-image open test space. The two
functions agree pointwise.
-/
noncomputable def coordPullbackCLM
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (e : E ≃L[ℝ] F) (U : Opens F) :
    TestFunction U ℂ ⊤ →L[ℂ] TestFunction (coordDomain e U) ℂ ⊤ := by
  refine ⟨coordPullback e U, ?_⟩
  apply (TestFunction.continuous_iff_continuous_comp (coordPullback e U)).mpr
  intro K hK
  let L : Compacts E :=
    ⟨e ⁻¹' (K : Set F), e.toHomeomorph.isCompact_preimage.mpr K.isCompact⟩
  have hL : (L : Set E) ⊆ (coordDomain e U : Set E) := by
    intro x hx
    exact hK hx
  have hcomp : coordPullback e U ∘ TestFunction.ofSupportedIn hK =
      TestFunction.ofSupportedIn hL ∘ coordFixedPullbackCLM e K := by
    ext φ x
    rfl
  rw [hcomp]
  exact ((TestFunction.ofSupportedInCLM ℂ hL).comp
    (coordFixedPullbackCLM e K)).continuous


end HolomorphicAnosov.Analysis.Distribution
