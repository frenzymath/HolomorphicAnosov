import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordDomain
import Mathlib.Analysis.Distribution.TestFunction

/-!
# coordPullback

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.
DAG node: `analysis.dbar_helper_coord_pullback_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
The complex-linear pullback of a smooth compactly supported test along a real continuous linear
equivalence is its composition with that equivalence, on the inverse-image open domain.

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.

Proof/construction: Compose the underlying function with the equivalence. Smoothness follows from
the native chain rule, compact support from the homeomorphism, and the support inclusion from the
preimage support inclusion. Addition and complex scalar multiplication hold pointwise.
-/
noncomputable def coordPullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (U : Opens F) :
    TestFunction U ℂ ⊤ →ₗ[ℂ] TestFunction (coordDomain e U) ℂ ⊤ where
  toFun φ := ⟨φ ∘ e, φ.contDiff.comp e.contDiff,
    φ.hasCompactSupport.comp_homeomorph e.toHomeomorph,
    (tsupport_comp_subset_preimage φ e.continuous).trans
      (preimage_mono φ.tsupport_subset)⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl


end HolomorphicAnosov.Analysis.Distribution
