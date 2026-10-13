import HolomorphicAnosov.Analysis.Distribution.DbarHelpers.CoordinatePullbackIteratedBound
import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.Distribution.TestFunction

/-!
# coordFixedPullbackCLM

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.
DAG node: `analysis.dbar_helper_coord_fixed_pullback_c_l_m_g6`.
-/

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/--
For a real continuous linear equivalence between Banach spaces, fixed-compact-support test
pullback is a continuous complex-linear map into tests supported in the compact preimage.

Source: Semyon Dyatlov, 18.155 distributions notes, obtained 2026 version, §10.1.3, p.109, test
pullback under a diffeomorphism; for continuity use the source-specialized higher-chain bound and
native fixed-support/LF seminorm topologies.

Proof/construction: Bundle composition as a linear map. For each derivative seminorm i, the
source-specialized coordinate pullback estimate bounds the output seminorm by norm(e)^i times the
input seminorm i. The native seminorm criterion gives continuity. Compactness of the target
support is the homeomorphism preimage theorem.
-/
noncomputable def coordFixedPullbackCLM
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (e : E ≃L[ℝ] F) (K : Compacts F) :
    ContDiffMapSupportedIn F ℂ ⊤ K →L[ℂ]
      ContDiffMapSupportedIn E ℂ ⊤
        (⟨e ⁻¹' (K : Set F), e.toHomeomorph.isCompact_preimage.mpr K.isCompact⟩ : Compacts E) := by
  let L : Compacts E :=
    ⟨e ⁻¹' (K : Set F), e.toHomeomorph.isCompact_preimage.mpr K.isCompact⟩
  let A : ContDiffMapSupportedIn F ℂ ⊤ K →ₗ[ℂ] ContDiffMapSupportedIn E ℂ ⊤ L :=
    { toFun := fun φ ↦ ⟨φ ∘ e, φ.contDiff.comp e.contDiff,
        fun x hx ↦ φ.zero_on_compl hx⟩
      map_add' := fun _ _ ↦ by ext; rfl
      map_smul' := fun _ _ ↦ by ext; rfl }
  refine ⟨A, ?_⟩
  refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ℂ F ℂ ⊤ K)
    (ContDiffMapSupportedIn.withSeminorms ℂ E ℂ ⊤ L) A (Seminorm.IsBounded.of_real fun i ↦ ?_)
  refine ⟨{i}, ‖e.toContinuousLinearMap‖ ^ i, ?_⟩
  intro φ
  rw [Finset.sup_singleton]
  apply ((A φ).seminorm_top_le_iff ℂ
    (mul_nonneg (pow_nonneg (norm_nonneg _) _) (apply_nonneg _ _)) i).mpr
  intro x hx
  exact coordinatePullback_iterated_bound e K φ i x


end HolomorphicAnosov.Analysis.Distribution
