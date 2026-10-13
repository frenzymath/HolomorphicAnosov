import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.ContinuousMap.Compact

open Set Filter
open scoped Topology _root_.Topology ContDiff

namespace HolomorphicAnosov.Analysis

/-- A family of smooth functions supported in one compact set is continuous in the
fixed-support test topology if every spatial derivative is jointly continuous on
the parameter space times that compact set.

Source: Dyatlov, 18.155 notes (2026), Proposition 6.3, pp.68–69, equation (6.8).
Each derivative, restricted to the compact support, is a continuous family in the
uniform norm by the compact-open exponential law. The full derivative vanishes
outside the support, so its uniform distance is bounded by the distance of these
restrictions. Thus every derivative structure map is continuous. These structure
maps define the fixed-support test topology. Empty supports are included. -/
theorem fixed_support_family_continuous_of_jets
    {E F A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace A]
    (K : TopologicalSpace.Compacts E) (Φ : A → ContDiffMapSupportedIn E F ⊤ K)
    (hΦ : ∀ n : ℕ, Continuous (fun z : A × K ↦
      iteratedFDeriv ℝ n (Φ z.1) z.2.val)) : Continuous Φ := by
  apply (ContDiffMapSupportedIn.continuous_iff_comp Φ).mpr
  intro n
  let ψ := ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ n ∘ Φ
  let ψK : A → C(K, E [×n]→L[ℝ] F) := fun a ↦
    ⟨fun x ↦ ψ a x.val, (ψ a).continuous.comp continuous_subtype_val⟩
  have hψK : Continuous ψK := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : A × K ↦ ψ z.1 z.2.val)
    convert hΦ n using 1
    funext z
    exact congrFun (ContDiffMapSupportedIn.structureMapCLM_top_apply ℝ (Φ z.1)) z.2.val
  have hdist (a b : A) : dist (ψ a) (ψ b) ≤ dist (ψK a) (ψK b) := by
    apply (BoundedContinuousFunction.dist_le dist_nonneg).mpr
    intro x
    by_cases hx : x ∈ K
    · exact ContinuousMap.dist_apply_le_dist (f := ψK a) (g := ψK b) ⟨x, hx⟩
    · have hz (a : A) : ψ a x = 0 := by
        rw [show ψ a x = iteratedFDeriv ℝ n (Φ a) x from congrFun
          (ContDiffMapSupportedIn.structureMapCLM_top_apply ℝ (Φ a)) x]
        exact image_eq_zero_of_notMem_tsupport (fun h ↦ hx
          ((tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := (Φ a : E → F)) n).trans (Φ a).tsupport_subset h))
      simp only [hz, dist_self]
      exact dist_nonneg
  apply continuous_iff_continuousAt.mpr
  intro a
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (hψK.continuousAt (x := a)).eventually (Metric.ball_mem_nhds (ψK a) hε)
  filter_upwards [he] with b hb
  exact (hdist b a).trans_lt hb

end HolomorphicAnosov.Analysis

