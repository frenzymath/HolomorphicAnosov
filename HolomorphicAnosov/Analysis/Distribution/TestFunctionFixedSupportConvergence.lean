import Mathlib.Analysis.Distribution.TestFunction

open Set Filter TopologicalSpace
open scoped ContDiff Topology _root_.Topology

namespace HolomorphicAnosov.Analysis.Distribution

/-- Uniform convergence of every real derivative with one eventual compact support
implies convergence in the canonical test-function topology.

Source: Dyatlov, *Lecture notes for 18.155*, proof of Theorem 6.7, p.73,
equation (6.25), together with the native Mathlib topology on
`ContDiffMapSupportedIn` and its continuous inclusion into `TestFunction`.
Proof: replace the family by the limit outside the eventual support condition,
then bundle it in the smooth space supported in K. Each derivative structure map
converges in its supremum norm by the assumed uniform estimates (use half the
requested tolerance). The topology induced by these maps gives convergence in
the fixed-support space. Apply its continuous inclusion and eventual equality. -/
theorem testFunction_tendsto_of_eventual_fixed_support
    {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Opens E) (K : Compacts E) (hKU : (K : Set E) ⊆ U)
    (φ : TestFunction U F ⊤) (η : ι → TestFunction U F ⊤) (l : Filter ι)
    (hφ : tsupport (φ : E → F) ⊆ K)
    (hη : ∀ᶠ a in l, tsupport (η a : E → F) ⊆ K)
    (hderiv : ∀ j : ℕ, ∀ t : ℝ, 0 < t → ∀ᶠ a in l, ∀ y : E,
      ‖iteratedFDeriv ℝ j (η a : E → F) y - iteratedFDeriv ℝ j (φ : E → F) y‖ < t) :
    Tendsto η l (𝓝 φ) := by
  classical
  let φK : ContDiffMapSupportedIn E F ⊤ K :=
    ⟨φ, φ.contDiff, fun y hy => image_eq_zero_of_notMem_tsupport (fun h => hy (hφ h))⟩
  let ηK : ι → ContDiffMapSupportedIn E F ⊤ K := fun a =>
    if h : tsupport (η a : E → F) ⊆ K then
      ⟨η a, (η a).contDiff, fun y hy =>
        image_eq_zero_of_notMem_tsupport (fun hp => hy (h hp))⟩
    else φK
  have heq : ∀ᶠ a in l, (ηK a : E → F) = η a := by
    filter_upwards [hη] with a ha
    simp only [ηK, dite_eq_left ha]
    rfl
  have hK : Tendsto ηK l (𝓝 φK) := by
    apply (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM ℝ (n := ⊤)).isEmbedding.tendsto_nhds_iff.mpr
    apply tendsto_pi_nhds.mpr
    intro j
    apply Metric.tendsto_nhds.mpr
    intro t ht
    filter_upwards [heq, hderiv j (t / 2) (half_pos ht)] with a ha hb
    change dist (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ j (ηK a))
      (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ j φK) < t
    apply lt_of_le_of_lt ((BoundedContinuousFunction.dist_le (le_of_lt (half_pos ht))).mpr ?_)
      (half_lt_self ht)
    intro y
    simp only [ContDiffMapSupportedIn.structureMapCLM_top_apply, ha]
    change dist (iteratedFDeriv ℝ j (η a : E → F) y) (iteratedFDeriv ℝ j (φ : E → F) y) ≤ t / 2
    rw [dist_eq_norm]
    exact (hb y).le
  have h := (TestFunction.continuous_ofSupportedIn hKU).tendsto φK |>.comp hK
  apply h.congr'
  filter_upwards [heq] with a ha
  exact TestFunction.ext fun y => congrFun ha y

end HolomorphicAnosov.Analysis.Distribution
