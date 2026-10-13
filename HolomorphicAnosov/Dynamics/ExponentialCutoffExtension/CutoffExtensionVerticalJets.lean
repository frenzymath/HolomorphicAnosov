import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.LinearVerticalJets
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.MetricCutoffVerticalJets
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.VerticalJetOpenGluing
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.OpenFrameMetricDomain
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.FiniteSpatialJetCompositionContinuous

noncomputable section
namespace HolomorphicAnosov.ExponentialCutoff
open Bundle Set ExponentialLift
open scoped Manifold ContDiff Topology _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Original-model fibre regularity transfers to any fixed tangent frames by
continuous linear composition. Source: the frame-coordinate calculus in HPS,
proof of Theorem 5.5, p.62. The frame maps are used only linearly. -/
theorem contDiffOn_fibreExpression
    (A : Set M) (f : M → M)
    (G : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (p : A) (s t : M) (r : ℕ∞) (V : Set (TangentSpace 𝓘(ℝ, E) (p : M)))
    (hG : ContDiffOn ℝ r (fun u : E ↦ tangentSpaceCastModel 𝓘(ℝ, E) (f p)
      (G p ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm u)))
      ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm ⁻¹' V)) :
    ContDiffOn ℝ r (fibreExpression A f G s t p)
      {u | (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (p : M) u ∈ V} := by
  let es := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
  let et := trivializationAt E (TangentSpace 𝓘(ℝ, E)) t
  let J := tangentSpaceCastModel 𝓘(ℝ, E) (p : M)
  let L := tangentSpaceCastModel 𝓘(ℝ, E) (f p)
  have hi := hG.comp (J.toContinuousLinearMap.comp (es.symmL ℝ (p : M))).contDiff.contDiffOn
    (fun u (hu : es.symmL ℝ (p : M) u ∈ V) ↦ by
      simpa only [mem_preimage, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, J, ContinuousLinearEquiv.symm_apply_apply] using hu)
  have ho := ((et.continuousLinearMapAt ℝ (f p)).comp L.symm.toContinuousLinearMap).contDiff
    |>.comp_contDiffOn hi
  convert! ho using 1

omit [T2Space M] in
/-- The concrete cutoff extension preserves all jointly continuous vertical
jets through the given order. Source: HPS (1977), proof of Theorem 5.5, p.62.
The scalar cutoff has smooth ambient frame expressions. The actual tangent map
has continuous coefficients and explicit linear vertical jets, requiring only
C¹ regularity in the base. Pair the cutoff, H, and Tf jets and compose with the
fixed smooth map (a,b,c) ↦ c+a(b-c); the finite Faà di Bruno formula gives joint
continuity through precisely the supplied order r. Glue the product region
metricNorm<R to the linear region delta<metricNorm using locality of ordinary
fibre derivatives. These open regions cover since delta<R. No ambient C^r
regularity of Tf, and no manifold structure on A, is assumed. -/
theorem hasContinuousVerticalJets_extension
    (A : Set M) (f : M → M) (r : ℕ∞) (hr : 1 ≤ r)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r f)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    {R δ : ℝ} (hδ : 0 < δ) (hδR : δ < R)
    (hH : HasContinuousVerticalJetsOn A f r H (fun p ↦ {v | metricNorm g p v < R})) :
    HasContinuousVerticalJets A f r (extension A f g H R δ) := by
  have hlinear := hasContinuousVerticalJets_mfderiv A f r hr hf
  apply extension_vertical_jets_of_product_and_linear A f hf.continuous g H r hδ hδR hH
    (hlinear := hlinear)
  refine ⟨?_, ?_⟩
  · intro p
    have hL : ContDiff ℝ r (modelDerivative (E := E) f p) :=
      (modelDerivative (E := E) f p).contDiff
    have hχ := contDiff_fibreCutoff g δ (p : M) r
    have hp := hL.contDiffOn.add (hχ.contDiffOn.smul ((hH.1 p).sub hL.contDiffOn))
    convert! hp using 1
  · intro s t j hj
    let es := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
    let et := trivializationAt E (TangentSpace 𝓘(ℝ, E)) t
    let Ω : Set (A × E) := {z | (z.1 : M) ∈ (chartAt E s).source ∧
      f z.1 ∈ (chartAt E t).source ∧ metricNorm g z.1 (es.symmL ℝ (z.1 : M) z.2) < R}
    have hΩ : IsOpen Ω := isOpen_fixed_paired_frame_metric_domain g A f hf.continuous s t
    let a : A → E → ℝ := fun p u ↦ fibreCutoff g δ p (es.symmL ℝ (p : M) u)
    let b : A → E → E := fibreExpression A f H s t
    let c : A → E → E := fibreExpression A f
      (fun p ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)) s t
    have ha (p : A) : ContDiff ℝ r (a p) := by
      dsimp [a, fibreCutoff]
      apply scalarBump.contDiff.comp
      fun_prop
    have hb (p : A) : ContDiffOn ℝ r (b p) {u | (p, u) ∈ Ω} :=
      (contDiffOn_fibreExpression A f H p s t r _ (hH.1 p)).mono
        (fun u hu ↦ hu.2.2)
    have hc (p : A) : ContDiff ℝ r (c p) :=
      ((et.continuousLinearMapAt ℝ (f p)).comp
        ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M)).comp (es.symmL ℝ (p : M)))).contDiff
    have haj (k : ℕ) : ContinuousOn
        (fun z : A × E ↦ iteratedFDeriv ℝ k (a z.1) z.2) Ω :=
      (continuousOn_fibreCutoff_frame_vertical_jets_restrict A g δ s k).mono
        (fun z hz ↦ hz.1)
    have hbj (k : ℕ) (hk : (k : ℕ∞) ≤ r) : ContinuousOn
        (fun z : A × E ↦ iteratedFDeriv ℝ k (b z.1) z.2) Ω := hH.2 s t k hk
    have hcj (k : ℕ) (hk : (k : ℕ∞) ≤ r) : ContinuousOn
        (fun z : A × E ↦ iteratedFDeriv ℝ k (c z.1) z.2) Ω :=
      (hlinear.2 s t k hk).mono (fun z hz ↦ ⟨hz.1, hz.2.1, mem_univ _⟩)
    let B : A → E → ℝ × (E × E) := fun p u ↦ (a p u, b p u, c p u)
    have hB (p : A) : ContDiffOn ℝ r (B p) {u | (p, u) ∈ Ω} :=
      (ha p).contDiffOn.prodMk ((hb p).prodMk (hc p).contDiffOn)
    have hBj (k : ℕ) (hk : k ≤ j) : ContinuousOn
        (fun z : A × E ↦ iteratedFDeriv ℝ k (B z.1) z.2) Ω := by
      have hkr : (k : ℕ∞) ≤ r := (by exact_mod_cast hk : (k : ℕ∞) ≤ j).trans hj
      have hkr' : (k : ℕ∞ω) ≤ r := by exact_mod_cast hkr
      have hbc := HolomorphicAnosov.continuousOn_parametric_jet_prodMk b c Ω hΩ k
        (fun p ↦ (hb p).of_le hkr') (fun p ↦ (hc p).contDiffOn.of_le hkr')
        (hbj k hkr) (hcj k hkr)
      exact HolomorphicAnosov.continuousOn_parametric_jet_prodMk a (fun p u ↦ (b p u, c p u))
        Ω hΩ k (fun p ↦ (ha p).contDiffOn.of_le hkr')
        (fun p ↦ ((hb p).prodMk (hc p).contDiffOn).of_le hkr') (haj k) hbc
    let P : ℝ × (E × E) → E := fun z ↦ z.2.2 + z.1 • (z.2.1 - z.2.2)
    have hP : ContDiff ℝ j P := by dsimp [P]; fun_prop
    have hj' : (j : ℕ∞ω) ≤ r := by exact_mod_cast hj
    have hcomp := HolomorphicAnosov.continuousOn_parametric_jet_comp_finite B P Ω hΩ j
      (fun p ↦ (hB p).of_le hj') hP hBj
    apply hcomp.congr
    intro z hz
    have heq : fibreExpression A f
        (fun p v ↦ mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v +
          fibreCutoff g δ p v • (H p v - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v))
        s t z.1 = P ∘ B z.1 := by
      ext u
      simp [fibreExpression, P, B, a, b, c, es, map_add, map_sub, map_smul]
    exact congrArg (fun F : E → E ↦ iteratedFDeriv ℝ j F z.2) heq

end HolomorphicAnosov.ExponentialCutoff
