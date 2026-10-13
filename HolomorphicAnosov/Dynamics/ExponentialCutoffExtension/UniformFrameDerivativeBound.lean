import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.FrameCoordinateMetricBound
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.OpenFrameMetricDomain
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.CommonRadius
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.FiniteCompactPairedTangentCores
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.CompactZeroSectionSmallness

noncomputable section
namespace HolomorphicAnosov.ExponentialCutoff
open Bundle Set ExponentialLift
open scoped Manifold ContDiff Topology _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- A compact family of continuously varying first vertical derivatives has a
uniform metric radius on which its derivative differences are small in any
prescribed continuous fibre norm, expressed in paired original tangent frames.

Source: Lee (2003), Lemma 11.19 and proof of Theorem 17.19, pp. 278 and 457–458;
HPS (1977), proof of Theorem 5.5, pp. 61–62. This is the explicit moving-frame
application of those compact norm comparison and uniform continuity arguments.
Choose finitely many compact paired frame cores. On each core, compare source
coordinates with the metric norm and the target metric norm with coordinates.
The continuous first derivative field minus its value at zero vanishes on the
zero section, so compact zero-section smallness gives a coordinate radius for
any positive tolerance. Choose that tolerance to cancel the source/target norm
comparison constants, and take a finite minimum of the scaled radii. The
result controls the closed metric disc, including its boundary. Empty bases
are vacuous; the seminorm comparisons also cover zero-dimensional fibres. -/
theorem exists_uniform_frame_derivative_bound
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) (f : M → M) (hf : Continuous f)
    (hfA : MapsTo f A A) (ν : ContinuousRestrictedTangentNorm (E := E) A)
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (r : ℕ∞) (hr : 1 ≤ r) {R : ℝ} (hR : 0 < R)
    (hjets : HasContinuousVerticalJetsOn A f r H
      (fun p ↦ {v | metricNorm g p v < R}))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧ ∀ p : A, ∃ s t : A,
      (p : M) ∈ (chartAt E (s : M)).source ∧
      f (p : M) ∈ (chartAt E (t : M)).source ∧
      ∀ u : E, metricNorm g (p : M)
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (s : M)).symmL ℝ (p : M) u) ≤ δ →
      ∀ w : E,
        ν.value ⟨f p, hfA p.property⟩
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (t : M)).symmL ℝ (f p)
            ((fderiv ℝ (fibreExpression A f H s t p) u -
              fderiv ℝ (fibreExpression A f H s t p) 0) w)) ≤
        η * ν.value p
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (s : M)).symmL ℝ (p : M) w) := by
  classical
  by_cases hEmpty : A = ∅
  · refine ⟨R / 2, by positivity, by linarith, ?_⟩
    intro p
    exact (Set.notMem_empty p.val (hEmpty ▸ p.property)).elim
  obtain ⟨m, M₀, hm, hM₀, hlower, hupper⟩ :=
    finite_core_two_sided_norm_comparison_from_canonical g A hA ν
  have hfirst (s t : M) :
      ContinuousOn
        (fun z : A × E ↦ fderiv ℝ (fibreExpression A f H s t z.1) z.2)
        {z | (z.1 : M) ∈ (chartAt E s).source ∧ f z.1 ∈ (chartAt E t).source ∧
          (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (z.1 : M) z.2 ∈
            {v | metricNorm g z.1 v < R}} := by
    have hc := (continuousMultilinearCurryFin1 ℝ E E).continuous.comp_continuousOn
      (hjets.2 s t 1 hr)
    convert hc using 1
    funext z
    ext u
    simp only [Function.comp_apply, continuousMultilinearCurryFin1_apply,
      iteratedFDeriv_one_apply]
    rfl
  have hframeSmall (s t : M) (C : Set A) (hC : IsCompact C)
      (D : Set (A × E)) (hD : IsOpen D)
      (hDframe : D ⊆ {z | (z.1 : M) ∈ (chartAt E s).source ∧
        f z.1 ∈ (chartAt E t).source ∧
        (trivializationAt E (TangentSpace 𝓘(ℝ, E)) s).symmL ℝ (z.1 : M) z.2 ∈
          {v | metricNorm g z.1 v < R}})
      (hCzero : ∀ p ∈ C, (p, (0 : E)) ∈ D)
      (ρ θ : ℝ) (hρ : 0 < ρ) (hθ : 0 < θ) :
      ∃ d : ℝ, 0 < d ∧ d < ρ ∧ ∀ p ∈ C, ∀ u : E, ‖u‖ ≤ d →
        (p, u) ∈ D ∧
          ‖fderiv ℝ (fibreExpression A f H s t p) u -
            fderiv ℝ (fibreExpression A f H s t p) 0‖ < θ := by
    let D₀ : Set (A × E) := D ∩ (fun z : A × E ↦ (z.1, (0 : E))) ⁻¹' D
    have hD₀ : IsOpen D₀ :=
      hD.inter (hD.preimage (continuous_fst.prodMk continuous_const))
    have hcont := (hfirst s t).mono hDframe
    have hfield : ContinuousOn (fun z : A × E ↦
        fderiv ℝ (fibreExpression A f H s t z.1) z.2 -
          fderiv ℝ (fibreExpression A f H s t z.1) 0) D₀ :=
      (hcont.mono inter_subset_left).sub
        (hcont.comp (continuous_fst.prodMk continuous_const).continuousOn
          (fun _ hz ↦ hz.2))
    obtain ⟨d, hd, hdρ, hdu⟩ := compact_zero_section_smallness C hC D₀ hD₀
      _ hfield (fun p hp ↦ ⟨hCzero p hp, hCzero p hp⟩)
      (fun _ _ ↦ sub_self _) hρ hθ
    exact ⟨d, hd, hdρ, fun p hp u hu ↦ ⟨(hdu p hp u hu).1.1, (hdu p hp u hu).2⟩⟩
  obtain ⟨cores, frames, hcores, hcompact, hcover⟩ :=
    exists_finite_compact_paired_cores (E := E) A hA f hf hfA
  have hcoord : ∀ s : A, ∃ C : ℝ, 1 ≤ C ∧ ∀ p : A, (p : M) ∈ cores s →
      ∀ u : E, ‖u‖ ≤ C * metricNorm g (p : M)
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (s : M)).symmL ℝ (p : M) u) := by
    intro s
    exact coordinate_metric_upper_bound g A hA (cores s) (hcores s).1
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (s : M))
      (by infer_instance) (hcores s).2.2
  choose csrc hcsrc hsrc using hcoord
  have hmetric : ∀ s : A, ∃ C : ℝ, 1 ≤ C ∧ ∀ p : A, (p : M) ∈ cores s →
      ∀ u : E, metricNorm g (p : M)
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (s : M)).symmL ℝ (p : M) u) ≤ C * ‖u‖ := by
    intro s
    exact coordinate_metric_lower_bound g A hA (cores s) (hcores s).1
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (s : M))
      (by infer_instance) (hcores s).2.2
  choose ctar hctar htar using hmetric
  let θ : A × A → ℝ := fun i ↦ η * m / (M₀ * ctar i.2 * csrc i.1)
  have hθ (i : A × A) : 0 < θ i := by
    have hs : 0 < csrc i.1 := lt_of_lt_of_le zero_lt_one (hcsrc _)
    have ht : 0 < ctar i.2 := lt_of_lt_of_le zero_lt_one (hctar _)
    dsimp [θ]
    positivity
  have hpair (i : A × A) : ∃ d : ℝ, 0 < d ∧ d < R ∧
      ∀ p : A, (p : M) ∈ cores i.1 → f (p : M) ∈ cores i.2 →
      ∀ u : E, ‖u‖ ≤ d →
        ‖fderiv ℝ (fibreExpression A f H i.1 i.2 p) u -
          fderiv ℝ (fibreExpression A f H i.1 i.2 p) 0‖ < θ i := by
    let D : Set (A × E) := {z | (z.1 : M) ∈ (chartAt E (i.1 : M)).source ∧
      f z.1 ∈ (chartAt E (i.2 : M)).source ∧
      metricNorm g z.1 ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (i.1 : M)).symmL
        ℝ (z.1 : M) z.2) < R}
    have hD : IsOpen D :=
      isOpen_fixed_paired_frame_metric_domain g A f hf i.1 i.2
    obtain ⟨d, hd, hdR, hbound⟩ := hframeSmall i.1 i.2
      {p : A | (p : M) ∈ cores i.1 ∧ f (p : M) ∈ cores i.2}
      (hcompact i.1 i.2) D hD (fun _ hz ↦ hz)
      (fun p hp ↦ ⟨(hcores i.1).2.2 hp.1, (hcores i.2).2.2 hp.2,
        by simpa [metricNorm] using hR⟩) R (θ i) hR (hθ i)
    exact ⟨d, hd, hdR, fun p hp hfp u hu ↦ (hbound p ⟨hp, hfp⟩ u hu).2⟩
  choose d hd hdR hpairBound using hpair
  have hframes : frames.Nonempty := by
    obtain ⟨p, hp⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
    have hp' := hcover (show (⟨p, hp⟩ : A) ∈ Set.univ from mem_univ _)
    obtain ⟨s, hs, _⟩ := mem_iUnion₂.mp hp'
    exact ⟨s, hs⟩
  obtain ⟨δ, hδ, hδR, hscale⟩ := finite_common_radius
    (frames.product frames) (hframes.product hframes) d (fun i ↦ csrc i.1)
    (fun i _ ↦ hd i) (fun i _ ↦ lt_of_lt_of_le zero_lt_one (hcsrc i.1)) hR
  have huniform (p : A) : ∃ s t : A,
      (p : M) ∈ (chartAt E (s : M)).source ∧
      f (p : M) ∈ (chartAt E (t : M)).source ∧
      ∀ u : E, metricNorm g (p : M)
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (s : M)).symmL ℝ (p : M) u) ≤ δ →
      ∀ w : E,
        ν.value ⟨f p, hfA p.property⟩
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (t : M)).symmL ℝ (f p)
            ((fderiv ℝ (fibreExpression A f H s t p) u -
              fderiv ℝ (fibreExpression A f H s t p) 0) w)) ≤
        η * ν.value p
          ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) (s : M)).symmL ℝ (p : M) w) := by
    obtain ⟨s, hs, hpcover⟩ := mem_iUnion₂.mp (hcover (mem_univ p))
    obtain ⟨t, ht, hp, hfp⟩ := mem_iUnion₂.mp hpcover
    refine ⟨s, t, (hcores s).2.2 hp, (hcores t).2.2 hfp, ?_⟩
    intro u hu w
    have hdu : ‖u‖ ≤ d (s, t) :=
      (hsrc s p hp u).trans ((mul_le_mul_of_nonneg_left hu
        (le_trans zero_le_one (hcsrc s))).trans
          (hscale (s, t) (Finset.mem_product.mpr ⟨hs, ht⟩)))
    have hnorm := (hpairBound (s, t) p hp hfp u hdu).le
    have hbound := coordinate_derivative_to_nu_bound g A ν hm hM₀.le
      (le_trans zero_le_one (hcsrc s)) (le_trans zero_le_one (hctar t)) (hθ (s, t)).le
      hlower hupper p ⟨f p, hfA p.property⟩
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (s : M))
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (t : M))
      (by infer_instance) (by infer_instance)
      (fun x ↦ (ContinuousLinearMap.le_opNorm _ x).trans
        (mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)))
      (hsrc s p hp) (htar t ⟨f p, hfA p.property⟩ hfp) w
    have hcancel : M₀ * ctar t * θ (s, t) * csrc s / m = η := by
      have hs0 : csrc s ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hcsrc s))
      have ht0 : ctar t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (hctar t))
      dsimp [θ]
      field_simp [hs0, ht0, hm.ne', hM₀.ne']
    simpa only [hcancel] using hbound
  exact ⟨δ, hδ, hδR, huniform⟩

end HolomorphicAnosov.ExponentialCutoff
