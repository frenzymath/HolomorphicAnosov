import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.SmallCutoffLipschitz
import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.CutoffExtensionVerticalJets

noncomputable section
namespace HolomorphicAnosov.ExponentialCutoff
open Bundle Set ExponentialLift
open scoped Manifold ContDiff Topology _root_.Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- A compact family of local fibre maps tangent to `Tf` has a uniformly small
cutoff remainder, with all its continuous vertical jets preserved.

Source: HPS, *Invariant Manifolds*, proof of Theorem 5.5, pp. 61–62;
Lee (2003), Lemma 2.27 p. 56, Lemma 11.19 p. 278, and Theorem 17.19
pp. 457–458; Merry, Lecture 32, Theorem 32.2, equations (32.6)–(32.7).
This is the analytic part of the source composite, for an arbitrary local
fibre map `H`; no exponential identity or local inverse is needed.

Proof: choose finitely many paired source and receiving tangent frames whose
compact cores cover `A`. Continuity of `f` permits the receiving-frame choice.
Compact unit-sphere minima and maxima in each frame compare the prescribed
continuous norm, the metric norm, and coordinate norms by positive constants
uniform over all cores. This also covers zero-dimensional fibres by using their
unique zero vector; empty `A` is vacuous. Write `Q_p(v)=H_p(v)-Tf_p(v)`.
The hypotheses give `Q_p(0)=0`, `DQ_p(0)=0`, and continuous vertical jets for Q:
the linear term has jets `(Tf_p(v),Tf_p,0,...)`, with continuous coefficients
from `hf` and `hr`. On each compact core, continuity of `DQ` and its vanishing
at zero give one small closed coordinate ball with arbitrarily small operator
norm. Apply `compact_zero_section_smallness`, then use the norm comparisons and
the finite minimum of the resulting radii to obtain a common metric radius δ<R
on which the derivative of Q has norm at most η in the prescribed norms.
The radial mean value theorem gives `ν(Q_p(v)) ≤ η ν(v)` there.

The smooth scalar bump has finite derivative bound K. Its composition with
`g_p(v,v)/δ²` is fibrewise smooth, bounded by one, vanishes for metric norm at
least δ, and has directional derivative at most `2K|u|_g/δ` on that disc, by
the quadratic chain rule and Cauchy–Schwarz. Its vertical jets depend
continuously on the base: in any tangent frame the quadratic form is a finite
sum of products of smooth metric coefficients and vector coordinates.
If `m|v|_g ≤ ν(v) ≤ M|v|_g`, the derivative of the cutoff product is bounded by
`(1+2KM/m)η` in ν. Choose η positive so this quantity is at most ε, and only
then choose δ by the preceding compactness argument. On `|v|_g<R` the extension
is `Tf + χQ`; on the open set `|v|_g>δ` it is `Tf`. These sets cover every
fibre because δ<R. The product rule and locality give fibrewise C^r and the
joint continuous jets: subtraction, pairing, and composition with scalar
multiplication give the finite Taylor coefficients on the first open region;
on the second they are the explicit linear jets. The coefficients agree on
the overlap by equality of germs. At finite r this uses only vertical jets,
not ambient C^r regularity of Tf. Order-zero jet continuity in paired frames
and continuity of f give continuity of the total bundle map. Finally the
fixed-fibre mean value theorem along the segment between arbitrary v and w
converts the global derivative bound for the cutoff remainder into the stated
all-pairs ν-Lipschitz inequality. -/
theorem exists_small_cutoff_remainder
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) (f : M → M) (r : ℕ∞)
    (hr : 1 ≤ r) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) r f)
    (hfA : MapsTo f A A)
    (ν : ContinuousRestrictedTangentNorm (E := E) A)
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    {R : ℝ} (hR : 0 < R)
    (hzero : ∀ p : A, H p 0 = 0 ∧ HasFDerivAt
      (fun u : E ↦ tangentSpaceCastModel 𝓘(ℝ, E) (f p)
        (H p ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm u)))
      (modelDerivative f p) 0)
    (hjets : HasContinuousVerticalJetsOn A f r H
      (fun p ↦ {v | metricNorm g p v < R}))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
      let G := extension A f g H R δ
      IsContinuousBundleMap A f G ∧ HasContinuousVerticalJets A f r G ∧
      ∀ (p : A) (v w : TangentSpace 𝓘(ℝ, E) (p : M)),
        ν.value ⟨f p, hfA p.property⟩
          ((G p v - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v) -
            (G p w - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) w)) ≤
          ε * ν.value p (v - w) := by
  obtain ⟨δ, hδ, hδR, hLipschitz⟩ := exists_small_cutoff_lipschitz
    g A hA f r hr hf hfA ν H hR hzero hjets hε
  have hcontinuous
      (G : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
      (hG : HasContinuousVerticalJets A f r G) : IsContinuousBundleMap A f G := by
    rw [IsContinuousBundleMap, continuous_iff_continuousAt]
    intro z
    let s : M := z.val.proj
    let t : M := f s
    let es := trivializationAt E (TangentSpace 𝓘(ℝ, E)) s
    let et := trivializationAt E (TangentSpace 𝓘(ℝ, E)) t
    let b : {z : TangentBundle 𝓘(ℝ, E) M | z.proj ∈ A} → A :=
      fun z ↦ ⟨z.val.proj, z.property⟩
    let P : {z : TangentBundle 𝓘(ℝ, E) M | z.proj ∈ A} → A × E :=
      fun z ↦ (b z, (es z.val).2)
    have hb : Continuous b :=
      ((FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp
        continuous_subtype_val).subtype_mk _
    have hP : ContinuousAt P z := hb.continuousAt.prodMk
      ((continuous_snd.continuousAt.comp
        (es.continuousAt (by exact es.mem_source.mpr (mem_chart_source E s)))).comp
          continuous_subtype_val.continuousAt)
    have hzerojet := hG.2 s t 0 (bot_le : (0 : ℕ∞) ≤ r)
    have hvalue : ContinuousOn (fun q : A × E ↦ fibreExpression A f G s t q.1 q.2)
        {q | (q.1 : M) ∈ (chartAt E s).source ∧ f q.1 ∈ (chartAt E t).source} := by
      have hv := (continuousMultilinearCurryFin0 ℝ E E).continuous.comp_continuousOn hzerojet
      simp only [Set.mem_univ, and_true] at hv
      convert hv using 1
      funext q
      simp only [Function.comp_apply, continuousMultilinearCurryFin0_apply,
        iteratedFDeriv_zero_apply]
    have hopen : IsOpen
        {q : A × E | (q.1 : M) ∈ (chartAt E s).source ∧ f q.1 ∈ (chartAt E t).source} :=
      ((chartAt E s).open_source.preimage
        (continuous_subtype_val.comp continuous_fst)).inter
      ((chartAt E t).open_source.preimage
        (hf.continuous.comp (continuous_subtype_val.comp continuous_fst)))
    have hmem : P z ∈
        {q : A × E | (q.1 : M) ∈ (chartAt E s).source ∧ f q.1 ∈ (chartAt E t).source} :=
      ⟨mem_chart_source E s, mem_chart_source E t⟩
    apply (FiberBundle.continuousAt_totalSpace E _).mpr
    refine ⟨hf.continuous.continuousAt.comp (continuous_subtype_val.comp hb).continuousAt, ?_⟩
    apply ((hvalue.continuousAt (hopen.mem_nhds hmem)).comp hP).congr_of_eventuallyEq
    filter_upwards [hP.eventually (hopen.mem_nhds hmem)] with y hy
    change (et ⟨f (b y), G (b y) y.val.snd⟩).2 =
      fibreExpression A f G s t (b y) (es y.val).2
    rw [fibreExpression, ← es.continuousLinearMapAt_apply_of_mem ℝ hy.1,
      es.symmL_continuousLinearMapAt hy.1,
      et.continuousLinearMapAt_apply_of_mem ℝ hy.2]
  have hj := hasContinuousVerticalJets_extension A f r hr hf g H hδ hδR hjets
  exact ⟨δ, hδ, hδR, hcontinuous _ hj, hj, hLipschitz⟩

end HolomorphicAnosov.ExponentialCutoff
