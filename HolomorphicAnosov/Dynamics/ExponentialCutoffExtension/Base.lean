import HolomorphicAnosov.Geometry.UniformExponentialLift
import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The exponential-lift cutoff extension

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, LNM 583 (1977), proof of Theorem 5.5,
pp. 61–62, with the current node's explicit source composite.
DAG node: `hps.theorem_5_5_exponential_cutoff_extension`.

The original metric's actual geodesic exponential and the local/whole-fibre jet
notions are shared with `UniformExponentialLift`. Finite-order fibre regularity does
not assert ambient `C^r` regularity of `Tf` or of the global cutoff extension.
-/

noncomputable section

namespace HolomorphicAnosov
namespace ExponentialCutoff

open Bundle Set ExponentialLift
open scoped Manifold ContDiff Topology _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- An arbitrary continuous real fibre norm on the original tangent bundle restricted to `A`.
Source: HPS Theorem 5.5, pp. 61–62; Lee, *Introduction to Smooth Manifolds* (2003),
Lemma 11.19, p. 278. Continuity is only required on that restricted total space.
No new fibre topology, differentiability of the norm, or ambient extension is assumed. -/
structure ContinuousRestrictedTangentNorm (A : Set M) where
  value : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → ℝ
  nonneg : ∀ p v, 0 ≤ value p v
  eq_zero_iff : ∀ p v, value p v = 0 ↔ v = 0
  add_le : ∀ p v w, value p (v + w) ≤ value p v + value p w
  smul : ∀ p (a : ℝ) v, value p (a • v) = |a| * value p v
  continuous : Continuous (fun z : {z : TangentBundle 𝓘(ℝ, E) M | z.proj ∈ A} ↦
    value ⟨z.val.proj, z.property⟩ z.val.snd)

private def νSeminorm {A : Set M} (ν : ContinuousRestrictedTangentNorm (E := E) A)
    (p : A) : Seminorm ℝ (TangentSpace 𝓘(ℝ, E) (p : M)) :=
  Seminorm.of (ν.value p) (ν.add_le p) (ν.smul p)

/-- Continuity of the actual bundle map covering the given base map.
Source: HPS Theorem 5.5, pp. 61–62. The domain is the restricted original total
tangent bundle with its induced topology, not a disjoint union of bare fibres. -/
def IsContinuousBundleMap (A : Set M) (f : M → M)
    (G : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p)) :
    Prop :=
  Continuous (fun z : {z : TangentBundle 𝓘(ℝ, E) M | z.proj ∈ A} ↦
    (⟨f z.val.proj, G ⟨z.val.proj, z.property⟩ z.val.snd⟩ : TangentBundle 𝓘(ℝ, E) M))

/-- The fixed actual smooth scalar bump used in the source cutoff, with inner radius
`1/4` and outer radius `1`. Source: the bump averaging in HPS p. 62 and the
scaled-bump calculation in Merry, Lecture 32, Theorem 32.2, equations 32.6–32.7.
The coercion uses Mathlib's concrete smooth-bump construction on the real line. -/
def scalarBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 4
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The intrinsic squared-metric cutoff, equal to one on the closed half-radius
disc and zero outside the radius disc. Source: current node Steps 5–6; HPS p. 62
and Merry Lecture 32, equations 32.6–32.7. Only the given smooth metric is used. -/
def fibreCutoff
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (δ : ℝ) (p : M) (v : TangentSpace 𝓘(ℝ, E) p) : ℝ :=
  scalarBump (g.inner p v v / δ ^ 2)

/-- The actual global extension formula, with its local-lift input evaluated only
inside the original lift radius. Source: HPS p. 62 and current node Step 7.
The theorem binds `H` to the genuine exponential lift, not a supplied oracle.
The zero branch is literal zero before adding the original manifold derivative. -/
def extension (A : Set M) (f : M → M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (R δ : ℝ) (p : A) (v : TangentSpace 𝓘(ℝ, E) (p : M)) :
    TangentSpace 𝓘(ℝ, E) (f p) :=
  mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v +
    if metricNorm g p v < R then
      fibreCutoff g δ p v • (H p v - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v)
    else 0

/-- The actual derivative of `f` expressed in the original source and receiving
tangent model identifications. Source: HPS p. 62, the equation `DG_p(0) = Tf_p`.
No normed-space structure is installed on the tangent fibres themselves. -/
def modelDerivative (f : M → M) (p : M) : E →L[ℝ] E :=
  (tangentSpaceCastModel 𝓘(ℝ, E) (f p)).toContinuousLinearMap.comp
    ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f p).comp
      (tangentSpaceCastModel 𝓘(ℝ, E) p).symm.toContinuousLinearMap)

/-- The geometric and regularity assertions of the cutoff extension, except its
inner-domain exponential identity, which is stated using the shared genuine
exponential interface. Source: HPS Theorem 5.5, pp. 61–62; current node Steps 1–9.
The Lipschitz estimate uses exactly the supplied arbitrary continuous norm on both
original fibres. The exterior assertion uses a single uniform finite radius. -/
def IsGlobalExtension (A : Set M) (f : M → M) (hfA : MapsTo f A A) (r : ℕ∞)
    (ν : ContinuousRestrictedTangentNorm (E := E) A) (ε : ℝ)
    (G : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p)) :
    Prop :=
  IsContinuousBundleMap A f G ∧ HasContinuousVerticalJets A f r G ∧
    (∀ p : A, G p 0 = 0) ∧
    (∀ p : A, HasFDerivAt
      (fun u : E ↦ tangentSpaceCastModel 𝓘(ℝ, E) (f p)
        (G p ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm u)))
      (modelDerivative f p) 0) ∧
    (∀ (p : A) (v w : TangentSpace 𝓘(ℝ, E) (p : M)),
      ν.value ⟨f p, hfA p.property⟩
        ((G p v - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v) -
          (G p w - mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) w)) ≤
        ε * ν.value p (v - w)) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ (p : A) (v : TangentSpace 𝓘(ℝ, E) (p : M)),
      c < ν.value p v → G p v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The squared metric norm recovers the given quadratic form. This is the
fixed-fibre identity used in HPS p. 62's cutoff construction. -/
private theorem metricNorm_sq
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (v : TangentSpace 𝓘(ℝ, E) p) :
    metricNorm g p v ^ 2 = g.inner p v v := by
  apply Real.sq_sqrt
  by_cases hv : v = 0
  · simp [hv]
  · exact (g.pos p v hv).le

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The concrete cutoff equals one on the closed half-radius metric disc.
Source: HPS p. 62, implemented with the stated scalar bump and its closed inner ball. -/
theorem fibreCutoff_one
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {δ : ℝ} (hδ : 0 < δ) (p : M) (v : TangentSpace 𝓘(ℝ, E) p)
    (hv : metricNorm g p v ≤ δ / 2) : fibreCutoff g δ p v = 1 := by
  apply scalarBump.one_of_mem_closedBall
  have hn : 0 ≤ metricNorm g p v := Real.sqrt_nonneg _
  have hs := metricNorm_sq g p v
  have hq : 0 ≤ g.inner p v v := by rw [← hs]; positivity
  change dist (g.inner p v v / δ ^ 2) 0 ≤ 1 / 4
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hq (sq_nonneg δ))]
  apply (div_le_iff₀ (sq_pos_of_pos hδ)).2
  nlinarith [sq_nonneg (δ / 2 - metricNorm g p v)]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The concrete cutoff vanishes at and outside its metric radius.
Source: the compactly supported averaging in HPS p. 62. -/
theorem fibreCutoff_zero
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    {δ : ℝ} (hδ : 0 < δ) (p : M) (v : TangentSpace 𝓘(ℝ, E) p)
    (hv : δ ≤ metricNorm g p v) : fibreCutoff g δ p v = 0 := by
  apply scalarBump.zero_of_le_dist
  have hn : 0 ≤ metricNorm g p v := Real.sqrt_nonneg _
  have hs := metricNorm_sq g p v
  have hq : 0 ≤ g.inner p v v := by rw [← hs]; positivity
  change 1 ≤ dist (g.inner p v v / δ ^ 2) 0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hq (sq_nonneg δ))]
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).2
  nlinarith

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The extension agrees with its original lift on the closed inner disc.
Source: HPS p. 62; this is Step 9 of the present composite proof. -/
theorem extension_eq_lift
    (A : Set M) (f : M → M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    {R δ : ℝ} (hδ : 0 < δ) (hδR : δ < R)
    (p : A) (v : TangentSpace 𝓘(ℝ, E) (p : M))
    (hv : metricNorm g p v ≤ δ / 2) : extension A f g H R δ p v = H p v := by
  have hvR : metricNorm g p v < R := by linarith
  simp [extension, hvR, fibreCutoff_one g hδ p v hv]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The extension agrees with the original derivative outside the cutoff radius,
even when the original lift is evaluated by an arbitrary totalization.
Source: HPS p. 62; Step 7's two branches are both zero in the exterior region. -/
theorem extension_eq_derivative
    (A : Set M) (f : M → M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    {R δ : ℝ} (hδ : 0 < δ) (p : A) (v : TangentSpace 𝓘(ℝ, E) (p : M))
    (hv : δ ≤ metricNorm g p v) :
    extension A f g H R δ p v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v := by
  simp [extension, fibreCutoff_zero g hδ p v hv]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Smoothness of the concrete squared-metric cutoff on each original fibre,
expressed using the original tangent-model identification. Source: Step 5 of the
HPS cutoff composite; a continuous bilinear quadratic form followed by the smooth bump. -/
theorem contDiff_fibreCutoff
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (δ : ℝ) (p : M) (r : ℕ∞) :
    ContDiff ℝ r (fun u : E ↦
      fibreCutoff g δ p ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm u)) := by
  unfold fibreCutoff
  apply scalarBump.contDiff.comp
  fun_prop

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Continuity of the metric radius in the original tangent-model coordinates.
Source: Step 7 of the HPS cutoff composite, to justify its two genuine open regions. -/
private theorem continuous_modelMetricNorm
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) : Continuous (fun u : E ↦
      metricNorm g p ((tangentSpaceCastModel 𝓘(ℝ, E) p).symm u)) := by
  unfold metricNorm
  fun_prop

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The actual product/zero extension is globally `C^r` on each original fibre,
provided the original lift is `C^r` on its genuine radius disc. No regularity of
its off-domain totalization is used. Source: HPS p. 62, Lee's product/zero gluing,
and Step 7 of the current composite. At radii below `R` use the local product;
at radii above `δ` use the derivative; the two open sets cover because `δ < R`. -/
theorem contDiff_extension_fibre
    (A : Set M) (f : M → M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    {R δ : ℝ} (hδ : 0 < δ) (hδR : δ < R) (p : A) (r : ℕ∞)
    (hH : ContDiffOn ℝ r (fun u : E ↦
      tangentSpaceCastModel 𝓘(ℝ, E) (f p)
        (H p ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm u)))
      {u | metricNorm g p ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm u) < R}) :
    ContDiff ℝ r (fun u : E ↦
      tangentSpaceCastModel 𝓘(ℝ, E) (f p)
        (extension A f g H R δ p ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm u))) := by
  let J := (tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm
  have hL : ContDiff ℝ r (modelDerivative (E := E) f p) :=
    (modelDerivative (E := E) f p).contDiff
  have hχ := contDiff_fibreCutoff g δ (p : M) r
  have hn := continuous_modelMetricNorm g (p : M)
  apply contDiff_iff_contDiffAt.mpr
  intro u
  by_cases hu : metricNorm g p (J u) < R
  · have hU : {w : E | metricNorm g p (J w) < R} ∈ 𝓝 u :=
      (isOpen_lt hn continuous_const).mem_nhds hu
    have hprod := hL.contDiffAt.add ((hχ.contDiffAt).smul
      ((hH.contDiffAt hU).sub hL.contDiffAt))
    apply hprod.congr_of_eventuallyEq
    filter_upwards [hU] with w hw
    simp [extension, hw, J, modelDerivative, map_add, map_sub, map_smul]
  · have huδ : δ < metricNorm g p (J u) := lt_of_lt_of_le hδR (le_of_not_gt hu)
    have hV : {w : E | δ < metricNorm g p (J w)} ∈ 𝓝 u :=
      (isOpen_lt continuous_const hn).mem_nhds huδ
    apply hL.contDiffAt.congr_of_eventuallyEq
    filter_upwards [hV] with w hw
    rw [extension_eq_derivative A f g H hδ p (J w) hw.le]
    rfl

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The global extension preserves the original lift's value at the zero section.
Source: the inner-disc equality in Step 9 of the HPS cutoff composite. -/
theorem extension_zero
    (A : Set M) (f : M → M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    {R δ : ℝ} (hδ : 0 < δ) (hδR : δ < R) (p : A) (hH : H p 0 = 0) :
    extension A f g H R δ p 0 = 0 := by
  rw [extension_eq_lift A f g H hδ hδR p 0, hH]
  simpa [metricNorm] using (half_pos hδ).le

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The extension preserves the original lift's first derivative at zero, in the
same actual source and receiving tangent models. Source: Step 9 of the HPS cutoff
composite. The maps agree on the open half-radius disc, so their derivatives agree. -/
theorem hasFDerivAt_extension_zero
    (A : Set M) (f : M → M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    {R δ : ℝ} (hδ : 0 < δ) (hδR : δ < R) (p : A)
    (hH : HasFDerivAt (fun u : E ↦ tangentSpaceCastModel 𝓘(ℝ, E) (f p)
      (H p ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm u)))
      (modelDerivative f p) 0) :
    HasFDerivAt (fun u : E ↦ tangentSpaceCastModel 𝓘(ℝ, E) (f p)
      (extension A f g H R δ p ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm u)))
      (modelDerivative f p) 0 := by
  apply hH.congr_of_eventuallyEq
  have hn := continuous_modelMetricNorm g (p : M)
  have hU : {u : E |
      metricNorm g p ((tangentSpaceCastModel 𝓘(ℝ, E) (p : M)).symm u) < δ / 2} ∈ 𝓝 0 :=
    (isOpen_lt hn continuous_const).mem_nhds (by simpa [metricNorm] using half_pos hδ)
  filter_upwards [hU] with u hu
  rw [extension_eq_lift A f g H hδ hδR p _ hu.le]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- A lower comparison of the auxiliary norm with the metric norm converts the
uniform auxiliary radius into the closed inner metric disc used by the cutoff.
Source: HPS p. 62 together with Lee's compact-sphere comparison (Lemma 11.19,
p.278). This is the exact endpoint inequality behind the choice `b = m δ / 2`. -/
theorem inner_metric_radius_of_auxiliary_bound
    (A : Set M) (ν : ContinuousRestrictedTangentNorm (E := E) A)
    {m δ b : ℝ} (hm : 0 < m) (hb : b = m * δ / 2)
    {p : A} {v : TangentSpace 𝓘(ℝ, E) (p : M)}
    (hcompare : m * metricNorm g (p : M) v ≤ ν.value p v)
    (hv : ν.value p v ≤ b) : metricNorm g (p : M) v ≤ δ / 2 := by
  nlinarith

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The corresponding exterior implication uses the upper comparison from Lee's
compact-sphere argument. It is the edge condition for the single global radius
in the HPS extension statement. -/
theorem exterior_metric_radius_of_auxiliary_bound
    (A : Set M) (ν : ContinuousRestrictedTangentNorm (E := E) A)
    {M₀ δ c : ℝ} (hM : 0 < M₀) (hc : c = M₀ * δ)
    {p : A} {v : TangentSpace 𝓘(ℝ, E) (p : M)}
    (hcompare : ν.value p v ≤ M₀ * metricNorm g (p : M) v)
    (hv : c < ν.value p v) : δ < metricNorm g (p : M) v := by
  nlinarith

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The inner endpoint clause for the source extension: the auxiliary closed ball
is carried into the region where the cutoff is identically one. -/
theorem extension_eq_lift_of_auxiliary_bound
    (A : Set M) (f : M → M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (ν : ContinuousRestrictedTangentNorm (E := E) A)
    {m δ b R : ℝ} (hm : 0 < m) (hδ : 0 < δ) (hδR : δ < R)
    (hb : b = m * δ / 2) {p : A}
    {v : TangentSpace 𝓘(ℝ, E) (p : M)}
    (hcompare : m * metricNorm g (p : M) v ≤ ν.value p v)
    (hv : ν.value p v ≤ b) : extension A f g H R δ p v = H p v := by
  apply extension_eq_lift A f g H hδ hδR p v
  exact inner_metric_radius_of_auxiliary_bound A ν hm hb hcompare hv

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The exterior endpoint clause for the source extension: beyond one uniform
auxiliary radius the extension is exactly the original tangent derivative. -/
theorem extension_eq_derivative_of_auxiliary_bound
    (A : Set M) (f : M → M)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (H : ∀ p : A, TangentSpace 𝓘(ℝ, E) (p : M) → TangentSpace 𝓘(ℝ, E) (f p))
    (ν : ContinuousRestrictedTangentNorm (E := E) A)
    {M₀ δ c R : ℝ} (hM : 0 < M₀) (hδ : 0 < δ) (hc : c = M₀ * δ) {p : A}
    {v : TangentSpace 𝓘(ℝ, E) (p : M)}
    (hcompare : ν.value p v ≤ M₀ * metricNorm g (p : M) v)
    (hv : c < ν.value p v) : extension A f g H R δ p v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (p : M) v := by
  apply extension_eq_derivative A f g H hδ p v
  exact (exterior_metric_radius_of_auxiliary_bound A ν hM hc hcompare hv).le

omit [T2Space M] in
/-- Finite compact cores for the original tangent frames over a compact set.
Source: Lee (2003), Lemma 1.6 and Proposition 2.24, the compact chart-neighborhood
and finite-subcover construction used in Step 2 of the cutoff proof. Mathlib's
manifold local compactness is obtained by compact subsets of the original charts;
its finite-subcover theorem uses the directed family of finite open unions.
The cores are ambient compact sets; intersecting with `A` gives the relative cores.
Empty `A` and zero-dimensional models require no separate nonempty-sphere premise. -/
theorem exists_finite_compact_tangent_frame_cores (A : Set M) (hA : IsCompact A) :
    ∃ (K : A → Set M) (t : Finset A),
      (∀ p, IsCompact (K p) ∧ (p : M) ∈ interior (K p) ∧
        K p ⊆ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (p : M)).baseSet) ∧
      A ⊆ ⋃ p ∈ t, interior (K p) := by
  classical
  let : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) 𝓘(ℝ, E)
  have hcore : ∀ p : A, ∃ K : Set M, IsCompact K ∧ (p : M) ∈ interior K ∧
      K ⊆ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (p : M)).baseSet := by
    intro p
    apply exists_compact_subset
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (p : M)).open_baseSet
    exact FiberBundle.mem_baseSet_trivializationAt E (TangentSpace 𝓘(ℝ, E)) (p : M)
  choose K hK using hcore
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun p ↦ interior (K p))
    (fun _ ↦ isOpen_interior) (fun p hp ↦ mem_iUnion.mpr ⟨⟨p, hp⟩, (hK ⟨p, hp⟩).2.1⟩)
  exact ⟨K, t, hK, ht⟩


theorem local_tangent_norm_comparison_reverse
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) (ν : ContinuousRestrictedTangentNorm (E := E) A)
    (K : Set M) (hK : IsCompact K)
    (e : Bundle.Trivialization E
      (TotalSpace.proj (F := E) (E := fun p : M ↦ TangentSpace 𝓘(ℝ, E) p)))
    (he : e.IsLinear ℝ) (hKe : K ⊆ e.baseSet) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : A), (p : M) ∈ K → ∀ v,
      metricNorm g (p : M) v ≤ C * ν.value p v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
  let metricSeminorm : ∀ p : A, Seminorm ℝ (TangentSpace 𝓘(ℝ, E) (p : M)) :=
    fun p ↦ Seminorm.of (fun v ↦ ‖v‖)
      (fun v w ↦ norm_add_le _ _) (fun a v ↦ norm_smul _ _)
  have hmetric : Continuous (fun z : TangentBundle 𝓘(ℝ, E) M ↦
      metricNorm g z.proj z.snd) := by
    unfold metricNorm
    have h := Continuous.inner_bundle (F := E)
      (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
      (b := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.proj)
      (v := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.snd)
      (w := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.snd) continuous_id continuous_id
    exact Real.continuous_sqrt.comp h
  let : e.IsLinear ℝ := he
  let X := {p : M // p ∈ A ∩ K}
  let : CompactSpace X := isCompact_iff_compactSpace.mp (hA.inter_right hK.isClosed)
  let frame (y : X) : E →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) (y.1 : M) :=
    (e.linearEquivAt ℝ (y.1 : M) (hKe y.2.2)).symm.toLinearMap
  have hf : Continuous (fun z : X × E ↦
      (⟨(z.1 : M), frame z.1 z.2⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    let coords : X × E → M × E := fun z ↦ (z.1, z.2)
    have hc : Continuous coords := by
      simpa [coords] using (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact e.continuousOn_symm.comp_continuous hc
      (fun z ↦ ⟨hKe z.1.2.2, mem_univ _⟩)
  let pX : X → Seminorm ℝ E := fun y ↦
    (metricSeminorm ⟨y.1, y.2.1⟩).comp (frame y)
  let qX : X → Seminorm ℝ E := fun y ↦
    (νSeminorm ν ⟨y.1, y.2.1⟩).comp (frame y)
  have hpX : Continuous (fun z : X × E ↦ pX z.1 z.2) := by
    have hmc := hmetric.comp hf
    change Continuous (fun z : X × E ↦ ‖frame z.1 z.2‖)
    convert hmc using 1
    ext z
    rfl
  have hqX : Continuous (fun z : X × E ↦ qX z.1 z.2) := by
    have hfr : Continuous (fun z : X × E ↦
        (⟨⟨z.1, frame z.1 z.2⟩, z.1.2.1⟩ :
          {z : TangentBundle 𝓘(ℝ, E) M | z.proj ∈ A})) := by
      apply hf.subtype_mk
    change Continuous (fun z : X × E ↦ ν.value ⟨z.1, z.1.2.1⟩ (frame z.1 z.2))
    convert ν.continuous.comp hfr using 1
    ext z
    rfl
  have hqXpos : ∀ y v, v ≠ 0 → 0 < qX y v := by
    intro y v hv
    have hframe : frame y v ≠ 0 := by
      intro hz
      apply hv
      exact (e.linearEquivAt ℝ (y.1 : M) (hKe y.2.2)).symm.injective (by
        simpa [frame, map_zero] using hz)
    have hval : ν.value ⟨y.1, y.2.1⟩ (frame y v) ≠ 0 := by
      intro hz
      exact hframe ((ν.eq_zero_iff ⟨y.1, y.2.1⟩ (frame y v)).mp hz)
    exact lt_of_le_of_ne (ν.nonneg _ _) (Ne.symm hval)
  obtain ⟨C, hC, hbound⟩ := Preparation.uniform_seminorm_upper_bound pX qX hpX hqX hqXpos
  refine ⟨C, hC, ?_⟩
  intro p hp v
  let y : X := ⟨p, ⟨p.property, hp⟩⟩
  have hbound' := hbound y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v)
  have heq : frame y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v) = v := by
    exact (e.linearEquivAt ℝ (p : M) (hKe hp)).symm_apply_apply v
  change metricNorm g (p : M) (frame y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v)) ≤
      C * ν.value p (frame y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v)) at hbound'
  rw [heq] at hbound'
  simpa using hbound'


theorem local_tangent_norm_comparison_forward_adapter
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A) (ν : ContinuousRestrictedTangentNorm (E := E) A)
    (K : Set M) (hK : IsCompact K)
    (e : Bundle.Trivialization E
      (TotalSpace.proj (F := E) (E := fun p : M ↦ TangentSpace 𝓘(ℝ, E) p)))
    (he : e.IsLinear ℝ)
    (hKe : K ⊆ e.baseSet) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : A), (p : M) ∈ K → ∀ v,
      ν.value p v ≤ C * metricNorm g (p : M) v := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) :=
    ⟨g.toContinuousRiemannianMetric.toRiemannianMetric⟩
  let : e.IsLinear ℝ := he
  let X := {p : M // p ∈ A ∩ K}
  let : CompactSpace X := isCompact_iff_compactSpace.mp (hA.inter_right hK.isClosed)
  let frame (y : X) : E →ₗ[ℝ] TangentSpace 𝓘(ℝ, E) (y.1 : M) :=
    (e.linearEquivAt ℝ (y.1 : M) (hKe y.2.2)).symm.toLinearMap
  let coords : X × E → M × E := fun z ↦ (z.1, z.2)
  have hcoords : Continuous coords := by
    simpa [coords] using (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hf : Continuous (fun z : X × E ↦
      (⟨(z.1 : M), frame z.1 z.2⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
    have hc := e.continuousOn_symm.comp_continuous hcoords
      (fun z ↦ ⟨hKe z.1.2.2, mem_univ _⟩)
    exact hc
  let pX : X → Seminorm ℝ E := fun y ↦ (νSeminorm ν ⟨y.1, y.2.1⟩).comp (frame y)
  let qX : X → Seminorm ℝ E := fun y ↦ Seminorm.of (fun v ↦ ‖frame y v‖)
    (fun v w ↦ by rw [map_add]; exact norm_add_le _ _)
    (fun a v ↦ by rw [map_smul, norm_smul])
  have hpX : Continuous (fun z : X × E ↦ pX z.1 z.2) := by
    have hfr : Continuous (fun z : X × E ↦
        (⟨⟨z.1, frame z.1 z.2⟩, z.1.2.1⟩ :
          {z : TangentBundle 𝓘(ℝ, E) M | z.proj ∈ A})) := by
      apply hf.subtype_mk
    change Continuous (fun z : X × E ↦ ν.value ⟨z.1, z.1.2.1⟩ (frame z.1 z.2))
    convert ν.continuous.comp hfr using 1
    ext z
    rfl
  have hqX : Continuous (fun z : X × E ↦ qX z.1 z.2) := by
    have hm : Continuous (fun z : TangentBundle 𝓘(ℝ, E) M ↦
        metricNorm g z.proj z.snd) := by
      unfold metricNorm
      have h := Continuous.inner_bundle (F := E)
        (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
        (b := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.proj)
        (v := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.snd)
        (w := fun p : TangentBundle 𝓘(ℝ, E) M ↦ p.snd) continuous_id continuous_id
      exact Real.continuous_sqrt.comp h
    have hmc := hm.comp hf
    change Continuous (fun z : X × E ↦ metricNorm g (z.1 : M) (frame z.1 z.2))
    convert hmc using 1
    ext z
    rfl
  have hqXpos : ∀ y v, v ≠ 0 → 0 < qX y v := by
    intro y v hv
    have hframe : frame y v ≠ 0 := by
      intro hz
      have hz' : (e.linearEquivAt ℝ (y.1 : M) (hKe y.2.2)).symm v = 0 := by
        simpa [frame] using hz
      exact hv ((e.linearEquivAt ℝ (y.1 : M) (hKe y.2.2)).symm.injective (by
        simpa [map_zero] using hz'))
    exact norm_pos_iff.mpr hframe
  obtain ⟨C, hC, hbound⟩ := Preparation.uniform_seminorm_upper_bound pX qX hpX hqX hqXpos
  refine ⟨C, hC, ?_⟩
  intro p hp v
  let y : X := ⟨p, ⟨p.property, hp⟩⟩
  have hbound' := hbound y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v)
  have he : frame y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v) = v := by
    exact (e.linearEquivAt ℝ (p : M) (hKe hp)).symm_apply_apply v
  have hbound'' : ν.value p (frame y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v)) ≤
      C * metricNorm g (p : M) (frame y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v)) := by
    change ν.value p (frame y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v)) ≤
      C * ‖frame y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v)‖ at hbound'
    simpa only [show metricNorm g (p : M) (frame y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v)) =
      ‖frame y ((e.linearEquivAt ℝ (p : M) (hKe hp)) v)‖ by rfl] using hbound'
  rw [he] at hbound''
  simpa [metricNorm] using hbound''



/-- Finite-core application of the canonical reverse comparison and the forward
adapter above. The finite core cover supplies the chart-local hypotheses; the
only missing canonical API this adapter supplies is the forward direction.
-/
theorem finite_core_two_sided_norm_comparison_from_canonical
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (A : Set M) (hA : IsCompact A)
    (ν : ContinuousRestrictedTangentNorm (E := E) A) :
    ∃ m M₀ : ℝ, 0 < m ∧ 0 < M₀ ∧
      (∀ q : A, ∀ v,
        m * metricNorm g (q : M) v ≤ ν.value q v) ∧
      (∀ q : A, ∀ v,
        ν.value q v ≤ M₀ * metricNorm g (q : M) v) := by
  classical
  obtain ⟨K, t, hK, hcover⟩ := exists_finite_compact_tangent_frame_cores (E := E) A hA
  have hrev : ∀ p : A, ∃ C : ℝ, 1 ≤ C ∧
      ∀ q : A, (q : M) ∈ K p → ∀ v,
        metricNorm g (q : M) v ≤ C * ν.value q v := by
    intro p
    exact local_tangent_norm_comparison_reverse g A hA ν (K p) (hK p).1
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (p : M))
      (by infer_instance) (hK p).2.2
  have hfwd : ∀ p : A, ∃ C : ℝ, 1 ≤ C ∧
      ∀ q : A, (q : M) ∈ K p → ∀ v,
        ν.value q v ≤ C * metricNorm g (q : M) v := by
    intro p
    exact local_tangent_norm_comparison_forward_adapter g A hA ν (K p) (hK p).1
      (trivializationAt E (TangentSpace 𝓘(ℝ, E)) (p : M))
      (by infer_instance) (hK p).2.2
  choose cRev hcRev hRev using hrev
  choose cFwd hcFwd hFwd using hfwd
  let smin : Finset ℝ := t.image (fun p ↦ (cRev p)⁻¹)
  let smax : Finset ℝ := t.image cFwd
  by_cases ht : t.Nonempty
  · have hsmin : smin.Nonempty := Finset.image_nonempty.mpr ht
    have hsmax : smax.Nonempty := Finset.image_nonempty.mpr ht
    let m : ℝ := smin.min' hsmin
    let M₀ : ℝ := smax.max' hsmax
    have hmpos : 0 < m := by
      have hm_mem : m ∈ smin := Finset.min'_mem smin hsmin
      obtain ⟨p, hp, hpm⟩ := Finset.mem_image.mp hm_mem
      rw [← hpm]
      exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (hcRev p))
    have hMpos : 0 < M₀ := by
      have hM_mem : M₀ ∈ smax := Finset.max'_mem smax hsmax
      obtain ⟨p, hp, hpM⟩ := Finset.mem_image.mp hM_mem
      rw [← hpM]
      exact lt_of_lt_of_le zero_lt_one (hcFwd p)
    refine ⟨m, M₀, hmpos, hMpos, ?_, ?_⟩
    · intro q v
      have hqcover : q.val ∈ ⋃ p ∈ t, interior (K p) := hcover q.property
      obtain ⟨p, hqcover⟩ := Set.mem_iUnion.mp hqcover
      obtain ⟨hp, hqint⟩ := Set.mem_iUnion.mp hqcover
      have hqK : q.val ∈ K p := interior_subset hqint
      have hmc : m ≤ (cRev p)⁻¹ := by
        exact Finset.min'_le smin ((cRev p)⁻¹)
          (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      have hnorm : 0 ≤ metricNorm g q.val v := by
        unfold metricNorm
        exact Real.sqrt_nonneg _
      have hscaled : m * metricNorm g q.val v ≤
          (cRev p)⁻¹ * metricNorm g q.val v :=
        mul_le_mul_of_nonneg_right hmc hnorm
      have hrev' := hRev p q hqK v
      have hconvert : (cRev p)⁻¹ * metricNorm g q.val v ≤ ν.value q v := by
        have hcpos : 0 < cRev p := lt_of_lt_of_le zero_lt_one (hcRev p)
        rw [inv_mul_le_iff₀ hcpos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hrev'
      exact hscaled.trans hconvert
    · intro q v
      have hqcover : q.val ∈ ⋃ p ∈ t, interior (K p) := hcover q.property
      obtain ⟨p, hqcover⟩ := Set.mem_iUnion.mp hqcover
      obtain ⟨hp, hqint⟩ := Set.mem_iUnion.mp hqcover
      have hqK : q.val ∈ K p := interior_subset hqint
      have hcm : cFwd p ≤ M₀ := by
        exact Finset.le_max' smax (cFwd p)
          (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      have hnorm : 0 ≤ metricNorm g q.val v := by
        unfold metricNorm
        exact Real.sqrt_nonneg _
      exact (hFwd p q hqK v).trans
        (mul_le_mul_of_nonneg_right hcm hnorm)
  · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    have hAempty : A = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hAn
      obtain ⟨q, hq⟩ := hAn
      have hqcover := hcover hq
      simp [ht0] at hqcover
    subst A
    refine ⟨1, 1, by norm_num, by norm_num, ?_, ?_⟩
    · intro q _
      exact q.property.elim
    · intro q _
      exact q.property.elim


/-- The fixed bump has a finite derivative bound. Source: Step 5 of the
HPS p.62 cutoff composite and Merry Lecture 32, equations 32.6--32.7.
Compact support and smoothness give the bound for the actual chosen bump;
no prescribed numerical derivative bound is assumed. -/
theorem scalarBump_derivative_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, |deriv scalarBump t| ≤ K := by
  obtain ⟨K, hK, hbound⟩ := scalarBump.hasCompactSupport.exists_bound_iteratedFDeriv
    (scalarBump.contDiff : ContDiff ℝ ∞ scalarBump) 1
  refine ⟨K, hK, fun t ↦ ?_⟩
  simpa only [norm_iteratedFDeriv_one, ← norm_deriv_eq_norm_fderiv, Real.norm_eq_abs]
    using hbound 1 le_rfl t

/-- The fixed bump derivative vanishes at the outer boundary as well as beyond
it. Source: Step 5 of the HPS cutoff composite. Outside the boundary the bump
is locally zero; continuity of its derivative gives the boundary value. -/
theorem scalarBump_derivative_zero {t : ℝ} (ht : 1 ≤ t) : deriv scalarBump t = 0 := by
  have hcont : Continuous (deriv scalarBump) :=
    (scalarBump.contDiff : ContDiff ℝ ∞ scalarBump).continuous_deriv (by simp)
  have hzero : Set.Ioi (1 : ℝ) ⊆ {t | deriv scalarBump t = 0} := by
    intro t ht
    apply HasDerivAt.deriv
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact (scalarBump.zero_of_le_dist (by
      change (1 : ℝ) ≤ dist s 0
      rw [Real.dist_eq, sub_zero, abs_of_pos (lt_trans zero_lt_one hs)]
      exact hs.le))
  have hclosed : IsClosed {t : ℝ | deriv scalarBump t = 0} :=
    isClosed_eq hcont continuous_const
  exact closure_minimal hzero hclosed (by simpa only [closure_Ioi, Set.mem_Ici] using ht)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Differentiate the actual squared-metric cutoff along a line in the original
tangent fibre. Source: Step 6 of the HPS cutoff composite and Merry (32.6).
Bilinearity expands the quadratic into a real polynomial, and the scalar chain
rule gives the formula without changing the native tangent norm or topology. -/
theorem hasDerivAt_fibreCutoff_line
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (δ : ℝ) (p : M) (v w : TangentSpace 𝓘(ℝ, E) p) :
    HasDerivAt (fun t : ℝ ↦ fibreCutoff g δ p (v + t • w))
      (deriv scalarBump (g.inner p v v / δ ^ 2) *
        ((g.inner p v w + g.inner p w v) / δ ^ 2)) 0 := by
  have hpoly : HasDerivAt
      (fun t : ℝ ↦ (g.inner p v v + t * (g.inner p v w + g.inner p w v) +
        t ^ 2 * g.inner p w w) / δ ^ 2)
      ((g.inner p v w + g.inner p w v) / δ ^ 2) 0 := by
    convert (((hasDerivAt_const (0 : ℝ) (g.inner p v v)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (g.inner p v w + g.inner p w v))).add
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (g.inner p w w))).div_const (δ ^ 2) using 1 <;>
      norm_num
  have hb := (((scalarBump.contDiff : ContDiff ℝ ∞ scalarBump).differentiable (by simp))
    (g.inner p v v / δ ^ 2)).hasDerivAt
  have hp : HasDerivAt (fun t : ℝ ↦ g.inner p (v + t • w) (v + t • w) / δ ^ 2)
      ((g.inner p v w + g.inner p w v) / δ ^ 2) 0 := by
    convert hpoly using 1
    ext t
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
    ring
  have hb' : HasDerivAt scalarBump (deriv scalarBump (g.inner p v v / δ ^ 2))
      (g.inner p (v + (0 : ℝ) • w) (v + (0 : ℝ) • w) / δ ^ 2) := by
    simpa only [zero_smul, add_zero] using hb
  convert! hb'.comp 0 hp using 1


end ExponentialCutoff
end HolomorphicAnosov
