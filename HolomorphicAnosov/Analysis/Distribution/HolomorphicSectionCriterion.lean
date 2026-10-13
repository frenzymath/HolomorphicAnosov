import HolomorphicAnosov.Analysis.Distribution.DbarClosedScalarCurrentHolomorphic
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# A distributional criterion for holomorphic bundle sections

Source: Zhang, *Codimension-one holomorphic Anosov diffeomorphisms*, Lemma 4.1,
pp.13–14; Demailly, *Complex Analytic and Differential Geometry* (June 21, 2012),
Chapter I §3.E, Lemma (3.29)(a), pp.28–29, with p=q=0.
DAG node: `zhang.distributional_holomorphic_section_criterion`.

The finite-rank holomorphic bundle is the genuine Mathlib complex vector bundle
with complex C∞ transition functions. In finite complex coordinates this is
the holomorphic transition condition. A holomorphic section is complex C∞ as a
map into its native total space, equivalently holomorphic in local holomorphic
frames. All weak tests use unconjugated multiplication and real Lebesgue volume.
-/

open Bundle Filter MeasureTheory TopologicalSpace Set
open scoped ContDiff Manifold Topology _root_.Topology

namespace HolomorphicAnosov.DistributionalSection

noncomputable section

universe u v

variable {d r : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (Fin d → ℂ) X]
  {V : X → Type v} [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace (Fin r → ℂ) V)]
  [FiberBundle (Fin r → ℂ) V] [VectorBundle ℂ (Fin r → ℂ) V]
  [ContMDiffVectorBundle ∞ (Fin r → ℂ) V 𝓘(ℂ, Fin d → ℂ)]

/-- A genuine fiberwise complex-linear holomorphic frame: both its coordinate
map and inverse are complex smooth on their actual open domains. Source:
Demailly I §3.E and Zhang Lemma 4.1, local holomorphic frames. -/
def IsHolomorphicFrame
    (e : Trivialization (Fin r → ℂ) (TotalSpace.proj : TotalSpace (Fin r → ℂ) V → X)) :
    Prop :=
  e.IsLinear ℂ ∧
    ContMDiffOn (𝓘(ℂ, Fin d → ℂ).prod 𝓘(ℂ, Fin r → ℂ))
      (𝓘(ℂ, Fin d → ℂ).prod 𝓘(ℂ, Fin r → ℂ)) ∞ e e.source ∧
    ContMDiffOn (𝓘(ℂ, Fin d → ℂ).prod 𝓘(ℂ, Fin r → ℂ))
      (𝓘(ℂ, Fin d → ℂ).prod 𝓘(ℂ, Fin r → ℂ)) ∞
      e.toOpenPartialHomeomorph.symm e.target

/-- The exact open chart domain where the chosen frame is defined. Source:
Zhang pp.13–14, distributional convergence in a local holomorphic frame. -/
def frameDomain (c : OpenPartialHomeomorph X (Fin d → ℂ))
    (e : Trivialization (Fin r → ℂ) (TotalSpace.proj : TotalSpace (Fin r → ℂ) V → X)) :
    Opens (Fin d → ℂ) :=
  ⟨c.target ∩ c.symm ⁻¹' e.baseSet, c.isOpen_inter_preimage_symm e.open_baseSet⟩

/-- Literal scalar frame coefficient of the original section in the original
chart. Values outside `frameDomain` are immaterial. Source: Zhang Lemma 4.1. -/
def coefficient (s : ∀ x, V x) (c : OpenPartialHomeomorph X (Fin d → ℂ))
    (e : Trivialization (Fin r → ℂ) (TotalSpace.proj : TotalSpace (Fin r → ℂ) V → X))
    (k : Fin r) (z : Fin d → ℂ) : ℂ :=
  (e (TotalSpace.mk' (Fin r → ℂ) (c.symm z) (s (c.symm z)))).2 k

/-- Unconjugated regular-distribution pairing on the original open coordinate
domain. Source: Zhang p.13 and Demailly I §2, distributions. -/
def regularPairing (Ω : Opens (Fin d → ℂ)) (a : (Fin d → ℂ) → ℂ)
    (φ : TestFunction Ω ℂ ⊤) : ℂ :=
  ∫ z in (Ω : Set (Fin d → ℂ)), a z * φ z ∂volume

/-- The distributional antiholomorphic derivative evaluated on the same test:
minus pairing with (∂x_j φ+i∂y_j φ)/2. Source: Zhang Lemma 4.1 and Demailly I §3.E. -/
def dbarPairing (Ω : Opens (Fin d → ℂ)) (a : (Fin d → ℂ) → ℂ)
    (j : Fin d) (φ : TestFunction Ω ℂ ⊤) : ℂ :=
  -regularPairing Ω a ((2 : ℂ)⁻¹ •
    ((TestFunction.lineDerivCLM ℂ (Pi.single j 1) φ : TestFunction Ω ℂ ⊤) +
      Complex.I • (TestFunction.lineDerivCLM ℂ (Pi.single j Complex.I) φ :
        TestFunction Ω ℂ ⊤)))

/-- Continuous sections whose coefficients converge weakly and whose
distributional antiholomorphic derivatives converge weakly to zero have a
holomorphic limit section.

Source: Zhang Lemma 4.1, pp.13–14; Demailly I §3.E, Lemma (3.29)(a), pp.28–29,
specialized to scalar currents p=q=0. The formal proof uses the named scalar-current
and polydisc providers. The hypotheses do not assume differentiability of the
approximating sections or any classical derivative for their coefficients.

Natural-language proof.
W1. Fix a compatible complex chart and a genuine local holomorphic frame.
Every coefficient a_n,a is continuous on the exact open domain Ω, by continuity
of the original sections, chart inverse and frame. If d=0 the domain is discrete
and all coefficients are holomorphic. Otherwise continuity gives local
integrability for real Euclidean Lebesgue volume. They therefore determine
regular distributions. Mathlib's real-test, complex-output presentation extends
to complex tests by T(φ+iχ)=T(φ)+iT(χ). Test integrability and integral linearity
identify this with the displayed unconjugated pairing. Pointwise convergence
on complex tests is equivalent to convergence on real tests, by decomposition
and the triangle inequality with error ε/2 in both real-test pairings.

W2. The directional derivative of a smooth test with compact closed support
inside Ω is again such a test; the infinite-order derivative constructor has
the exact guard ⊤+1≤⊤. The derivative of a distribution is minus its pairing
with the corresponding derivative of the test. Consequently coefficient
convergence implies convergence of the differentiated pairings. The j-th
antiholomorphic difference is minus one half of the x_j difference minus i/2
times the y_j difference. The triangle inequality proves convergence to the
antiholomorphic derivative of the limit. This uses no differentiability of a_n.

W3. By assumption that same sequence of derivative pairings converges to zero.
Uniqueness of complex limits along the nontrivial natural-number atTop filter
shows every antiholomorphic derivative of the limit distribution is zero.
Apply `analysis.dbar_closed_scalar_current_holomorphic` at each coordinate
point. It gives an open neighborhood and a holomorphic function h representing
the coefficient distribution there. This is the scalar distributional
Dolbeault–Grothendieck input, not an assumption of holomorphy of the coefficient.

W4. On that neighborhood a-h is continuous and locally integrable. Equality
of distributions gives zero integral against every compactly supported smooth
real test. Smooth-test uniqueness yields a=h almost everywhere for the same
Lebesgue measure. Convert to the restricted measure on the open neighborhood.
Both functions are continuous and Lebesgue volume is positive on nonempty
open sets, so continuous almost-everywhere equality gives equality everywhere.
Thus the representative is the original coefficient, not a substituted
almost-everywhere section or independently selected values on overlaps.

W5. Each original scalar coefficient is consequently holomorphic near every
point. The finitely many frame coefficients are holomorphic on their open
coordinate domain. The finite-dimensional holomorphic/complex-smooth criterion
and the native section-in-trivialization criterion make the original section
complex C∞ into the native total space. All overlap values already agree
because they come from that same section. Empty base spaces and rank zero are
vacuous; disconnected bases require only this local argument. No compactness,
uniform convergence, L² bounds, ambient trivialization or derivative of s_n
is assumed.
-/
theorem distributional_holomorphic_section_criterion
    {d r : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (Fin d → ℂ) X]
    {V : X → Type v} [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace (Fin r → ℂ) V)]
    [FiberBundle (Fin r → ℂ) V] [VectorBundle ℂ (Fin r → ℂ) V]
    [ContMDiffVectorBundle ∞ (Fin r → ℂ) V 𝓘(ℂ, Fin d → ℂ)]
    [T2Space X] [SecondCountableTopology X] [IsManifold 𝓘(ℂ, Fin d → ℂ) ∞ X]
    (s : ∀ x, V x) (s_n : ℕ → ∀ x, V x)
    (hs : Continuous (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (s x)))
    (_hs_n : ∀ n, Continuous (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (s_n n x)))
    (hweak : ∀ (c : OpenPartialHomeomorph X (Fin d → ℂ)),
      c ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ∞ X →
      ∀ (e : Trivialization (Fin r → ℂ)
        (TotalSpace.proj : TotalSpace (Fin r → ℂ) V → X)), IsHolomorphicFrame (d := d) e →
        ∀ (k : Fin r) (φ : TestFunction (frameDomain c e) ℂ ⊤),
          Tendsto (fun n ↦ regularPairing (frameDomain c e) (coefficient (s_n n) c e k) φ)
            atTop (𝓝 (regularPairing (frameDomain c e) (coefficient s c e k) φ)))
    (hdbar : ∀ (c : OpenPartialHomeomorph X (Fin d → ℂ)),
      c ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ∞ X →
      ∀ (e : Trivialization (Fin r → ℂ)
        (TotalSpace.proj : TotalSpace (Fin r → ℂ) V → X)), IsHolomorphicFrame (d := d) e →
        ∀ (k : Fin r) (j : Fin d) (φ : TestFunction (frameDomain c e) ℂ ⊤),
          Tendsto (fun n ↦ dbarPairing (frameDomain c e) (coefficient (s_n n) c e k) j φ)
            atTop (𝓝 0)) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) (𝓘(ℂ, Fin d → ℂ).prod 𝓘(ℂ, Fin r → ℂ)) ∞
      (fun x ↦ TotalSpace.mk' (Fin r → ℂ) x (s x)) := by
  classical
  have regular_eq (Ω : Opens (Fin d → ℂ)) (a : (Fin d → ℂ) → ℂ)
      (φ : TestFunction Ω ℂ ⊤) :
      regularPairing Ω a φ = ∫ z, φ z * a z ∂volume := by
    rw [regularPairing, setIntegral_eq_integral_of_forall_compl_eq_zero]
    · congr 1
      ext z
      exact mul_comm _ _
    · intro z hz
      simp [φ.zero_on_compl hz]
  have scalar_smooth (Ω : Opens (Fin d → ℂ)) (a : (Fin d → ℂ) → ℂ)
      (ha : ContinuousOn a Ω)
      (hclosed : ∀ (j : Fin d) (φ : TestFunction Ω ℂ ⊤), dbarPairing Ω a j φ = 0) :
      ∀ z ∈ Ω, ContDiffAt ℂ ∞ a z := by
    intro z hz
    by_cases hd : d = 0
    · subst d
      have heq : a = fun _ ↦ a z := funext fun y ↦ congrArg a (Subsingleton.elim y z)
      rw [heq]
      exact contDiffAt_const
    have hdpos : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
    have hali : LocallyIntegrableOn a Ω volume := ha.locallyIntegrableOn Ω.isOpen.measurableSet
    let T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ :=
      TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ) volume a
    have hT (φ : TestFunction Ω ℂ ⊤) : T φ = regularPairing Ω a φ := by
      rw [regular_eq]
      exact TestFunction.integralAgainstBilinCLM_eq_integral hali
    obtain ⟨W, hzW, hWΩ, h, hhol, hrep⟩ :=
      HolomorphicAnosov.dbar_closed_scalar_current_holomorphic hdpos Ω T
        (fun j φ ↦ by simpa only [hT, dbarPairing] using hclosed j φ) z hz
    have hac : ContinuousOn a W := ha.mono hWΩ
    have hhc : ContinuousOn h W := hhol.continuousOn
    have haW : LocallyIntegrableOn a W volume := hac.locallyIntegrableOn W.isOpen.measurableSet
    have hhW : LocallyIntegrableOn h W volume := hhc.locallyIntegrableOn W.isOpen.measurableSet
    have hae : ∀ᵐ y ∂volume, y ∈ W → (a y - h y) = 0 := by
      apply W.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero (haW.sub hhW)
      intro g hg hgcompact hgsupport
      let ψ : TestFunction W ℝ ⊤ := ⟨g, hg, hgcompact, hgsupport⟩
      let ψc : TestFunction W ℂ ⊤ := TestFunction.postcompCLM Complex.ofRealCLM ψ
      let φ : TestFunction Ω ℂ ⊤ := TestFunction.monoCLM ℂ ψc
      have hφ : (φ : (Fin d → ℂ) → ℂ) = fun y ↦ (g y : ℂ) := by
        simp [φ, TestFunction.monoCLM_apply, hWΩ, ψc, TestFunction.postcompCLM_apply, ψ]
        rfl
      have hφsupport : tsupport (φ : (Fin d → ℂ) → ℂ) ⊆ W := by
        rw [hφ]
        exact (tsupport_comp_subset (map_zero Complex.ofRealCLM) g).trans hgsupport
      have hzero (b : (Fin d → ℂ) → ℂ) :
          (∫ y in (W : Set (Fin d → ℂ)), b y * φ y ∂volume) = ∫ y, φ y * b y ∂volume := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        · congr 1
          ext y
          exact mul_comm _ _
        · intro y hy
          rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hy (hφsupport ht)), mul_zero]
      have heq : (∫ y, g y • a y ∂volume) = ∫ y, g y • h y ∂volume := by
        have hr := hrep φ hφsupport
        rw [hT, regular_eq, hzero] at hr
        simpa only [hφ, Complex.real_smul] using hr
      change (∫ y, g y • (a y - h y) ∂volume) = 0
      rw [show (fun y ↦ g y • (a y - h y)) =
          (fun y ↦ g y • a y - g y • h y) by funext y; exact smul_sub _ _ _,
        integral_sub (show Integrable (fun y ↦ g y • a y) volume from ψ.integrable_smul haW)
          (show Integrable (fun y ↦ g y • h y) volume from ψ.integrable_smul hhW), heq, sub_self]
    have heq : EqOn a h W := by
      apply Measure.eqOn_open_of_ae_eq (μ := volume) _ W.isOpen hac hhc
      change ∀ᵐ y ∂volume.restrict (W : Set (Fin d → ℂ)), a y = h y
      rw [ae_restrict_iff' W.isOpen.measurableSet]
      filter_upwards [hae] with y hy hyW
      exact sub_eq_zero.mp (hy hyW)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp W.isOpen z hzW
    have hseparate : ∀ (w : Fin d → ℂ) (j : Fin d),
        DifferentiableOn ℂ (fun t : ℂ ↦ h (Function.update w j t))
          ((fun t : ℂ ↦ Function.update w j t) ⁻¹' (W : Set (Fin d → ℂ))) := by
      intro w j
      exact hhol.comp ((contDiff_update (𝕜 := ℂ) ∞ w j).differentiable (by simp)).differentiableOn
        (fun _ hy ↦ hy)
    have hpolydisc : HolomorphicAnosov.PolydiscBoundaryCauchySeries.closedPolydisc z (fun _ ↦ ε / 2) ⊆ (W : Set (Fin d → ℂ)) := by
      intro w hw
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have hn : ‖w - z‖ ≤ ε / 2 := (pi_norm_le_iff_of_nonneg (by positivity)).mpr hw
      exact hn.trans_lt (by linarith)
    have hanalytic :=
      (HolomorphicAnosov.PolydiscCauchy.polydisc_cauchy_power_series hdpos W W.isOpen h hhc
        hseparate z (fun _ ↦ ε / 2) (fun _ ↦ by positivity) hpolydisc).2.2.2.2
    have hevent : a =ᶠ[𝓝 z] h := Filter.eventually_of_mem (W.isOpen.mem_nhds hzW) (fun y hy ↦ heq hy)
    exact hanalytic.contDiffAt.congr_of_eventuallyEq hevent
  intro x
  let c := chartAt (Fin d → ℂ) x
  let e := trivializationAt (Fin r → ℂ) V x
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℂ, Fin d → ℂ) ∞ X := IsManifold.chart_mem_maximalAtlas x
  have hx : x ∈ c.source := mem_chart_source (Fin d → ℂ) x
  have he : IsHolomorphicFrame (d := d) e :=
    ⟨inferInstance, e.contMDiffOn, e.contMDiffOn_symm⟩
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt (Fin r → ℂ) V x
  have hcx : c x ∈ frameDomain c e := by
    exact ⟨c.map_source hx, by change c.symm (c x) ∈ e.baseSet; rwa [c.left_inv hx]⟩
  have hcoef (k : Fin r) : ContinuousOn (coefficient s c e k) (frameDomain c e) := by
    apply (continuous_apply k).continuousOn.comp
      (continuous_snd.continuousOn.comp (e.continuousOn.comp
        (hs.continuousOn.comp (c.continuousOn_symm.mono inter_subset_left)
          (fun _ _ ↦ mem_univ _)) (fun z hz ↦ ?_)) (fun _ _ ↦ mem_univ _))
      (fun _ _ ↦ mem_univ _)
    exact e.mem_source.mpr hz.2
  have hcoeffsmooth (k : Fin r) : ContDiffAt ℂ ∞ (coefficient s c e k) (c x) := by
    apply scalar_smooth (frameDomain c e) (coefficient s c e k) (hcoef k) _ (c x) hcx
    intro j φ
    have hlim := (hweak c hc e he k ((2 : ℂ)⁻¹ •
      ((TestFunction.lineDerivCLM ℂ (Pi.single j 1) φ : TestFunction (frameDomain c e) ℂ ⊤) +
       Complex.I • (TestFunction.lineDerivCLM ℂ (Pi.single j Complex.I) φ :
         TestFunction (frameDomain c e) ℂ ⊤)))).neg
    exact tendsto_nhds_unique hlim (hdbar c hc e he k j φ)
  apply (e.contMDiffAt_section_iff hxe).mpr
  rw [contMDiffAt_iff_source_of_mem_source hx]
  simpa only [mfld_simps, c, coefficient, Function.comp_def, contMDiffWithinAt_univ] using
    (contDiffAt_pi.mpr hcoeffsmooth).contMDiffAt

end
end HolomorphicAnosov.DistributionalSection

