import HolomorphicAnosov.Analysis.Distribution.ReflectedMollifierConvergence
import Mathlib.Topology.MetricSpace.Thickening
import HolomorphicAnosov.Analysis.DistributionSmoothFixedSupportFamily

open Function Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators ContDiff Distributions ENNReal Topology _root_.Topology
attribute [local instance] Classical.propDecidable

namespace HolomorphicAnosov.Analysis.Distribution

/-- Fixed-test weak convergence of local distributional mollification.

Source: Demailly, *Complex Analytic and Differential Geometry*, I §2.D.3
(2.23), p.19 and I §2.A (2.3), p.14; parameter integral interchange follows
Dyatlov, Lemma 6.8 and Remark 6.9, pp.71–73. The seminorm estimates below expand
the convergence assertion in the source for a kernel that need not be even.

Proof: Fix φ and its compact topological support L⊂U. Choose a bounded open
neighborhood P of L whose closure is compact in U, and then a positive δ such
that the closed δ-neighborhood K of that closure is compact and contained in U.
For 0<ε<δ/2, P is inside the strict ε-interior, and Hε(p,y)=ε⁻ᵐρ((p-y)/ε)
has spatial support in K for p∈P. Regard φ as a test on P. The fixed-support
family theorem constructs ηε(y)=∫ₚ∈P φ(p)Hε(p,y) and gives
T ηε=∫ₚ∈P φ(p)Fε(p). Since φ vanishes outside L, the latter integral equals
the integral on the strict ε-interior. The integrals are genuine Lebesgue
integrals by the same theorem, rather than values of nonintegrable totalizations.

Translation in the parameter integral and the vanishing of φ outside P give
ηε(y)=∫ᵤ ρε(u)φ(y+u). This is convolution with the reflected kernel; no
evenness is assumed. The dilation change of variables u=εz gives ∫ρε=1,
and ρε is nonnegative and supported in the closed ε-ball. Differentiating
under this compact integral in every finite order gives
Dʲηε(y)=∫ᵤ ρε(u)Dʲφ(y+u), as an equality of multilinear maps. Consequently
the norm of Dʲηε(y)-Dʲφ(y) is bounded by the supremum of
‖Dʲφ(y+u)-Dʲφ(y)‖ over ‖u‖≤ε. Each derivative of the smooth compactly
supported φ is uniformly continuous (apply compact uniform continuity on a
fixed compact neighborhood of its support and use its vanishing outside).
Thus this bound tends to zero uniformly in y for every finite j.

All ηε and φ are supported in K. The uniform derivative estimates give
convergence in each defining seminorm of the fixed-support smooth test space.
The canonical supported inclusion into TestFunction U ℂ ∞ is continuous,
so ηε tends to φ in the LF topology. Continuity of T gives T ηε→T φ.
The equalities valid for 0<ε<δ/2 hold eventually in the right neighborhood
filter of zero, proving the stated limit. If φ=0, all pairings are zero;
this includes empty U. The whole-space case uses infinite distance to the
empty complement and otherwise the same compact neighborhood argument. -/
theorem distribution_mollifier_weak_convergence
    {m : ℕ} (hm : 1 ≤ m)
    (U : Opens (EuclideanSpace ℝ (Fin m)))
    (T : TestFunction U ℂ ⊤ →L[ℂ] ℂ)
    (ρ : TestFunction (⊤ : Opens (EuclideanSpace ℝ (Fin m))) ℝ ⊤)
    (hρ_nonneg : ∀ x, 0 ≤ ρ x)
    (hρ_support : tsupport (ρ : EuclideanSpace ℝ (Fin m) → ℝ) ⊆
      Metric.closedBall 0 1)
    (hρ_norm : ∫ x, ρ x ∂volume = 1)
    (κ : ∀ ε : ℝ, 0 < ε → ∀ x,
      x ∈ {x | x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x ((U : Set _)ᶜ)} →
        TestFunction U ℂ ⊤)
    (F : ∀ ε : ℝ, 0 < ε → EuclideanSpace ℝ (Fin m) → ℂ)
    (hκ : ∀ ε (hε : 0 < ε) x hx y,
      κ ε hε x hx y = (((ε⁻¹) ^ m : ℝ) : ℂ) *
        ((ρ (ε⁻¹ • (x - y)) : ℝ) : ℂ))
    (hF : ∀ ε (hε : 0 < ε) x
      (hx : x ∈ {x | x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x ((U : Set _)ᶜ)}),
      F ε hε x = T (κ ε hε x hx))
    : ∀ φ : TestFunction U ℂ ⊤,
      Tendsto
        (fun ε : ℝ ↦ if hε : 0 < ε then
          ∫ x in {x | x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x ((U : Set _)ᶜ)},
            F ε hε x * φ x else 0)
        (𝓝[>] (0 : ℝ)) (𝓝 (T φ)) := by
  classical
  intro φ
  let L := tsupport (φ : EuclideanSpace ℝ (Fin m) → ℂ)
  obtain ⟨δ, hδ, hδU⟩ := φ.hasCompactSupport.exists_cthickening_subset_open
    U.isOpen φ.tsupport_subset
  let K := Metric.cthickening δ L
  let P : Opens (EuclideanSpace ℝ (Fin m)) :=
    ⟨Metric.thickening (δ / 2) L, Metric.isOpen_thickening⟩
  have hLP : L ⊆ P := Metric.self_subset_thickening (by linarith) L
  let ψ : TestFunction P ℂ ⊤ := ⟨φ, φ.contDiff, φ.hasCompactSupport, hLP⟩
  obtain ⟨r, hr, hrsep⟩ := Metric.exists_pos_forall_lt_edist
    φ.hasCompactSupport U.isOpen.isClosed_compl φ.tsupport_subset.disjoint_compl_right
  have hrR : (0 : ℝ) < r := hr
  let a := min (δ / 2) (r : ℝ)
  have ha : 0 < a := lt_min (by linarith) hrR
  have construct : ∀ (ε : ℝ) (hε : 0 < ε), ε < a → ∃ η : TestFunction U ℂ ⊤,
      (∀ y, η y = ∫ p, φ p * ((((ε⁻¹) ^ m : ℝ) : ℂ) *
        ((ρ (ε⁻¹ • (p - y)) : ℝ) : ℂ))) ∧
      T η = ∫ x in {x | x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x ((U : Set _)ᶜ)},
        F ε hε x * φ x := by
    intro ε hε hεa
    have hεδ : ε < δ / 2 := hεa.trans_le (min_le_left _ _)
    have hεr : ε < (r : ℝ) := hεa.trans_le (min_le_right _ _)
    let S : Set (EuclideanSpace ℝ (Fin m)) :=
      {x | x ∈ U ∧ ENNReal.ofReal ε < Metric.infEDist x ((U : Set _)ᶜ)}
    have hLS : L ⊆ S := by
      intro x hx
      refine ⟨φ.tsupport_subset hx, ?_⟩
      have hlow : (r : ℝ≥0∞) ≤ Metric.infEDist x ((U : Set _)ᶜ) :=
        Metric.le_infEDist.mpr fun y hy ↦ (hrsep x hx y hy).le
      apply lt_of_lt_of_le _ hlow
      exact (ENNReal.ofReal_lt_coe_iff hε.le).mpr hεr
    let H : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) → ℂ :=
      fun p y ↦ (((ε⁻¹) ^ m : ℝ) : ℂ) * ((ρ (ε⁻¹ • (p - y)) : ℝ) : ℂ)
    have hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)) := by
      apply ContDiff.contDiffOn
      exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (ρ.contDiff.comp ((contDiff_fst.sub contDiff_snd).const_smul ε⁻¹)))
    have hSupport : ∀ p ∈ P, tsupport (H p) ⊆ K := by
      intro p hp
      obtain ⟨z, hz, hpz⟩ := Metric.mem_thickening_iff.mp hp
      apply closure_minimal _ Metric.isClosed_cthickening
      intro y hy
      have hρy : ρ (ε⁻¹ • (p - y)) ≠ 0 := by
        intro hzero
        exact hy (by simp [H, hzero])
      have hn := hρ_support (subset_tsupport _ hρy)
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hε)] at hn
      have hpy : dist y p ≤ ε := by
        have h := mul_le_mul_of_nonneg_left hn hε.le
        simpa [← mul_assoc, hε.ne', dist_eq_norm, norm_sub_rev] using h
      exact Metric.mem_cthickening_of_dist_le y z δ L hz
        ((dist_triangle y p z).trans (by linarith))
    obtain ⟨sections, hsections, _, _, hint⟩ :=
      HolomorphicAnosov.Analysis.distribution_smooth_fixed_support_family
        (by omega : 0 < m) (by omega : 0 < m) U P T K
        φ.hasCompactSupport.cthickening hδU H hH hSupport
    obtain ⟨η, _, hη, _, _, hTη⟩ := hint ψ
    refine ⟨η, ?_, ?_⟩
    · intro y
      rw [hη y]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      have hz : φ p = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hLP h))
      simp [ψ, hz]
    · rw [hTη]
      have hPint : (∫ p in (P : Set _), ψ p * T (sections p)) =
          ∫ p, φ p * T (sections p) := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro p hp
        have hz : φ p = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hLP h))
        simp [ψ, hz]
      rw [hPint]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (f := fun p ↦ F ε hε p * φ p)
        (fun p hp ↦ by
          have hz : φ p = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hp (hLS h))
          simp [hz])]
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hp : p ∈ L
      · have hEq : sections p = κ ε hε p (hLS hp) := by
          ext y
          rw [hsections p (hLP hp) y, hκ]
        rw [hEq, ← hF ε hε p (hLS hp), mul_comm]
      · simp [image_eq_zero_of_notMem_tsupport hp]
  let η : ℝ → TestFunction U ℂ ⊤ := fun ε ↦
    if h : 0 < ε ∧ ε < a then (construct ε h.1 h.2).choose else 0
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < a := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds ha).filter_mono nhdsWithin_le_nhds] with ε hε hεa
    exact ⟨hε, hεa⟩
  have hη : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y,
      η ε y = ∫ p, φ p * ((((ε⁻¹) ^ m : ℝ) : ℂ) *
        ((ρ (ε⁻¹ • (p - y)) : ℝ) : ℂ)) := by
    filter_upwards [hevent] with ε hε
    simpa only [η, dite_eq_left hε] using (construct ε hε.1 hε.2).choose_spec.1
  have ht := T.continuous.tendsto φ |>.comp
    (testFunction_reflected_mollifier_tendsto U ρ hρ_nonneg hρ_support hρ_norm φ η hη)
  apply ht.congr'
  filter_upwards [hevent] with ε hε
  simp only [Function.comp_apply, η, dite_eq_left hε, dite_eq_left hε.1]
  exact (construct ε hε.1 hε.2).choose_spec.2

end HolomorphicAnosov.Analysis.Distribution
