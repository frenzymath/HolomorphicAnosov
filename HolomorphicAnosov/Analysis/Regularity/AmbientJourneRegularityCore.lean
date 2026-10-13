import HolomorphicAnosov.Analysis.Regularity.CampanatoPolynomialRegularity
import HolomorphicAnosov.Analysis.Regularity.JourneLeafPolynomialApproximation
import HolomorphicAnosov.Analysis.Regularity.GraphFoliationData
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov
open Set JourneLeafPolynomialApproximation
open scoped Manifold ContDiff

/-- The exact positive-dimensional finite-order consequence of the two published children.
Source: parent clauses J2–J3, Journé pp.187–192 and Campanato §6 p.156.
This uses the original function and preserves the exponent and both original graph atlases.
It inherits the children’s proof admissions; it is not a kernel-complete Journé theorem. -/
theorem finite_order_from_graphs
    {p q n : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (hn : 1 ≤ n)
    {Ω : Set (Block (p + q))} (hΩ : IsOpen Ω)
    (F₁ : GraphFoliation p q (p + q) n (1 / 2) Ω)
    (F₂ : GraphFoliation q p (p + q) n (1 / 2) Ω)
    (ht : AreTransverse F₁ F₂) (f : Block (p + q) → ℝ)
    (hf : ContinuousOn f Ω)
    (hf₁ : HasLeafwiseHolderBounds F₁ f) (hf₂ : HasLeafwiseHolderBounds F₂ f) :
    ContDiffOn ℝ n f Ω := by
  exact (campanato_uniform_polynomial_approximation_regularity (by omega) hn hΩ
    (by norm_num) (by norm_num) f hf
    (journe_transverse_leaf_polynomial_approximation hp hq hn hΩ
      (by norm_num) (by norm_num) F₁ F₂ ht f hf hf₁ hf₂)).1

/-- Parent J4: finite chart regularity at every order gives smoothness of the same function.
Source: Journé p.187, local finite-order reduction; native maximal-atlas composition and
`contMDiff_infty`. The chart and neighborhood may depend on both order and point. -/
theorem smooth_from_finite_chart_regularities
    {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Block N) M]
    [IsManifold (𝓘(ℝ, Block N)) ∞ M] (h : M → ℝ)
    (hfinite : ∀ (n : ℕ) (a : M),
      ∃ e : OpenPartialHomeomorph M (Block N),
        e ∈ IsManifold.maximalAtlas (𝓘(ℝ, Block N)) ∞ M ∧ a ∈ e.source ∧
        ∃ Ω : Set (Block N), IsOpen Ω ∧ e a ∈ Ω ∧
          ContDiffOn ℝ n (h ∘ e.symm) Ω) :
    ContMDiff (𝓘(ℝ, Block N)) (𝓘(ℝ, ℝ)) ∞ h := by
  apply contMDiff_infty.mpr
  intro n a
  obtain ⟨e, he, ha, Ω, hΩ, hΩa, hreg⟩ := hfinite n a
  have hchart : ContMDiffAt (𝓘(ℝ, Block N)) (𝓘(ℝ, Block N)) n e a :=
    (contMDiffAt_of_mem_maximalAtlas he ha).of_le (by exact_mod_cast le_top)
  have hlocal : ContMDiffAt (𝓘(ℝ, Block N)) (𝓘(ℝ, ℝ)) n (h ∘ e.symm) (e a) :=
    (hreg.contDiffAt (hΩ.mem_nhds hΩa)).contMDiffAt
  apply (hlocal.comp a hchart).congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds ha] with y hy
  simp only [Function.comp_apply, e.left_inv hy]

/-- Parent J5 with a zero-dimensional transverse block. The SAME full-dimensional
plaque gives ambient smoothness: its inverse coordinate is the first component of the
original frame inverse, an actual affine map. Source: parent J5, native graph-box formula.
No inverse-function theorem, positive leaf rank, or transverse differentiability is used. -/
theorem smooth_on_full_dimensional_box
    {d N : ℕ} {Ω : Set (Block N)} (b : GraphBox d 0 N 1 0 Ω)
    (f : Block N → ℝ)
    (hf : ContDiffOn ℝ ∞ (f ∘ b.plaque 0) (Metric.ball 0 b.leafRadius)) :
    ContDiffOn ℝ ∞ f b.image := by
  let k : Block N → Block d := fun y ↦ (b.frame.symm (y - b.base)).1
  have hk : ContDiff ℝ ∞ k :=
    contDiff_fst.comp (b.frame.symm.contDiff.comp (contDiff_id.sub contDiff_const))
  have hcoordinates : ∀ y ∈ b.image,
      k y ∈ Metric.ball 0 b.leafRadius ∧ b.plaque 0 (k y) = y := by
    intro y hy
    let z := b.chart.symm ⟨y, hy⟩
    have hz : (b.chart z).val = y := congrArg Subtype.val (b.chart.apply_symm_apply ⟨y, hy⟩)
    have hform : y = b.base + b.frame (z.val.1, 0) := by
      rw [← hz, b.chart_formula]
      congr 2
      exact Prod.ext rfl (Subsingleton.elim _ _)
    have hky : k y = z.val.1 := by
      simp [k, hform]
    constructor
    · rw [hky]
      exact z.property.1
    · rw [GraphBox.plaque, hky, hform]
      congr 2
      exact Prod.ext rfl (Subsingleton.elim _ _)
  apply b.image_open.contDiffOn_iff.mpr
  intro a ha
  have hlocal : ContDiffAt ℝ ∞ ((f ∘ b.plaque 0) ∘ k) a :=
    (hf.contDiffAt (Metric.isOpen_ball.mem_nhds (hcoordinates a ha).1)).comp a hk.contDiffAt
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [b.image_open.mem_nhds ha] with y hy
  simp only [Function.comp_apply, (hcoordinates y hy).2]

/-- Parent J1's quantitative step: a bound on the next spatial derivative gives the
exact half-Hölder bound for the original order-n derivative on the same convex ball.
Source: parent J1, native convex mean-value estimate and iterated-derivative norm recursion.
This theorem differentiates only spatial variables and needs no transverse jet continuity. -/
theorem half_holder_of_next_derivative_bound
    {D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : D → F) (n : ℕ) {r L : ℝ} (_hr : 0 < r) (hL : 0 ≤ L)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball 0 r))
    (hbound : ∀ x ∈ Metric.ball 0 r, ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ L) :
    ∀ x ∈ Metric.ball 0 r, ∀ y ∈ Metric.ball 0 r,
      ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ ≤
        (L * (2 * r) ^ (1 / 2 : ℝ)) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
  intro x hx y hy
  have hd : ∀ z ∈ Metric.ball (0 : D) r,
      DifferentiableAt ℝ (iteratedFDeriv ℝ n f) z := by
    intro z hz
    exact (hf.contDiffAt (Metric.isOpen_ball.mem_nhds hz)).differentiableAt_iteratedFDeriv
      (by exact_mod_cast ENat.natCast_lt_top n)
  have hb : ∀ z ∈ Metric.ball (0 : D) r,
      ‖fderiv ℝ (iteratedFDeriv ℝ n f) z‖ ≤ L := by
    intro z hz
    rw [norm_fderiv_iteratedFDeriv]
    exact hbound z hz
  have hLip := (convex_ball (0 : D) r).norm_image_sub_le_of_norm_fderiv_le hd hb hy hx
  have hdist : ‖x - y‖ ≤ 2 * r := by
    have hx' : ‖x‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have hy' : ‖y‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hy
    exact (norm_sub_le x y).trans (by linarith)
  have hfactor : ‖x - y‖ = ‖x - y‖ ^ (1 / 2 : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add' (norm_nonneg _) (by norm_num : (1 / 2 : ℝ) + 1 / 2 ≠ 0)]
    norm_num
  calc
    ‖iteratedFDeriv ℝ n f x - iteratedFDeriv ℝ n f y‖ ≤ L * ‖x - y‖ := hLip
    _ = L * (‖x - y‖ ^ (1 / 2 : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ)) := by rw [← hfactor]
    _ ≤ L * ((2 * r) ^ (1 / 2 : ℝ) * ‖x - y‖ ^ (1 / 2 : ℝ)) := by
      gcongr
    _ = (L * (2 * r) ^ (1 / 2 : ℝ)) * ‖x - y‖ ^ (1 / 2 : ℝ) := by ring

/-- Parent J1 for an arbitrary transverse parameter set: original all-order uniform
spatial bounds yield one finite C^{n,1/2} bound on the same smaller ball.
Source: parent J1's convex derivative estimate, with finite maxima replaced by a finite sum.
The parameter set has no topology here; no transverse derivative or jet continuity is used. -/
theorem uniform_half_holder_from_smooth_bounds
    {T D F : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (v : T → D → F) (S : Set T) (n : ℕ) {r : ℝ} (hr : 0 < r)
    (hv : ∀ t ∈ S, ContDiffOn ℝ ∞ (v t) (Metric.ball 0 r))
    (hb : ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ∈ S, ∀ x ∈ Metric.ball 0 r, ‖iteratedFDeriv ℝ j (v t) x‖ ≤ K) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ S,
      HasFiniteHolderBounds n (1 / 2) K (v t) (Metric.ball 0 r) := by
  choose K hKnonneg hKbound using hb
  let L : ℝ := ∑ j ∈ Finset.range (n + 2), K j
  have hL : 0 ≤ L := Finset.sum_nonneg (fun j _ ↦ hKnonneg j)
  have hKL : ∀ j ≤ n + 1, K j ≤ L := by
    intro j hj
    exact Finset.single_le_sum (fun i _ ↦ hKnonneg i) (Finset.mem_range.mpr (by omega))
  let A : ℝ := max L (L * (2 * r) ^ (1 / 2 : ℝ))
  refine ⟨A, hL.trans (le_max_left _ _), ?_⟩
  intro t ht
  refine ⟨(hv t ht).of_le (by exact_mod_cast le_top), ?_, ?_⟩
  · intro j hj x hx
    exact (hKbound j t ht x hx).trans ((hKL j (by omega)).trans (le_max_left _ _))
  · intro x hx y hy
    have hnext : ∀ z ∈ Metric.ball (0 : D) r,
        ‖iteratedFDeriv ℝ (n + 1) (v t) z‖ ≤ L := by
      intro z hz
      exact (hKbound (n + 1) t ht z hz).trans (hKL _ le_rfl)
    exact (half_holder_of_next_derivative_bound (v t) n hr hL (hv t ht) hnext x hx y hy).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) _))

/-- Parent J2–J4 with fully local finite-order data. Both the chart and the open domain
may depend on the derivative order and point, as the original proof requires.
Source: Journé p.187, Campanato §6 p.156 and native maximal-atlas calculus.
The case n=0 uses only the original continuity. The positive orders consume the two exact
published children; those inherited admissions are not hidden or replaced by new assumptions
in the public ambient theorem. -/
theorem smooth_from_local_finite_graph_data
    {p q : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Block (p + q)) M]
    [IsManifold (𝓘(ℝ, Block (p + q))) ∞ M]
    (hp : 1 ≤ p) (hq : 1 ≤ q) (h : M → ℝ) (hh : Continuous h)
    (hfinite : ∀ (n : ℕ), 1 ≤ n → ∀ a : M,
      ∃ e : OpenPartialHomeomorph M (Block (p + q)),
        e ∈ IsManifold.maximalAtlas (𝓘(ℝ, Block (p + q))) ∞ M ∧ a ∈ e.source ∧
        ∃ Ω : Set (Block (p + q)), IsOpen Ω ∧ Ω ⊆ e.target ∧ e a ∈ Ω ∧
          ∃ F₁ : GraphFoliation p q (p + q) n (1 / 2) Ω,
            ∃ F₂ : GraphFoliation q p (p + q) n (1 / 2) Ω,
              AreTransverse F₁ F₂ ∧ HasLeafwiseHolderBounds F₁ (h ∘ e.symm) ∧
                HasLeafwiseHolderBounds F₂ (h ∘ e.symm)) :
    ContMDiff (𝓘(ℝ, Block (p + q))) (𝓘(ℝ, ℝ)) ∞ h := by
  apply smooth_from_finite_chart_regularities h
  intro n a
  by_cases hn : 1 ≤ n
  · obtain ⟨e, he, ha, Ω, hΩ, htarget, hea, F₁, F₂, ht, hf₁, hf₂⟩ := hfinite n hn a
    have hc : ContinuousOn (h ∘ e.symm) Ω :=
      hh.continuousOn.comp (e.continuousOn_symm.mono htarget) (fun _ _ ↦ Set.mem_univ _)
    exact ⟨e, he, ha, Ω, hΩ, hea, finite_order_from_graphs hp hq hn hΩ F₁ F₂ ht
      (h ∘ e.symm) hc hf₁ hf₂⟩
  · have hn0 : n = 0 := by omega
    subst n
    let e := chartAt (Block (p + q)) a
    refine ⟨e, IsManifold.chart_mem_maximalAtlas a, mem_chart_source _ a,
      e.target, e.open_target, e.map_source (mem_chart_source _ a), ?_⟩
    exact contDiffOn_zero.mpr (hh.continuousOn.comp e.continuousOn_symm
      (fun _ _ ↦ Set.mem_univ _))


end HolomorphicAnosov
