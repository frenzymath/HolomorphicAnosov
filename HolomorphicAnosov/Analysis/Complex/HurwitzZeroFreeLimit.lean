import HolomorphicAnosov.Analysis.Complex.ConwayZeroPersists
import HolomorphicAnosov.Analysis.Complex.LoopHomotopyOfNormSubLt
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Connected.Basic

/-!
# Hurwitz's zero-free limit dichotomy

Source: John B. Conway, *Functions of One Complex Variable I*, second edition
(1978), Chapter VII §2, Theorem 2.5 and Corollary 2.6, printed p.152 (PDF p.163).
The zero-count homotopy argument is also written in Curtis T. McMullen,
*Complex Analysis*, Harvard Math 213a author notes dated 22 January 2017,
Corollary 1.23, printed p.12.

DAG node: `analysis.conway_hurwitz_zero_free_limit_g2`.
Stage 2 records only the statement; the proof remains `sorry`.
-/

namespace HolomorphicAnosov

/--
A compact-uniform limit of zero-free holomorphic functions on a connected open
complex set is holomorphic and is either identically zero or everywhere nonzero.

`IsPreconnected G` expresses connectedness without adding nonemptiness: the
empty domain satisfies the identically-zero branch. The ambient functions are
unrestricted outside `G`; `DifferentiableOn ℂ` is holomorphicity on the open set.
Uniform convergence is required on every compact subset of the original domain.

Source and natural-language proof: Conway VII §2, Theorem 2.5 and Corollary 2.6,
p.152, with McMullen Corollary 1.23, p.12, for the zero-count homotopy.

1. Compact-uniform convergence on the open complex domain is locally uniform.
   The holomorphic locally uniform limit theorem makes `f` holomorphic. If it
   is identically zero, the first alternative holds. Otherwise the identity
   theorem and connectedness imply that its germ is nonzero at every point.
2. If `f a = 0` at a point of `G`, finite-zero factorization gives
   `f z = (z - a)^m * u z` near `a`, where `m ≥ 1` and `u a ≠ 0`.
   Choose a positive-radius closed disk contained in this neighborhood and in
   `G`, with `u` nonzero throughout it. Thus `a` is its only zero, of order `m`.
   On the compact boundary circle, `‖f‖` has a positive minimum `η`.
   Uniform convergence on the closed disk makes `‖F n - f‖ < η / 2` on the
   boundary for every sufficiently large `n`.
3. The straight-line family `f + t * (F n - f)`, for `0 ≤ t ≤ 1`, is jointly
   continuous and nonzero on the boundary, since its norm is greater than
   `η / 2`. Homotopy invariance equates the boundary windings of `f` and `F n`.
   The holomorphic zero-count theorem identifies these with the sums of zero
   orders in the disk. They are respectively `m ≥ 1` and zero, a contradiction.
4. Hence the non-identically-zero limit is everywhere nonzero on `G`. For the
   empty domain, all pointwise assertions and the identically-zero branch are
   vacuous. No boundedness or simple-connectedness assumption is used.
-/
theorem conway_hurwitz_zero_free_limit {G : Set ℂ}
    (hG_open : IsOpen G) (hG_connected : IsPreconnected G)
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF_holomorphic : ∀ n, DifferentiableOn ℂ (F n) G)
    (hF_nonzero : ∀ n, ∀ z ∈ G, F n z ≠ 0)
    (hF_limit : ∀ K : Set ℂ, K ⊆ G → IsCompact K →
      TendstoUniformlyOn F f Filter.atTop K) :
    DifferentiableOn ℂ f G ∧
      ((∀ z ∈ G, f z = 0) ∨ (∀ z ∈ G, f z ≠ 0)) := by
  classical
  have hloc : TendstoLocallyUniformlyOn F f Filter.atTop G :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hG_open).mpr hF_limit
  have hf : DifferentiableOn ℂ f G :=
    hloc.differentiableOn (Filter.Eventually.of_forall hF_holomorphic) hG_open
  have hfa : AnalyticOnNhd ℂ f G := hf.analyticOnNhd hG_open
  by_cases hzero : ∀ z ∈ G, f z = 0
  · exact ⟨hf, Or.inl hzero⟩
  · refine ⟨hf, Or.inr ?_⟩
    intro z hz hfz
    have hlocal := (hfa z hz).eventually_eq_zero_or_eventually_ne_zero
    rcases hlocal with hlocal | hlocal
    · have hglobal := hfa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hG_connected hz hlocal
      exact hzero hglobal
    · obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hlocal
      obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hG_open z hz
      obtain ⟨r, hr, hrmin⟩ := exists_between
        (lt_min hε (lt_min hδ (by positivity : 0 < (1 : ℝ))))
      have hrε : r < ε := lt_of_lt_of_le hrmin (min_le_left _ _)
      have hrδ : r < δ := lt_of_lt_of_le hrmin
        ((min_le_right _ _).trans (min_le_left _ _))
      have hKsub : Metric.closedBall z r ⊆ G := by
        intro w hw
        exact hδsub ((Metric.mem_closedBall.mp hw).trans_lt hrδ)
      have hsfne : ∀ w ∈ Metric.sphere z r, f w ≠ 0 := by
        intro w hw
        apply hεsub
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball, Metric.mem_sphere.mp hw]
          exact hrε
        · intro heq
          subst w
          have := Metric.mem_sphere.mp hw
          have hzero : (0 : ℝ) = r := by simpa using this
          exact (ne_of_gt hr) hzero.symm
      obtain ⟨w, hw, hmin⟩ := (isCompact_sphere z r).exists_isMinOn
        (NormedSpace.sphere_nonempty.mpr hr.le)
        ((hfa.continuousOn.mono (Metric.sphere_subset_closedBall.trans hKsub)).norm)
      have hwm : 0 < ‖f w‖ := norm_pos_iff.mpr (hsfne w hw)
      obtain ⟨n, hn⟩ := ((Metric.tendstoUniformlyOn_iff.mp
        (hF_limit (Metric.closedBall z r) hKsub (isCompact_closedBall z r))) (‖f w‖ / 2)
        (by positivity)).exists
      have hq : AnalyticOnNhd ℂ f (Metric.closedBall z r) := hfa.mono hKsub
      have hFn : AnalyticOnNhd ℂ (F n) (Metric.closedBall z r) :=
        ((hF_holomorphic n).analyticOnNhd hG_open).mono hKsub
      have hclose : ∀ y ∈ Metric.sphere z r, ‖F n y - f y‖ < ‖f y‖ := by
        intro y hy
        have hyerr : ‖F n y - f y‖ < ‖f w‖ / 2 := by
          simpa only [dist_eq_norm, norm_sub_rev] using hn y (Metric.sphere_subset_closedBall hy)
        have hymin : ‖f w‖ ≤ ‖f y‖ := hmin hy
        linarith
      obtain ⟨c, hc, hcn⟩ := conway_zero_persists_of_boundary_close z r hr f (F n)
        hq hFn hfz hclose
      exact (hF_nonzero n c (hKsub (Metric.ball_subset_closedBall hc))) hcn


end HolomorphicAnosov
