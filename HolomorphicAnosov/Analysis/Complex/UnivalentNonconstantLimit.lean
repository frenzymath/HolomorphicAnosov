import HolomorphicAnosov.Analysis.Complex.HurwitzZeroFreeLimit
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Nonconstant locally uniform limits of univalent functions

Source: Curtis T. McMullen, *Complex Analysis*, Harvard Math 213a notes,
22 January 2017, Lemma 4.2, printed p.58. The argument uses the existing
Conway Hurwitz theorem to express the source's local Rouché step.
-/

open Set Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- A nonconstant compact-uniform limit of injective holomorphic functions on a
connected open complex domain is injective.

Source: McMullen, *Complex Analysis*, Lemma 4.2, p.58.
Proof: The locally uniform holomorphic-limit theorem makes the limit holomorphic.
If two distinct points x and y have the same limiting value, choose an open ball
about y inside the domain and avoiding x. On this ball the holomorphic differences
Fₙ(z) − Fₙ(x) are nowhere zero by injectivity. They converge uniformly on compacta
to f(z) − f(x), which vanishes at y. Hurwitz therefore makes this difference
identically zero on the ball. The analytic identity principle makes f constant on
the entire connected domain, contrary to the nonconstancy hypothesis. The empty
domain is excluded by nonconstancy, and no global bound or simple connectedness
is assumed. -/
theorem univalent_nonconstant_limit {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hhol : ∀ n, DifferentiableOn ℂ (F n) U)
    (hinj : ∀ n, Set.InjOn (F n) U)
    (hlim : ∀ K : Set ℂ, K ⊆ U → IsCompact K →
      TendstoUniformlyOn F f atTop K)
    (hnonconstant : ¬ ∃ c : ℂ, Set.EqOn f (fun _ ↦ c) U) :
    Set.InjOn f U := by
  have hloc := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr hlim
  have hfhol := hloc.differentiableOn (Eventually.of_forall hhol) hU
  intro x hx y hy hxy
  by_contra hne
  have hys : y ∈ U \ {x} := ⟨hy, by simpa using Ne.symm hne⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU.sdiff isClosed_singleton) y hys
  have hbU : Metric.ball y r ⊆ U := fun z hz ↦ (hball hz).1
  have hzero := conway_hurwitz_zero_free_limit Metric.isOpen_ball
    (convex_ball y r).isPreconnected
    (F := fun n z ↦ F n z - F n x) (f := fun z ↦ f z - f x)
    (fun n ↦ ((hhol n).mono hbU).sub (differentiableOn_const (F n x)))
    (fun n z hz hzero ↦ (hball hz).2 (by
      have heq : z = x := hinj n (hbU hz) hx (sub_eq_zero.mp hzero)
      simpa only [Set.mem_singleton_iff] using heq))
    (fun K hK hKc ↦ (hlim K (hK.trans hbU) hKc).sub
      ((hloc.tendsto_at hx).tendstoUniformlyOn_const K))
  rcases hzero.2 with hzero | hzero
  · have hevent : f =ᶠ[𝓝 y] fun _ ↦ f x := by
      filter_upwards [Metric.ball_mem_nhds y hr] with z hz
      exact sub_eq_zero.mp (hzero z hz)
    exact hnonconstant ⟨f x, (hfhol.analyticOnNhd hU).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const hUc hy hevent⟩
  · exact hzero y (Metric.mem_ball_self hr) (sub_eq_zero.mpr hxy.symm)

end HolomorphicAnosov
