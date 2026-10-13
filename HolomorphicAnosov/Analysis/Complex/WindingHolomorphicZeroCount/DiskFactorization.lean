import HolomorphicAnosov.Analysis.Complex.WindingNumber
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Analytic.Order
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.Definitions
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.DiskOrdersFinite

open Set Bundle TopologicalSpace
open scoped Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section


lemma disk_factorization (a b : ℂ) (r : ℝ) (f : ℂ → ℂ) (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall a r))
    (hboundary : ∀ z ∈ Metric.sphere a r, f z ≠ b) :
    ∃ s : Finset ℂ,
      (∀ x, x ∈ s ↔ x ∈ Metric.ball a r ∧ f x = b) ∧
      (∀ x ∈ s, analyticOrderAt (fun z ↦ f z - b) x ≠ ⊤ ∧
        0 < analyticOrderNatAt (fun z ↦ f z - b) x) ∧
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.closedBall a r) ∧
        (∀ x ∈ Metric.closedBall a r, g x ≠ 0) ∧
        ∀ z ∈ Metric.closedBall a r,
          f z - b = (∏ x ∈ s, (z - x) ^ analyticOrderNatAt (fun z ↦ f z - b) x) * g z := by
  classical
  let K := Metric.closedBall a r
  let h := fun z ↦ f z - b
  have hh : AnalyticOnNhd ℂ h K := hf.sub analyticOnNhd_const
  have hfinite := disk_orders_finite a b r f hr hf hboundary
  let D := MeromorphicOn.divisor h K
  have hD (x : ℂ) (hx : x ∈ K) :
      D x = (analyticOrderNatAt h x : ℤ) := by
    dsimp [D]
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hh hx,
      ← Nat.cast_analyticOrderNatAt (hfinite x hx)]
    simp [h]
  have hsfinite := D.finiteSupport (isCompact_closedBall a r)
  let s := hsfinite.toFinset
  have hs (x : ℂ) : x ∈ s ↔ x ∈ Metric.ball a r ∧ f x = b := by
    change x ∈ hsfinite.toFinset ↔ _
    rw [Set.Finite.mem_toFinset]
    constructor
    · intro hx
      have hxK := D.supportWithinDomain hx
      have hn : analyticOrderNatAt h x ≠ 0 := by
        intro hn
        apply hx
        change D x = 0
        rw [hD x hxK, hn]
        rfl
      have hz : f x = b := sub_eq_zero.mp (apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := h) hn)
      refine ⟨?_, hz⟩
      have hdist := Metric.mem_closedBall.mp hxK
      apply Metric.mem_ball.mpr
      exact lt_of_le_of_ne hdist (fun heq ↦ hboundary x (Metric.mem_sphere.mpr heq) hz)
    · rintro ⟨hx, hz⟩
      have hxK := Metric.ball_subset_closedBall hx
      rw [Function.mem_support, hD x hxK, ne_eq, Nat.cast_eq_zero]
      intro hn
      have ho : analyticOrderAt h x = 0 := by
        rw [← Nat.cast_analyticOrderNatAt (hfinite x hxK), hn]
        rfl
      exact (hh x hxK).analyticOrderAt_eq_zero.mp ho (sub_eq_zero.mpr hz)
  have hord (x : ℂ) (hx : x ∈ s) : analyticOrderAt h x ≠ ⊤ ∧
      0 < analyticOrderNatAt h x := by
    have hxK := Metric.ball_subset_closedBall ((hs x).mp hx).1
    refine ⟨hfinite x hxK, Nat.pos_of_ne_zero ?_⟩
    have hx' : x ∈ D.support := (Set.Finite.mem_toFinset hsfinite).mp hx
    intro hn
    apply hx'
    change D x = 0
    rw [hD x hxK, hn]
    rfl
  obtain ⟨g, hg, hgne, heq⟩ := hh.meromorphicOn.extract_zeros_poles
    (fun x ↦ by
      rw [(hh x x.property).meromorphicOrderAt_eq,
        ← Nat.cast_analyticOrderNatAt (hfinite x x.property)]
      simp) hsfinite
  let P := fun z ↦ ∏ x ∈ s, (z - x) ^ analyticOrderNatAt h x
  have hprod : (∏ᶠ x, (· - x) ^ D x) = P := by
    rw [finprod_eq_prod_of_mulSupport_subset (s := s)]
    · funext z
      simp only [Finset.prod_apply, Pi.pow_apply]
      apply Finset.prod_congr rfl
      intro x hx
      rw [hD x (Metric.ball_subset_closedBall ((hs x).mp hx).1), zpow_natCast]
    · rw [Function.FactorizedRational.mulSupport]
      intro x hx
      exact (Set.Finite.mem_toFinset hsfinite).mpr hx
  have hPa : AnalyticOnNhd ℂ P K := by
    apply Finset.analyticOnNhd_fun_prod
    intro x hx
    fun_prop
  have heq' : h =ᶠ[Filter.codiscreteWithin K] fun z ↦ P z * g z := by
    change h =ᶠ[Filter.codiscreteWithin K] (∏ᶠ x, (· - x) ^ D x) • g at heq
    filter_upwards [heq] with z hz
    change h z = (∏ᶠ x, (· - x) ^ D x) z * g z at hz
    rw [hprod] at hz
    exact hz
  have hball : Set.EqOn h (fun z ↦ P z * g z) (Metric.ball a r) := by
    intro x hx
    have hxK := Metric.ball_subset_closedBall hx
    have he := eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp heq' x hxK
    have hK : ∀ᶠ z in nhdsWithin x {x}ᶜ, z ∈ K :=
      Filter.mem_of_superset
        (eventually_nhdsWithin_of_eventually_nhds (Metric.isOpen_ball.mem_nhds hx))
        Metric.ball_subset_closedBall
    have he' : h =ᶠ[nhdsWithin x {x}ᶜ] fun z ↦ P z * g z := by
      filter_upwards [he, hK] with z hz hzk
      exact hz hzk
    exact tendsto_nhds_unique
      ((hh x hxK).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (((hPa x hxK).continuousAt.mul (hg x hxK).continuousAt).tendsto
        |>.mono_left nhdsWithin_le_nhds |>.congr' he'.symm)
  refine ⟨s, hs, hord, g, hg, fun x hx ↦ hgne ⟨x, hx⟩, ?_⟩
  have hclosed := hball.of_subset_closure hh.continuousOn
    (hPa.continuousOn.mul hg.continuousOn)
    Metric.ball_subset_closedBall
    (show K ⊆ closure (Metric.ball a r) by rw [closure_ball a hr.ne'])
  exact hclosed


end
end HolomorphicAnosov
