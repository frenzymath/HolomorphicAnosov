import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open scoped Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
namespace StableFoliationsSupport

/-- For a uniformly continuous map, forward asymptoticity is equivalent to forward asymptoticity
under any positive iterate. (Shub, Def. 2.1, pp.8–9) -/
theorem forwardAsymptotic_iterate_iff {M : Type*} [MetricSpace M]
    {f : M → M} (hf : UniformContinuous f) {N : ℕ} (hN : 0 < N) (x y : M) :
    ForwardAsymptotic (f^[N]) x y ↔ ForwardAsymptotic f x y := by
  constructor
  · intro h
    have hp : Tendsto (fun m : ℕ ↦ (((f^[N])^[m]) y, ((f^[N])^[m]) x))
        atTop (uniformity M) := tendsto_uniformity_iff_dist_tendsto_zero.mpr h
    have hres (r : Fin N) :
        Tendsto (fun m : ℕ ↦ dist ((f^[r.val]) (((f^[N])^[m]) y))
          ((f^[r.val]) (((f^[N])^[m]) x))) atTop (𝓝 0) :=
      tendsto_uniformity_iff_dist_tendsto_zero.mp
        (Filter.Tendsto.comp (UniformContinuous.iterate f r.val hf) hp)
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hall : ∀ᶠ m : ℕ in atTop, ∀ r : Fin N,
        dist (dist ((f^[r.val]) (((f^[N])^[m]) y))
          ((f^[r.val]) (((f^[N])^[m]) x))) 0 < ε :=
      eventually_all.mpr fun r ↦ (Metric.tendsto_nhds.mp (hres r)) ε hε
    have hdiv : Tendsto (fun n : ℕ ↦ n / N) atTop atTop :=
      le_of_eq (map_div_atTop_eq_nat N hN)
    filter_upwards [hdiv.eventually hall] with n hn
    have heq (z : M) :
        (f^[n % N]) (((f^[N])^[n / N]) z) = (f^[n]) z := by
      rw [← Function.iterate_mul, ← Function.iterate_add_apply, Nat.mod_add_div]
    simpa only [heq] using hn ⟨n % N, Nat.mod_lt n hN⟩
  · intro h
    have hmul : Tendsto (fun n : ℕ ↦ N * n) atTop atTop := by
      apply tendsto_atTop_mono (fun n ↦ Nat.le_mul_of_pos_left n hN) tendsto_id
    simpa only [ForwardAsymptotic, Function.comp_def, Function.iterate_mul] using h.comp hmul

end StableFoliationsSupport
end HolomorphicAnosov
