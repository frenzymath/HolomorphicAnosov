import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section
open scoped Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
namespace StableFoliationsSupport

/-- Two points are forward asymptotic if and only if their images under the map are forward
asymptotic. (Shub, Def. 2.1, pp.8–9) -/
theorem forwardAsymptotic_apply_iff {M : Type*} [MetricSpace M]
    (f : M → M) (x y : M) :
    ForwardAsymptotic f (f x) (f y) ↔ ForwardAsymptotic f x y := by
  simpa only [ForwardAsymptotic, Function.iterate_succ_apply] using
    (tendsto_add_atTop_iff_nat (f := fun n : ℕ ↦ dist ((f^[n]) y) ((f^[n]) x))
      (l := 𝓝 (0 : ℝ)) 1)

end StableFoliationsSupport
end HolomorphicAnosov
