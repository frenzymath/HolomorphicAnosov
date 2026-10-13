import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import Mathlib.Topology.UniformSpace.HeineCantor
import HolomorphicAnosov.Paper.Zhang.StableFoliationsForwardAsymptoticApplyIff

noncomputable section
open scoped Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
namespace StableFoliationsSupport

/-- A bijection maps the inverse-time asymptotic point set through a point onto the inverse-time
asymptotic point set through its image. -/
theorem image_inverseAsymptotic_eq {M : Type*} [MetricSpace M]
    (f : M ≃ M) (x : M) :
    f '' {y | ForwardAsymptotic f.symm x y} =
      {y | ForwardAsymptotic f.symm (f x) y} := by
  have hs (z : M) : ForwardAsymptotic f.symm (f x) (f z) ↔
      ForwardAsymptotic f.symm x z := by
    simpa only [f.symm_apply_apply] using
      (forwardAsymptotic_apply_iff f.symm (f x) (f z)).symm
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (hs z).mpr hz
  · intro hy
    refine ⟨f.symm y, (hs (f.symm y)).mp ?_, f.apply_symm_apply y⟩
    simpa only [f.apply_symm_apply, Set.mem_ofPred_eq] using hy

end StableFoliationsSupport
end HolomorphicAnosov
