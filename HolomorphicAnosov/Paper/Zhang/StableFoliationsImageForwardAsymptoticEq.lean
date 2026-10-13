import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import Mathlib.Topology.UniformSpace.HeineCantor
import HolomorphicAnosov.Paper.Zhang.StableFoliationsForwardAsymptoticApplyIff

noncomputable section
open scoped Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
namespace StableFoliationsSupport

/-- A bijection maps the forward asymptotic point set through a point onto the forward asymptotic
point set through its image. -/
theorem image_forwardAsymptotic_eq {M : Type*} [MetricSpace M]
    (f : M ≃ M) (x : M) :
    f '' {y | ForwardAsymptotic f x y} = {y | ForwardAsymptotic f (f x) y} := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (forwardAsymptotic_apply_iff f x z).mpr hz
  · intro hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    apply (forwardAsymptotic_apply_iff f x (f.symm y)).mp
    simpa only [f.apply_symm_apply, Set.mem_ofPred_eq] using hy

end StableFoliationsSupport
end HolomorphicAnosov
