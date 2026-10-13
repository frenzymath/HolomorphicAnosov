import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateDerivative
import HolomorphicAnosov.Analysis.MovingOperatorNormStrictLocalBound
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeForwardInverse
import HolomorphicAnosov.Geometry.DiffeomorphDerivativeInverseForward
import HolomorphicAnosov.Geometry.DiffeomorphInverseIterateBasepoint
import HolomorphicAnosov.Geometry.DiffeomorphForwardInverseIterateBasepoint
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Tactic

noncomputable section
open Bundle Set Filter
open scoped ContDiff Manifold Topology _root_.Topology Bundle
namespace HolomorphicAnosov.FixedBlockEstimates.Native
universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The inverse frame of a local linear trivialization is continuous in the subbundle total-space
topology. -/
theorem continuous_frame_totalSpace {r : ℕ}
    (P : RealTangentDistribution 𝓘(ℝ, E) M)
    [TopologicalSpace (TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x)))]
    (e : Trivialization (Fin r → ℝ)
      (TotalSpace.proj (F := Fin r → ℝ) (E := fun x : M ↦ ↥(P x))))
    [e.IsLinear ℝ] :
    Continuous (fun p : e.baseSet × (Fin r → ℝ) ↦
      (⟨p.1.val, (e.linearEquivAt ℝ p.1.val p.1.prop).symm p.2⟩ :
        TotalSpace (Fin r → ℝ) (fun x : M ↦ ↥(P x)))) := by
  have h := e.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
    (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd)
    (fun p : e.baseSet × (Fin r → ℝ) ↦ e.mem_target.mpr p.1.prop)
  convert h using 1
  funext p
  exact e.toPretrivialization.mk_symm p.1.prop p.2

end HolomorphicAnosov.FixedBlockEstimates.Native
