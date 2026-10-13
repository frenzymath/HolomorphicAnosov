import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

open Set
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

omit [IsManifold (complexModel d) ∞ X] in
/-- The real differential of a scalar function, expressed in an inverse-chart tangent frame, equals
its ordinary real coordinate derivative. (Zhang, §2.1, (5), p.5 and p.6) -/
theorem scalar_differential_chart_transport
    (g : X → ℂ) (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (z : ComplexModel d) (hz : z ∈ c.target)
    (hg : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) g (c.symm z)) :
    (QuotientLineConnection.realDifferential g (c.symm z)).comp
      ((mfderiv (realModel d) (realModel d) c.symm z).comp
        (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap) =
      fderiv ℝ (fun w ↦ g (c.symm w)) z := by
  have hcs : MDifferentiableAt (realModel d) (realModel d) c.symm z := by
    obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp
      (contMDiffAt_symm_of_mem_maximalAtlas hc hz)
    exact (contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp z hg hcs
  ext v
  change ((mfderiv (realModel d) 𝓘(ℝ, ℂ) g (c.symm z)).comp
    (mfderiv (realModel d) (realModel d) c.symm z)) v = _
  rw [← hcomp]
  exact congrArg (fun L ↦ L v) (mfderiv_eq_fderiv (𝕜 := ℝ) (f := g ∘ c.symm) (x := z))

end HolomorphicAnosov.ConnectionCalculus
