import HolomorphicAnosov.Geometry.HermitianTangentMetric
import HolomorphicAnosov.Geometry.BiholomorphToReal
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology
universe u
namespace HolomorphicAnosov
attribute [local instance] complex_isManifold_real
namespace StableFoliationsSupport

/-- The Hermitian pairing of any two fixed coordinate vectors in an inverse-chart differential frame
varies smoothly on the chart target. (Moroianu, §4.2, pp.24–25; Demailly, VI §4, p.296) -/
theorem pairing_inverse_chart_smooth {d : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (ComplexModel d) M] [IsManifold (complexModel d) ∞ M]
    (h : HermitianTangentMetricCore d M) (hh : IsSmoothHermitianTangentMetric h)
    (e : OpenPartialHomeomorph M (ComplexModel d))
    (he : e ∈ IsManifold.maximalAtlas (complexModel d) ∞ M)
    (v w : ComplexModel d) :
    ContDiffOn ℝ ∞ (fun z ↦ hermitianTangentPairing h (e.symm z)
      (mfderiv (complexModel d) (complexModel d) e.symm z
        ((NormedSpace.fromTangentSpace z).symm v))
      (mfderiv (complexModel d) (complexModel d) e.symm z
        ((NormedSpace.fromTangentSpace z).symm w))) e.target := by
  induction v using Pi.single_induction with
  | zero => simp only [map_zero, hermitianTangentPairing, InnerProductSpace.Core.inner_zero_right]; exact contDiffOn_const
  | add v₁ v₂ hv₁ hv₂ =>
      simpa only [map_add, hermitianTangentPairing, InnerProductSpace.Core.inner_add_right] using hv₁.add hv₂
  | single i a =>
      induction w using Pi.single_induction with
      | zero => simp only [map_zero, hermitianTangentPairing, InnerProductSpace.Core.inner_zero_left]; exact contDiffOn_const
      | add w₁ w₂ hw₁ hw₂ =>
          simpa only [map_add, hermitianTangentPairing, InnerProductSpace.Core.inner_add_left] using hw₁.add hw₂
      | single j b =>
          have hi : Pi.single i a = a • Pi.single i (1 : ℂ) := by ext k; simp [Pi.single_apply]
          have hj : Pi.single j b = b • Pi.single j (1 : ℂ) := by ext k; simp [Pi.single_apply]
          rw [hi, hj]
          simp only [map_smul, hermitianTangentPairing, InnerProductSpace.Core.inner_smul_left,
            InnerProductSpace.Core.inner_smul_right]
          exact contDiffOn_const.mul (contDiffOn_const.mul (hh e he i j))

end StableFoliationsSupport
end HolomorphicAnosov
