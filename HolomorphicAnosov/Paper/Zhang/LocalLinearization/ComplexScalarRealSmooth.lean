import HolomorphicAnosov.Paper.Zhang.TransverseParallelCoordinates
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

open Set _root_.Topology
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
namespace HolomorphicAnosov.Paper.Zhang
noncomputable section
universe u

theorem localLinearization_complex_scalar_real_smooth
    {d : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    {s : Set M} {g : M → ℂ}
    (hg : ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ g s) :
    ContMDiffOn (realModel d) 𝓘(ℝ, ℂ) ∞ g s := by
  intro x hx
  have hh := hg x hx
  rw [contMDiffWithinAt_iff] at hh ⊢
  refine ⟨hh.1, ?_⟩
  simpa only [writtenInExtChartAt, mfld_simps] using hh.2.restrict_scalars ℝ


end
end HolomorphicAnosov.Paper.Zhang
