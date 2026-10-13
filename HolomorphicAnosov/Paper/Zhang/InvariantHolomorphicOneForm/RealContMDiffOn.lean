import Mathlib.Geometry.Manifold.ContMDiff.Defs
import HolomorphicAnosov.Geometry.ComplexToRealManifold

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.OneFormBundle

attribute [local instance] complex_isManifold_real
universe u

/-- A complex smooth coordinate-valued map remains smooth after restricting scalars to ℝ on the same
domain. -/
theorem real_contMDiffOn {d : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G]
    [IsScalarTower ℝ ℂ G] {n : ℕ∞ω} {f : M → G} {s : Set M}
    (hf : ContMDiffOn (complexModel d) 𝓘(ℂ, G) n f s) :
    ContMDiffOn (realModel d) 𝓘(ℝ, G) n f s := by
  intro x hx
  obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (hf x hx)
  exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩


end HolomorphicAnosov.OneFormBundle
