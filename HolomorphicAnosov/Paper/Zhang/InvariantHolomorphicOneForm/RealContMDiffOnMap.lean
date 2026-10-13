import Mathlib.Geometry.Manifold.ContMDiff.Defs
import HolomorphicAnosov.Geometry.ComplexToRealManifold

open Bundle Set
open scoped ContDiff Bundle Manifold
open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.OneFormBundle

attribute [local instance] complex_isManifold_real
universe u

/-- A complex smooth manifold map remains smooth after restricting the source and target manifold
structures to real scalars. -/
theorem real_contMDiffOn_map {d e : ℕ} {M N : Type*}
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [TopologicalSpace N] [ChartedSpace (ComplexModel e) N]
    {n : ℕ∞ω} {f : M → N} {s : Set M}
    (hf : ContMDiffOn (complexModel d) (complexModel e) n f s) :
    ContMDiffOn (realModel d) (realModel e) n f s := by
  intro x hx
  obtain ⟨hc, hd⟩ := contMDiffWithinAt_iff.mp (hf x hx)
  exact contMDiffWithinAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩



end HolomorphicAnosov.OneFormBundle
