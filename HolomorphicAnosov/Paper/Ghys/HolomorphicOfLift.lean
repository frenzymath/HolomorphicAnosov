import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import Mathlib.Geometry.Manifold.LocalDiffeomorph

noncomputable section
open scoped ContDiff Manifold Topology
open Filter Set _root_.Topology

universe u v w
namespace HolomorphicAnosov.Ghys
attribute [local instance] complex_isManifold_real

/-- A continuous lift through a local biholomorphism is holomorphic if its projection is
holomorphic. (Hatcher, Prop. 1.33, pp. 61–62; Ghys, §5, pp. 597–598) -/
theorem holomorphic_of_lift
    {k d : ℕ} {L E M : Type*}
    [TopologicalSpace L] [TopologicalSpace E] [TopologicalSpace M]
    [ChartedSpace (ComplexModel k) L] [ChartedSpace (ComplexModel d) E]
    [ChartedSpace (ComplexModel d) M]
    {p : E → M} (hp : IsLocalDiffeomorph (complexModel d) (complexModel d) ∞ p)
    (lift : L → E) (hlift : Continuous lift)
    (hproj : ContMDiff (complexModel k) (complexModel d) ∞ (p ∘ lift)) :
    ContMDiff (complexModel k) (complexModel d) ∞ lift := by
  intro x
  have hlocal := hp (lift x)
  have hsmooth := hlocal.localInverse_contMDiffAt.comp x (hproj x)
  apply hsmooth.congr_of_eventuallyEq
  have heq := (hlift.tendsto x).eventually hlocal.localInverse_eventuallyEq_left
  filter_upwards [heq] with z hz
  exact hz.symm

end HolomorphicAnosov.Ghys

