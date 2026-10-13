import Mathlib.Analysis.Normed.Module.Basic

noncomputable section
namespace HolomorphicAnosov.BoundedLipschitzJets
open Filter Set
open scoped Topology _root_.Topology

/-- HPS p.28's affine radial interpolation on an annulus. -/
def annularWeight (r : ℕ → ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (r n - t) / (r n - r (n+1))

end HolomorphicAnosov.BoundedLipschitzJets

