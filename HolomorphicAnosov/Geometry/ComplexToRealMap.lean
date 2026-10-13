import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.ContMDiff.Defs


/-!
# Scalar restriction for manifold maps

This file proves that complex manifold differentiability implies real differentiability of the same order in the same charts. (Demailly, §3.C; Ghys, §2)
-/

open scoped ContDiff

universe u v

namespace HolomorphicAnosov

/-- A complex `ContMDiff` map is real `ContMDiff` of the same order in the same charts. (Demailly, §3.C; Ghys, §2) -/
theorem contMDiff_complex_to_real {d e : ℕ} {X : Type u} {Y : Type v}
    [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [TopologicalSpace Y] [ChartedSpace (ComplexModel e) Y]
    {n : ℕ∞ω} {f : X → Y}
    (hf : ContMDiff (complexModel d) (complexModel e) n f) :
    ContMDiff (realModel d) (realModel e) n f := by
  intro x
  obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp (hf x)
  exact contMDiffAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩

end HolomorphicAnosov
