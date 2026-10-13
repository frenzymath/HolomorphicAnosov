import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Immersion

/-! This file defines complex structures compatible with the intrinsic real atlas of an immersed
leaf. (Ghys, §2, pp. 588–589; Demailly, I §3.A, p. 20; §3.C, p. 23) -/

open scoped ContDiff

namespace HolomorphicAnosov

universe u v

variable {r k d : ℕ} {L : Type u} {M : Type v}
  [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
  [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]

/-- A complex atlas compatible with the given intrinsic real leaf atlas, with real dimension twice
its complex dimension and a holomorphic immersed inclusion into the ambient manifold. (Ghys, pp.
588–589; Demailly, pp. 20, 23) -/
structure NativeLeafComplexUpgrade (k : ℕ) (inclusion : L → M) where
  real_rank : r = 2 * k
  charts : ChartedSpace (ComplexModel k) L
  complex_manifold : letI := charts
    IsManifold (complexModel k) ∞ L
  real_to_complex : ∀ e : OpenPartialHomeomorph L (Fin r → ℝ),
    e ∈ atlas (Fin r → ℝ) L →
    ∀ c : OpenPartialHomeomorph L (ComplexModel k),
      c ∈ charts.atlas →
      ContDiffOn ℝ ∞ (c ∘ e.symm) (e.target ∩ e.symm ⁻¹' c.source)
  complex_to_real : ∀ c : OpenPartialHomeomorph L (ComplexModel k),
    c ∈ charts.atlas →
    ∀ e : OpenPartialHomeomorph L (Fin r → ℝ),
      e ∈ atlas (Fin r → ℝ) L →
      ContDiffOn ℝ ∞ (e ∘ c.symm) (c.target ∩ c.symm ⁻¹' e.source)
  inclusion_holomorphic : letI := charts
    ContMDiff (complexModel k) (complexModel d) ∞ inclusion
  inclusion_immersion : letI := charts
    ∀ z : L, Manifold.IsImmersionAt (complexModel k) (complexModel d) ∞ inclusion z

end HolomorphicAnosov
