import HolomorphicAnosov.Dynamics.HirschPughNativeLeafSystem
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathMap
import HolomorphicAnosov.Dynamics.NativeLeafPathAdvanceLength
import Mathlib.Basic.ENNReal.Inv

namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold ENNReal
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "I" => 𝓘(ℝ, E)

/-- The intrinsic native path infimum contracts under the original advance.

Agent-written infimum step of the Hirsch–Pugh intrinsic distance argument.
Map every source path to a receiving path and use its proved length bound.
The receiving infimum is below this candidate length. Positive finite scalar
multiplication commutes with the source infimum, including an empty path family;
thus no separate path-existence or distance-convention lemma is needed here. -/
theorem nativeLeafPathEDist_advance_le
    (f : Diffeomorph I I M M ∞)
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (S : NativeInvariantLeafSystem I D f)
    (h : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {θ : ℝ} (hθpos : 0 < θ)
    (hθ : ∀ (x : M) (v : TangentSpace I x), v ∈ D x →
      hyperbolicRiemannianNorm h (mfderiv I I f x v) ≤ θ * hyperbolicRiemannianNorm h v)
    (x : M) (y z : (S.leaf x).Carrier) :
    nativeLeafPathEDist I h (S.leaf (f x)) (S.advance x y) (S.advance x z) ≤
      ENNReal.ofReal θ * nativeLeafPathEDist I h (S.leaf x) y z := by
  unfold nativeLeafPathEDist
  rw [ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hθpos)) ENNReal.ofReal_ne_top]
  apply le_iInf
  intro p
  calc
    nativeLeafPathEDist I h (S.leaf (f x)) (S.advance x y) (S.advance x z) ≤
      ENNReal.ofReal (nativeLeafPathLength I h (S.leaf (f x))
        (p.map (S.advance x) (S.advance x).contMDiff)) := iInf_le _ _
    _ ≤ ENNReal.ofReal (θ * nativeLeafPathLength I h (S.leaf x) p) :=
      ENNReal.ofReal_le_ofReal (nativeLeafPath_advance_length_le f S h θ hθ x p)
    _ = _ := ENNReal.ofReal_mul hθpos.le

end HolomorphicAnosov
