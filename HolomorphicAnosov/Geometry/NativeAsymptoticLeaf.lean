import HolomorphicAnosov.Dynamics.AsymptoticLeaf
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentDistribution
import Mathlib.Geometry.Manifold.Immersion

/-! This file defines intrinsic smooth immersed-leaf data on stable and unstable asymptotic point
sets. (Hirsch–Pugh–Shub, §6B–7, pp. 114–116; Ghys, §2, pp. 588–589; Shub, Def. 2.1, pp. 8–9) -/

namespace HolomorphicAnosov

open scoped ContDiff

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type v} [TopologicalSpace H]
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]

/-- An intrinsic connected smooth manifold structure on the forward asymptotic carrier, whose
inclusion is an immersion with tangent image equal to the specified distribution.
(Hirsch–Pugh–Shub, §6B–7, pp. 114–116; Ghys, §2, pp. 588–589) -/
structure NativeAsymptoticLeafDatum (I : ModelWithCorners ℝ E H)
    [IsManifold I ∞ M] (f : M ≃ₜ M) (P : RealTangentDistribution I M) (x : M) where
  /-- The finite real dimension of the intrinsic leaf. -/
  rank : ℕ
  /-- An intrinsic topology on the stable asymptotic carrier. -/
  topology : TopologicalSpace (StableAsymptoticLeaf f x)
  /-- Intrinsic real charts on the stable asymptotic carrier. -/
  charts : letI := topology
    ChartedSpace (Fin rank → ℝ) (StableAsymptoticLeaf f x)
  /-- The intrinsic leaf topology is Hausdorff. -/
  hausdorff : letI := topology
    T2Space (StableAsymptoticLeaf f x)
  /-- The intrinsic leaf topology has a countable base. -/
  secondCountable : letI := topology
    SecondCountableTopology (StableAsymptoticLeaf f x)
  /-- The intrinsic leaf is connected. -/
  connected : letI := topology
    ConnectedSpace (StableAsymptoticLeaf f x)
  /-- The intrinsic real atlas defines a smooth manifold without boundary. -/
  smoothAtlas : letI := topology; letI := charts
    IsManifold (modelWithCornersSelf ℝ (Fin rank → ℝ)) ∞ (StableAsymptoticLeaf f x)
  /-- The inclusion into the ambient manifold is smooth. -/
  inclusion_smooth : letI := topology; letI := charts
    ContMDiff (modelWithCornersSelf ℝ (Fin rank → ℝ)) I ∞
      (Subtype.val : StableAsymptoticLeaf f x → M)
  /-- The inclusion is an immersion at every leaf point. -/
  inclusion_immersion : letI := topology; letI := charts
    ∀ z : StableAsymptoticLeaf f x,
      Manifold.IsImmersionAt (modelWithCornersSelf ℝ (Fin rank → ℝ)) I ∞
        (Subtype.val : StableAsymptoticLeaf f x → M) z
  /-- The range of the inclusion differential equals the specified tangent distribution at every
  leaf point. -/
  tangent_image : letI := topology; letI := charts
    ∀ z : StableAsymptoticLeaf f x,
      LinearMap.range
        (mfderiv (modelWithCornersSelf ℝ (Fin rank → ℝ)) I
          (Subtype.val : StableAsymptoticLeaf f x → M) z).toLinearMap = P z.val

/-- Intrinsic unstable-leaf data are stable-leaf data for `f.symm`. (Shub, Def. 2.1, pp. 8–9; Ghys,
§2, pp. 588–589) -/
abbrev NativeUnstableAsymptoticLeafDatum (I : ModelWithCorners ℝ E H)
    [IsManifold I ∞ M] (f : M ≃ₜ M) (P : RealTangentDistribution I M) (x : M) :=
  NativeAsymptoticLeafDatum I f.symm P x

end HolomorphicAnosov
