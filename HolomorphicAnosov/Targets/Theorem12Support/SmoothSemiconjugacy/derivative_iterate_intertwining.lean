import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Logic.Function.Iterate
import HolomorphicAnosov.Targets.Theorem12Support.SmoothSemiconjugacy.derivative_intertwining

/-! The derivative of a smooth semiconjugacy intertwines the derivatives of matching iterates.
(Zhang, Theorem 1.2) -/

open scoped ContDiff Manifold Topology _root_.Topology

namespace HolomorphicAnosov.Theorem12SupportW2

noncomputable section

universe u v

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]
  [IsManifold I ∞ M] [IsManifold J ∞ N]
  (e : Diffeomorph I J M N ∞)

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- If `e` semiconjugates the smooth maps `f` and `g`, then its derivative intertwines the
derivatives of `f^[m]` and `g^[m]` for every `m`. -/
theorem derivative_iterate_intertwining {f : M → M} {g : N → N}
    (hf : ContMDiff I I ∞ f) (hg : ContMDiff J J ∞ g)
    (h : Function.Semiconj e f g) (m : ℕ) (x : M) :
    (mfderiv J J (g^[m]) (e x)).comp (mfderiv I J e x) =
      (mfderiv I J e ((f^[m]) x)).comp (mfderiv I I (f^[m]) x) :=
  derivative_intertwining e (hf.iterate m) (hg.iterate m) (h.iterate_right m) x

end

end HolomorphicAnosov.Theorem12SupportW2

