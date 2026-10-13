import Mathlib.Geometry.Manifold.Diffeomorph

/-! The derivative of a smooth semiconjugacy intertwines the derivatives of the two maps. (Zhang,
Theorem 1.2) -/

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
/-- If the smooth diffeomorphism `e` semiconjugates `f` to `g`, then `Dg(e x) ∘ De(x) = De(f x) ∘
Df(x)`. (Zhang, Theorem 1.2) -/
theorem derivative_intertwining {f : M → M} {g : N → N}
    (hf : ContMDiff I I ∞ f) (hg : ContMDiff J J ∞ g)
    (h : Function.Semiconj e f g) (x : M) :
    (mfderiv J J g (e x)).comp (mfderiv I J e x) =
      (mfderiv I J e (f x)).comp (mfderiv I I f x) := by
  have he := e.contMDiff.mdifferentiable (by simp)
  have hleft := mfderiv_comp x (he (f x)) (hf.mdifferentiable (by simp) x)
  have hright := mfderiv_comp x (hg.mdifferentiable (by simp) (e x)) (he x)
  have hmaps : (e : M → N) ∘ f = g ∘ e := by
    funext z; exact h z
  rw [hmaps, hright] at hleft
  exact hleft

end
end HolomorphicAnosov.Theorem12SupportW2

