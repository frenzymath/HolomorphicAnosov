import HolomorphicAnosov.Targets.Theorem12Support.InvariantDistributionTransport.rechartDistribution
import HolomorphicAnosov.Targets.Theorem12Support.InvariantDistributionTransport.map_submodule_of_commuting_diagram

/-!
Invariance of a tangent distribution is preserved by a semiconjugating diffeomorphism with a commuting derivative square. (Zhang, Theorem 1.2)
-/

namespace HolomorphicAnosov.Theorem12SupportW4

open scoped Bundle ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]

/-- An invariant real tangent distribution remains invariant after transport by a semiconjugating
diffeomorphism whose derivatives satisfy the commuting square. (Zhang, Theorem 1.2) -/
theorem rechart_distribution_invariant
    (e : Diffeomorph I J M N ∞) (f : Diffeomorph I I M M ∞)
    (g : Diffeomorph J J N N ∞) (P : RealTangentDistribution I M)
    (hP : ∀ x, (P x).map (mfderiv I I f x).toLinearMap = P (f x))
    (h : Function.Semiconj e f g)
    (hderiv : ∀ x, (mfderiv J J g (e x)).comp (mfderiv I J e x) =
      (mfderiv I J e (f x)).comp (mfderiv I I f x)) (y : N) :
    (rechartDistribution e P y).map (mfderiv J J g y).toLinearMap =
      rechartDistribution e P (g y) := by
  have hx : e.symm (g y) = f (e.symm y) := by
    have hh := h (e.symm y)
    rw [e.apply_symm_apply] at hh
    rw [← hh, e.symm_apply_apply]
  have hi := map_submodule_of_commuting_diagram
    (P (e.symm y)) (P (f (e.symm y)))
    (mfderiv I I f (e.symm y)).toLinearMap
    (mfderiv I J e (e.symm y)).toLinearMap
    (mfderiv I J e (f (e.symm y))).toLinearMap
    (mfderiv J J g (e (e.symm y))).toLinearMap
    (hP (e.symm y))
    (congrArg ContinuousLinearMap.toLinearMap (hderiv (e.symm y)))
  rw [e.apply_symm_apply] at hi
  unfold rechartDistribution
  rw [hx]
  exact hi


end HolomorphicAnosov.Theorem12SupportW4
