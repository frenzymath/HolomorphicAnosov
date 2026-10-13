import HolomorphicAnosov.Geometry.Manifold.VectorBundle.RealTangentDistribution
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Logic.Function.Iterate

/-!
A norm-preserving diffeomorphism transfers derivative estimates for iterates along a tangent distribution. (Zhang, §3, p.11)
-/

namespace HolomorphicAnosov.Theorem12SupportW4

open scoped Bundle ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H K : Type*} [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace K N]
  [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [Bundle.RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- A norm-preserving semiconjugating diffeomorphism transfers an iterate derivative bound on a
tangent distribution when the iterate derivatives satisfy the commuting square. (Zhang, Theorem
1.2, §3, p.11) -/
theorem rechart_iterate_vector_bound
    (e : Diffeomorph I J M N ∞) (f : Diffeomorph I I M M ∞)
    (g : Diffeomorph J J N N ∞) (P : RealTangentDistribution I M)
    (h : Function.Semiconj e f g)
    (hnorm : ∀ x (v : TangentSpace I x), ‖mfderiv I J e x v‖ = ‖v‖)
    (n : ℕ) (B : ℝ)
    (hderiv : ∀ x, (mfderiv J J ((g : N → N)^[n]) (e x)).comp (mfderiv I J e x) =
      (mfderiv I J e (((f : M → M)^[n]) x)).comp
        (mfderiv I I ((f : M → M)^[n]) x))
    (hbound : ∀ x (v : TangentSpace I x), v ∈ P x →
      ‖mfderiv I I ((f : M → M)^[n]) x v‖ ≤ B * ‖v‖)
    (x : M) (v : TangentSpace I x) (hv : v ∈ P x) :
    ‖mfderiv J J ((g : N → N)^[n]) (e x) (mfderiv I J e x v)‖ ≤
      B * ‖mfderiv I J e x v‖ := by
  have hval := congrArg (fun L ↦ L v) (hderiv x)
  have hnval := congrArg
    (fun w : TangentSpace J (e (((f : M → M)^[n]) x)) ↦ ‖w‖) hval
  have hendpoint := congrArg
    (fun z : N ↦ (fun w : F ↦ @norm (TangentSpace J z) inferInstance w))
    ((h.iterate_right n) x)
  have hp := congrFun hendpoint
    (mfderiv J J ((g : N → N)^[n]) (e x) (mfderiv I J e x v))
  calc
    _ = @norm (TangentSpace J (e (((f : M → M)^[n]) x))) inferInstance
        (mfderiv J J ((g : N → N)^[n]) (e x) (mfderiv I J e x v)) := hp.symm
    _ = ‖mfderiv I J e (((f : M → M)^[n]) x)
        (mfderiv I I ((f : M → M)^[n]) x v)‖ := hnval
    _ = ‖mfderiv I I ((f : M → M)^[n]) x v‖ := hnorm _ _
    _ ≤ B * ‖v‖ := hbound x v hv
    _ = _ := by rw [hnorm]

end HolomorphicAnosov.Theorem12SupportW4

