import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.SmoothMetricPullback
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HolomorphicAnosov.GhysAnosovConjugacy.ConjugateIterate
import HolomorphicAnosov.GhysAnosovConjugacy.ConjugateIterateDerivative
import HolomorphicAnosov.GhysAnosovConjugacy.RestrictedConjugateOperatorNorms

open scoped ContDiff Manifold
namespace HolomorphicAnosov.GhysAnosovConjugacy
noncomputable section
universe u v
variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel d) X] [ChartedSpace (ComplexModel d) Y]
  [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y]

attribute [local instance] complex_isManifold_real

set_option backward.isDefEq.respectTransparency false in
open scoped Bundle in
/-- Restricted stable forward and unstable inverse iterate norms are unchanged by conjugacy in the inverse-differential pullback metric. -/
theorem transported_restricted_iterate_norms
    (h : Biholomorph d d X Y) (f : Biholomorph d d X X)
    (metric : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x))
    (metric' : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun y : Y ↦ TangentSpace (realModel d) y))
    (hmetric : metric' = smoothMetricPullback h.toReal metric)
    (P : RealTangentDistribution (realModel d) X)
    (Q : RealTangentDistribution (realModel d) Y)
    (hP : ∀ x, (P x).map (mfderiv (realModel d) (realModel d) f x).toLinearMap = P (f x))
    (hQ : ∀ y, (Q y).map (mfderiv (realModel d) (realModel d)
      ((h.symm.trans f).trans h) y).toLinearMap = Q (((h.symm.trans f).trans h) y))
    (hPQ : ∀ x, (P x).map (mfderiv (realModel d) (realModel d) h x).toLinearMap = Q (h x))
    (n : ℕ) (x : X) :
    letI : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
      ⟨metric.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun y : Y ↦ TangentSpace (realModel d) y) :=
      ⟨metric'.toRiemannianMetric⟩
    ‖(restrictedIterateDerivative (Biholomorph.toReal ((h.symm.trans f).trans h))
      Q hQ n (h x)).toContinuousLinearMap‖ =
      ‖(restrictedIterateDerivative f.toReal P hP n x).toContinuousLinearMap‖ ∧
    ‖(restrictedIterateDerivative (Biholomorph.toReal ((h.symm.trans f).trans h))
      Q hQ n (h x)).symm.toContinuousLinearMap‖ =
      ‖(restrictedIterateDerivative f.toReal P hP n x).symm.toContinuousLinearMap‖ := by
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨metric.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (fun y : Y ↦ TangentSpace (realModel d) y) :=
    ⟨metric'.toRiemannianMetric⟩
  let g : Biholomorph d d Y Y := (h.symm.trans f).trans h
  have hiter : ((g : Y → Y)^[n]) (h x) = h (((f : X → X)^[n]) x) :=
    conjugate_iterate h f n x
  unfold restrictedIterateDerivative
  apply restricted_conjugate_operator_norms
    (V := TangentSpace (realModel d) x)
    (W := TangentSpace (realModel d) (h x))
    (V' := TangentSpace (realModel d) (((f : X → X)^[n]) x))
    (W' := TangentSpace (realModel d) (((g : Y → Y)^[n]) (h x)))
    (h.toReal.mfderivToContinuousLinearEquiv (by simp) x)
    (h.toReal.mfderivToContinuousLinearEquiv (by simp) (((f : X → X)^[n]) x))
    ((realIterate (realModel d) f.toReal n).mfderivToContinuousLinearEquiv (by simp) x)
    ((realIterate (realModel d) g.toReal n).mfderivToContinuousLinearEquiv (by simp) (h x))
    (P x) (Q (h x)) (P (((f : X → X)^[n]) x)) (Q (((g : Y → Y)^[n]) (h x)))
  · exact hPQ x
  · change (P (((f : X → X)^[n]) x)).map
      (mfderiv (realModel d) (realModel d) h (((f : X → X)^[n]) x)).toLinearMap =
      Q (((g : Y → Y)^[n]) (h x))
    rw [hiter]
    exact hPQ (((f : X → X)^[n]) x)
  · intro v
    subst metric'
    exact smoothMetricPullback_norm_forward h.toReal metric x v
  · intro v
    subst metric'
    have hn := smoothMetricPullback_norm_forward h.toReal metric (((f : X → X)^[n]) x) v
    change @norm _ (@NormedAddCommGroup.toNorm _
      (Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (h (((f : X → X)^[n]) x))))
      ((h.toReal.mfderivToContinuousLinearEquiv (by simp) (((f : X → X)^[n]) x)) v) = ‖v‖ at hn
    have hend := congrArg (fun y' : Y ↦ @norm (TangentSpace (realModel d) y')
      (@NormedAddCommGroup.toNorm _
        (Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
          y')) ((h.toReal.mfderivToContinuousLinearEquiv (by simp)
            (((f : X → X)^[n]) x)) v)) hiter
    exact hend.trans hn
  · exact conjugate_iterate_derivative h f n x


end
end HolomorphicAnosov.GhysAnosovConjugacy
