import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.SmoothMetricPullback
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import HolomorphicAnosov.GhysAnosovConjugacy.ConjugateDistributionInvariant
import HolomorphicAnosov.GhysAnosovConjugacy.ConjugateDistributionIsCompl
import HolomorphicAnosov.GhysAnosovConjugacy.TransportedRestrictedIterateNorms

open scoped ContDiff Manifold
namespace HolomorphicAnosov.GhysAnosovConjugacy
noncomputable section
universe u v
variable {d : ℕ} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel d) X] [ChartedSpace (ComplexModel d) Y]
  [IsManifold (complexModel d) ∞ X] [IsManifold (complexModel d) ∞ Y]

attribute [local instance] complex_isManifold_real

open scoped Bundle in
/-- The transported stable and unstable subbundles, with the inverse-differential pullback metric, form Anosov data for the conjugated map. The iterate and contraction constants are inherited from the original datum. -/
def transportedAnosovDatum
    (h : Biholomorph d d X Y) (f : Biholomorph d d X X) (a : AnosovDatum f)
    (s u : ContinuousRealTangentSubbundle (realModel d) Y)
    (hs : ∀ y, s.toDistribution y = (a.splitting.stable.toDistribution (h.symm y)).map
      (mfderiv (realModel d) (realModel d) h (h.symm y)).toLinearMap)
    (hu : ∀ y, u.toDistribution y = (a.splitting.unstable.toDistribution (h.symm y)).map
      (mfderiv (realModel d) (realModel d) h (h.symm y)).toLinearMap) :
    AnosovDatum ((h.symm.trans f).trans h) := by
  let g : Biholomorph d d Y Y := (h.symm.trans f).trans h
  have hs_map : ∀ y, (s.toDistribution y).map
      (mfderiv (realModel d) (realModel d) g y).toLinearMap = s.toDistribution (g y) := by
    intro y
    rw [hs y, hs (g y)]
    exact conjugate_distribution_invariant h f a.splitting.stable.toDistribution
      a.splitting.stable_map y
  have hu_map : ∀ y, (u.toDistribution y).map
      (mfderiv (realModel d) (realModel d) g y).toLinearMap = u.toDistribution (g y) := by
    intro y
    rw [hu y, hu (g y)]
    exact conjugate_distribution_invariant h f a.splitting.unstable.toDistribution
      a.splitting.unstable_map y
  let splitting : InvariantRealTangentSplitting g.toReal :=
    { stable := s
      unstable := u
      isCompl := fun y ↦ by
        rw [hs y, hu y]
        exact conjugate_distribution_isCompl h a.splitting.stable.toDistribution
          a.splitting.unstable.toDistribution a.splitting.isCompl y
      stable_map := hs_map
      unstable_map := hu_map }
  let metric' := smoothMetricPullback h.toReal a.metric
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (fun y : Y ↦ TangentSpace (realModel d) y) :=
    ⟨metric'.toRiemannianMetric⟩
  refine { metric := metric'
           splitting := splitting
           k := a.k
           one_le_k := a.one_le_k
           stable_contracting := ?_
           unstable_contracting := ?_ }
  · intro y
    have hPQ : ∀ x, (a.splitting.stable.toDistribution x).map
        (mfderiv (realModel d) (realModel d) h x).toLinearMap = s.toDistribution (h x) := by
      intro x
      have hx := hs (h x)
      rw [h.symm_apply_apply] at hx
      exact hx.symm
    have hn := (transported_restricted_iterate_norms h f a.metric metric' rfl
      a.splitting.stable.toDistribution s.toDistribution
      a.splitting.stable_map hs_map hPQ a.k (h.symm y)).1
    change ‖(restrictedIterateDerivative g.toReal s.toDistribution hs_map a.k y).toContinuousLinearMap‖ < 1
    rw [h.apply_symm_apply] at hn
    rw [hn]
    exact a.stable_contracting (h.symm y)
  · intro y
    have hPQ : ∀ x, (a.splitting.unstable.toDistribution x).map
        (mfderiv (realModel d) (realModel d) h x).toLinearMap = u.toDistribution (h x) := by
      intro x
      have hx := hu (h x)
      rw [h.symm_apply_apply] at hx
      exact hx.symm
    have hn := (transported_restricted_iterate_norms h f a.metric metric' rfl
      a.splitting.unstable.toDistribution u.toDistribution
      a.splitting.unstable_map hu_map hPQ a.k (h.symm y)).2
    change ‖(restrictedIterateDerivative g.toReal u.toDistribution hu_map a.k y).symm.toContinuousLinearMap‖ < 1
    rw [h.apply_symm_apply] at hn
    rw [hn]
    exact a.unstable_contracting (h.symm y)


end
end HolomorphicAnosov.GhysAnosovConjugacy
