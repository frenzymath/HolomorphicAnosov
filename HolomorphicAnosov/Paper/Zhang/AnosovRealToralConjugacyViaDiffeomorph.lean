import HolomorphicAnosov.Targets.Theorem12Support.SmoothSemiconjugacy.conjugatedDiffeomorph
import HolomorphicAnosov.Targets.Theorem12Support.SmoothSemiconjugacy.derivative_iterate_intertwining
import HolomorphicAnosov.Targets.Theorem12Support.InvariantDistributionTransport.rechart_distribution_invariant
import HolomorphicAnosov.Targets.Theorem12Support.InvariantDistributionTransport.rechart_distribution_isCompl
import HolomorphicAnosov.Geometry.PullbackMetricIterateNorm
import HolomorphicAnosov.GhysTangentTransport.TransportedSubbundle
import HolomorphicAnosov.Geometry.SmoothMetricPullback
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import HolomorphicAnosov.Topology.FranksManning










noncomputable section
open scoped ContDiff Manifold Bundle Topology _root_.Topology
open Set
namespace HolomorphicAnosov
universe u v
attribute [local instance] complex_isManifold_real
















theorem holomorphic_anosov_real_toral_conjugacy_via_diffeomorph
    {d n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsCompactComplexManifold d X]
    {Y : Type v} [TopologicalSpace Y]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ Y]
    [CompactSpace Y] [ConnectedSpace Y] [T2Space Y] [SecondCountableTopology Y]
    (e : Diffeomorph (realModel d) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) X Y ∞)
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    (hT : Nonempty (X ≃ₜ UnitAddTorus (Fin n))) :
    HyperbolicRealToralConjugacy n X (fun x ↦ f x) := by
  classical
  let originalReal : Diffeomorph (realModel d) (realModel d) X X ∞ := f.toReal
  let : Bundle.RiemannianBundle (fun x : X ↦ TangentSpace (realModel d) x) :=
    ⟨a.metric.toRiemannianMetric⟩
  obtain ⟨C, lam, hC, hlam, hlam1, hStableAll, hUnstableAll⟩ :=
    fixed_block_uniform_anosov_estimates f a
  let g := Theorem12SupportW2.conjugatedDiffeomorph e originalReal
  let Sr := GhysTangentTransport.transportedSubbundle e a.splitting.stable
  let Ur := GhysTangentTransport.transportedSubbundle e a.splitting.unstable
  have hRechartForward : Function.Semiconj e originalReal g :=
    e.toEquiv.semiconj_conj originalReal
  have hRechartInverse : Function.Semiconj e originalReal.symm g.symm :=
    hRechartForward.inverses_right originalReal.apply_symm_apply g.symm_apply_apply
  have hRechartStable (y : (Y)) :
      (Sr.toDistribution y).map
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (n))) g y).toLinearMap =
        Sr.toDistribution (g y) :=
    Theorem12SupportW4.rechart_distribution_invariant e originalReal g
      a.splitting.stable.toDistribution a.splitting.stable_map hRechartForward
      (Theorem12SupportW2.derivative_intertwining e originalReal.contMDiff
        g.contMDiff hRechartForward) y
  have hRechartUnstable (y : (Y)) :
      (Ur.toDistribution y).map
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin (n)))
          𝓘(ℝ, EuclideanSpace ℝ (Fin (n))) g y).toLinearMap =
        Ur.toDistribution (g y) :=
    Theorem12SupportW4.rechart_distribution_invariant e originalReal g
      a.splitting.unstable.toDistribution a.splitting.unstable_map hRechartForward
      (Theorem12SupportW2.derivative_intertwining e originalReal.contMDiff
        g.contMDiff hRechartForward) y
  have hRechartComplement (y : (Y)) : IsCompl (Sr.toDistribution y) (Ur.toDistribution y) :=
    Theorem12SupportW4.rechart_distribution_isCompl e
      a.splitting.stable.toDistribution a.splitting.unstable.toDistribution
      a.splitting.isCompl y
  have hTorusRecharted : Nonempty ((Y) ≃ₜ UnitAddTorus (Fin (n))) := by
    obtain ⟨q⟩ := hT
    exact ⟨e.toHomeomorph.symm.trans q⟩
  let metricR := smoothMetricPullback e a.metric
  have hFranksApplication : HyperbolicRealToralConjugacy n Y g := by
    let : Bundle.RiemannianBundle
        (fun y : Y ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) y) :=
      ⟨metricR.toRiemannianMetric⟩
    apply franks_manning g Sr Ur metricR C lam hTorusRecharted hC hlam hlam1
      hRechartComplement hRechartStable hRechartUnstable
    · intro y n v hv
      obtain ⟨x, rfl⟩ := e.surjective y
      change v ∈ (a.splitting.stable.toDistribution (e.symm (e x))).map
        (GhysTangentTransport.tangentEquiv e (e.symm (e x))).toLinearEquiv.toLinearMap at hv
      rw [e.symm_apply_apply] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      calc
        _ = ‖mfderiv (realModel d) (realModel d) ((originalReal : X → X)^[n]) x w‖ :=
          smoothMetricPullback_iterate_norm e a.metric originalReal.contMDiff
            g.contMDiff hRechartForward n x w
        _ ≤ (C * lam ^ n) * ‖w‖ := hStableAll n x w hw
        _ = _ := by
          change C * lam ^ n * ‖w‖ =
            C * lam ^ n * ‖GhysTangentTransport.tangentEquiv e x w‖
          rw [show GhysTangentTransport.tangentEquiv e x w =
            mfderiv (realModel d) _ e x w from rfl]
          rw [smoothMetricPullback_norm_forward e a.metric]
    · intro y n v hv
      obtain ⟨x, rfl⟩ := e.surjective y
      change v ∈ (a.splitting.unstable.toDistribution (e.symm (e x))).map
        (GhysTangentTransport.tangentEquiv e (e.symm (e x))).toLinearEquiv.toLinearMap at hv
      rw [e.symm_apply_apply] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      calc
        _ = ‖mfderiv (realModel d) (realModel d) ((originalReal.symm : X → X)^[n]) x w‖ :=
          smoothMetricPullback_iterate_norm e a.metric originalReal.symm.contMDiff
            g.symm.contMDiff hRechartInverse n x w
        _ ≤ (C * lam ^ n) * ‖w‖ := hUnstableAll n x w hw
        _ = _ := by
          change C * lam ^ n * ‖w‖ =
            C * lam ^ n * ‖GhysTangentTransport.tangentEquiv e x w‖
          rw [show GhysTangentTransport.tangentEquiv e x w =
            mfderiv (realModel d) _ e x w from rfl]
          rw [smoothMetricPullback_norm_forward e a.metric]
  have hRealToralModel : HyperbolicRealToralConjugacy n Y g := hFranksApplication
  
  
  
  have hOriginalRealToralModel : HyperbolicRealToralConjugacy (n) X f := by
    obtain ⟨A, h, hHyper, hConj⟩ := hRealToralModel
    refine ⟨A, e.toHomeomorph.trans h, hHyper, ?_⟩
    intro x
    change h (e (f x)) = integralToralMap A (h (e x))
    change h (e (originalReal x)) = integralToralMap A (h (e x))
    rw [hRechartForward x]
    exact hConj (e x)
  exact hOriginalRealToralModel

end HolomorphicAnosov
