import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphZpowEquiv
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Dynamics.RelativeHyperbolicBasicSetG7

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7

open Set Filter _root_.Topology
open scoped BigOperators ENNReal ContDiff Manifold Bundle Classical
noncomputable section

/-- A relative hyperbolic basic set supplies the Fact One dynamical datum with the original smooth Riemannian metric. -/
theorem relative_to_factOneDatum
    {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
    [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    (f : Diffeomorph
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (Λ : Set M) (hΛ : RelativeHyperbolicBasicSet f Λ) :
    ∃ H : HyperbolicSetFactOneDatum f Λ, H.originalMetric = hΛ.metric := by
  let hforward : MapsTo f Λ Λ := by
    intro x hx
    exact (hΛ.invariant x).mpr hx
  let hbackward : MapsTo f.symm Λ Λ := by
    intro x hx
    have hi := hΛ.invariant (f.symm x)
    exact hi.mp (by simpa using hx)
  obtain ⟨U, hUopen, hΛU, hmax⟩ := hΛ.locally_maximal
  let stable : ContinuousTangentSubbundleOn
      (E := EuclideanSpace ℝ (Fin n)) Λ :=
    { fibre := hΛ.stable.distribution
      locally_trivial := by
        intro x
        simpa using hΛ.stable.locally_trivial x }
  let unstable : ContinuousTangentSubbundleOn
      (E := EuclideanSpace ℝ (Fin n)) Λ :=
    { fibre := hΛ.unstable.distribution
      locally_trivial := by
        intro x
        simpa using hΛ.unstable.locally_trivial x }
  refine ⟨{
    nonempty := hΛ.nonempty
    compact := hΛ.compact
    forward_mem := hforward
    backward_mem := hbackward
    originalMetric := hΛ.metric
    stable := stable
    unstable := unstable
    complementary := by
      intro x
      exact hΛ.isCompl x
    stable_invariant := by
      intro x
      simpa [stable, hforward] using hΛ.stable_map x
    unstable_invariant := by
      intro x
      simpa [unstable, hforward] using hΛ.unstable_map x
    C := hΛ.C
    one_le_C := hΛ.one_le_C
    rate := hΛ.rate
    rate_pos := hΛ.rate_pos
    rate_lt_one := hΛ.rate_lt_one
    stable_estimate := by
      intro k x v hv
      have h := hΛ.stable_bound x ⟨v, hv⟩ k
      simpa [stable, hyperbolicRiemannianNorm] using h
    unstable_estimate := by
      intro k x v hv
      have h := hΛ.unstable_bound x ⟨v, hv⟩ k
      simpa [unstable, hyperbolicRiemannianNorm] using h
    isolatingNeighborhood := U
    isolating_open := hUopen
    subset_isolating := hΛU
    locally_maximal := by
      intro x
      have hpow_fun : ∀ k : ℤ,
          (f.toHomeomorph ^ k).toFun = (f.toEquiv ^ k).toFun := by
        intro k
        have h := congrArg Equiv.toFun (CarrierAdapter.homeomorph_zpow_equiv f.toHomeomorph k)
        exact h
      constructor
      · intro hx k
        have hk := (hmax x).mp hx k
        change (f.toHomeomorph ^ k).toFun x ∈ U
        rw [hpow_fun k]
        exact hk
      · intro hx
        apply (hmax x).mpr
        intro k
        have hk := hx k
        change (f.toHomeomorph ^ k).toFun x ∈ U at hk
        rw [hpow_fun k] at hk
        exact hk }, rfl⟩


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
