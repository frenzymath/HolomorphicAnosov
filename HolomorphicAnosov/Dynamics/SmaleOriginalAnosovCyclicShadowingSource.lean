import HolomorphicAnosov.Dynamics.HirschPughAdaptedOrbitPlaques
import HolomorphicAnosov.Dynamics.SmaleMetricComparison
import HolomorphicAnosov.Dynamics.CompactBracketFiniteShadowingG5

namespace HolomorphicAnosov
open Set Filter
open scoped ContDiff _root_.HolomorphicAnosov.Topology _root_.Topology Bundle
universe u

/-- An Anosov diffeomorphism has cyclic shadowing in its original metric, with tolerance independent
of the period (Shub, Props. 8.20 and 8.5). -/
theorem smale_original_anosov_cyclic_shadowing_source
    {n : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M] [SecondCountableTopology M]
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (Es Eu : ContinuousRealTangentSubbundle
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M)
    (metric : Bundle.ContMDiffRiemannianMetric
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M => TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x))
    (C lam : ℝ) :
    let I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨metric.toRiemannianMetric⟩
    IsRiemannianManifold I M →
    0 < C → 0 < lam → lam < 1 →
    (∀ x, IsCompl (Es.toDistribution x) (Eu.toDistribution x)) →
    (∀ x, (Es.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Es.toDistribution (f x)) →
    (∀ x, (Eu.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Eu.toDistribution (f x)) →
    (∀ x k (v : TangentSpace I x), v ∈ Es.toDistribution x →
      ‖mfderiv I I ((f : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    (∀ x k (v : TangentSpace I x), v ∈ Eu.toDistribution x →
      ‖mfderiv I I ((f.symm : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ), 0 < n → ∀ q : Fin n → M,
        (∀ i, dist (f (q i)) (q (finRotate n i)) < δ) →
          ∃ j : Fin n → M, Function.Semiconj j (finRotate n) f ∧
            ∀ i, dist (j i) (q i) ≤ ε := by
  classical
  dsimp only
  let : Bundle.RiemannianBundle (fun x : M ↦
      TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x) :=
    ⟨metric.toRiemannianMetric⟩
  intro _hRiem hC hlam hlam1 hcompl hEs hEu hs hu η hη
  let originalDistance : MetricSpace M := inferInstance
  let splitting : InvariantRealTangentSplitting f :=
    { stable := Es
      unstable := Eu
      isCompl := hcompl
      stable_map := hEs
      unstable_map := hEu }
  have hsAP : ∀ x k (v : TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x),
      v ∈ splitting.stable.toDistribution x →
      hyperbolicRiemannianNorm metric (mfderiv _ _ ((f : M → M)^[k]) x v) ≤
        max 1 C * lam^k * hyperbolicRiemannianNorm metric v := by
    intro x k v hv
    exact (hs x k v hv).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 C) (pow_nonneg hlam.le k))
      (norm_nonneg v))
  have huAP : ∀ x k (v : TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x),
      v ∈ splitting.unstable.toDistribution x →
      hyperbolicRiemannianNorm metric (mfderiv _ _ ((f.symm : M → M)^[k]) x v) ≤
        max 1 C * lam^k * hyperbolicRiemannianNorm metric v := by
    intro x k v hv
    exact (hu x k v hv).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 C) (pow_nonneg hlam.le k))
      (norm_nonneg v))
  obtain ⟨hAP, dAP, componentDistance, θAP, rate, β, γ, ε,
    hD, hθ, hθ1, hrate, hrate1, hγ, hβ, hε, htop, hmetric, hcomponents,
    hforward, hbackward, S, U, hS, hU, hstablePair, hunstablePair,
    hSlength, hUlength, hSadvance, hUadvance, bracket, hbracketContinuous,
    hbracketUnique, hproduct⟩ :=
    hirschPughAdaptedOrbitPlaques f splitting metric (max 1 C) lam
      (le_max_left 1 C) hlam hlam1 hsAP huAP
  let : MetricSpace M := originalDistance
  let d := dAP.replaceTopology htop.symm
  let : MetricSpace M := originalDistance
  apply compact_compatible_metric_cyclic_shadowing d rfl (f : M → M) ?_ η hη
  let : MetricSpace M := d
  let e : M ≃ₜ M := f.toHomeomorph
  let b : M × M → M := fun p ↦ if hp : dist p.1 p.2 < ε then bracket ⟨p, hp⟩ else p.1
  have hb : ContinuousOn b {p | dist p.1 p.2 < ε} := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (fun p : {p : M × M | dist p.1 p.2 < ε} ↦ b p) = bracket := by
      funext p
      dsimp only [b]
      split_ifs with hp
      · rfl
      · exact (hp p.property).elim
    change Continuous (fun p : {p : M × M | dist p.1 p.2 < ε} ↦ b p)
    rw [heq]
    exact hbracketContinuous
  have hbr : ∀ x y, dist x y < ε →
      {z | ∀ k : ℕ, dist ((e : M → M)^[k] z) ((e : M → M)^[k] x) ≤ γ} ∩
      {z | ∀ k : ℕ, dist ((e.symm : M → M)^[k] z) ((e.symm : M → M)^[k] y) ≤ γ}
        = {b (x, y)} := by
    intro x y hxy
    dsimp only [b]
    rw [dite_eq_left hxy]
    exact hbracketUnique ⟨(x, y), hxy⟩
  have hstable : ∀ x y, (∀ k : ℕ, dist ((e : M → M)^[k] y) ((e : M → M)^[k] x) ≤ γ) →
      ∀ k : ℕ, dist ((e : M → M)^[k] y) ((e : M → M)^[k] x) ≤ rate^k * dist y x := by
    intro x y hy k
    exact hstablePair x y hy x (fun k ↦ by simpa using hγ.le) k
  have hunstable : ∀ x y, (∀ k : ℕ, dist ((e.symm : M → M)^[k] y)
      ((e.symm : M → M)^[k] x) ≤ γ) →
      ∀ k : ℕ, dist ((e.symm : M → M)^[k] y) ((e.symm : M → M)^[k] x) ≤ rate^k * dist y x := by
    intro x y hy k
    exact hunstablePair x y hy x (fun k ↦ by simpa using hγ.le) k
  have hexp : ∀ x y : M,
      (∀ k : ℤ, dist ((e.toEquiv^k) x) ((e.toEquiv^k) y) ≤ γ) → x = y := by
    intro x y hxy
    have heq := hbr x x (by simpa using hε)
    have hx : x ∈
        {z | ∀ k : ℕ, dist ((e : M → M)^[k] z) ((e : M → M)^[k] x) ≤ γ} ∩
        {z | ∀ k : ℕ, dist ((e.symm : M → M)^[k] z) ((e.symm : M → M)^[k] x) ≤ γ} := by
      constructor <;> intro k <;> simpa using hγ.le
    have hy : y ∈
        {z | ∀ k : ℕ, dist ((e : M → M)^[k] z) ((e : M → M)^[k] x) ≤ γ} ∩
        {z | ∀ k : ℕ, dist ((e.symm : M → M)^[k] z) ((e.symm : M → M)^[k] x) ≤ γ} := by
      constructor
      · intro k
        have hh := hxy (k:ℤ)
        rw [zpow_natCast, Equiv.Perm.coe_pow, dist_comm] at hh
        exact hh
      · intro k
        have hh := hxy (-(k:ℤ))
        rw [zpow_neg, zpow_natCast, ← inv_pow, Equiv.Perm.coe_pow, dist_comm] at hh
        exact hh
    rw [heq] at hx hy
    exact (mem_singleton_iff.mp hx).trans (mem_singleton_iff.mp hy).symm
  exact cyclic_shadowing_of_full_shadowing_expansive_g5 e γ hγ hexp
    (compact_full_shadowing_of_forward_segments_g5 e
      (compact_bracket_finite_shadowing_g5 e γ ε rate hγ hε hrate.le hrate1
        b hb hbr hstable hunstable))

end HolomorphicAnosov
