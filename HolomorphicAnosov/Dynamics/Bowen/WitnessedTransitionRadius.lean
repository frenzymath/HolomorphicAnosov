import HolomorphicAnosov.Dynamics.Bowen.BracketCovarianceRadius

namespace HolomorphicAnosov.Dynamics.Bowen
open Set

/-- Bowen's witnessed-transition extension, Lemma 25, pp.739–740, with a uniform
smallness guard from Lemma 11(a). The sets need only be bracket closed and small;
compactness, nonempty interiors and regular closure of these sets are not used.

Choose the guarded covariance radius. For a stable source point z at x, transport
it to p=[w,z] at the witness w. Its image belongs to F by the witnessed law.
Uniqueness gives z=[x,p]; covariance and bracket closure put fz in F. Forward
shifting gives its stable membership at fx. For an unstable target point t at fx,
put p=[t,fw]. Pull p back using the witnessed unstable covering to q in E.
Then v=[q,x] belongs to E and the unstable plaque at x, and covariance gives
fv=[p,fx]=t. The final equality is uniqueness: p is stable to t, hence t is
stable to p by symmetry of orbit distances, and t is unstable to fx by hypothesis.
DAG: `dynamics.bowen_witnessed_transition_radius_g17`. -/
theorem exists_witnessed_transition_radius
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ lam : ℝ) (H : CompactLocalProductData f γ lam) :
    ∃ r : ℝ, 0 < r ∧ r ≤ H.closeRadius ∧
      ∀ E F : Set X,
        (∀ x ∈ E, ∀ y ∈ E, dist x y ≤ r) →
        (∀ x ∈ F, ∀ y ∈ F, dist x y ≤ r) →
        (∀ x ∈ E, ∀ y ∈ E, H.bracket x y ∈ E) →
        (∀ x ∈ F, ∀ y ∈ F, H.bracket x y ∈ F) →
        ∀ w ∈ E, f w ∈ F →
          (f '' (E ∩ relativeClosedStablePlaque f γ w) ⊆
            F ∩ relativeClosedStablePlaque f γ (f w)) →
          (F ∩ relativeClosedUnstablePlaque f γ (f w) ⊆
            f '' (E ∩ relativeClosedUnstablePlaque f γ w)) →
          ∀ x ∈ E, f x ∈ F →
            (f '' (E ∩ relativeClosedStablePlaque f γ x) ⊆
              F ∩ relativeClosedStablePlaque f γ (f x)) ∧
            (F ∩ relativeClosedUnstablePlaque f γ (f x) ⊆
              f '' (E ∩ relativeClosedUnstablePlaque f γ x)) := by
  obtain ⟨r, hr, hrcore, hcov⟩ := exists_bracket_covariance_radius f γ lam H
  refine ⟨r, hr, hrcore, ?_⟩
  intro E F hEsmall hFsmall hEb hFb w hw hfw hstable hunstable x hx hfx
  constructor
  · rintro t ⟨z, hz, rfl⟩
    let p := H.bracket w z
    have hpE : p ∈ E := hEb w hw z hz.1
    have hp := H.bracket_mem w z ((hEsmall w hw z hz.1).trans hrcore)
    have hfpF : f p ∈ F := (hstable ⟨p, ⟨hpE, hp.1⟩, rfl⟩).1
    have hzp : z = H.bracket x p := by
      apply H.bracket_unique x p z ((hEsmall x hx p hpE).trans hrcore)
      exact ⟨hz.2, fun n ↦ by simpa only [dist_comm] using hp.2 n⟩
    constructor
    · rw [hzp, hcov x p (hEsmall x hx p hpE) (hFsmall (f x) hfx (f p) hfpF)]
      exact hFb (f x) hfx (f p) hfpF
    · intro n
      simpa only [Function.iterate_succ_apply] using hz.2 (n + 1)
  · intro t ht
    let p := H.bracket t (f w)
    have hpF : p ∈ F := hFb t ht.1 (f w) hfw
    have hp := H.bracket_mem t (f w) ((hFsmall t ht.1 (f w) hfw).trans hrcore)
    obtain ⟨q, hq, hfq⟩ := hunstable ⟨hpF, hp.2⟩
    refine ⟨H.bracket q x, ⟨hEb q hq.1 x hx,
      (H.bracket_mem q x ((hEsmall q hq.1 x hx).trans hrcore)).2⟩, ?_⟩
    rw [hcov q x (hEsmall q hq.1 x hx)
      (hFsmall (f q) (hfq ▸ hpF) (f x) hfx), hfq]
    symm
    apply H.bracket_unique p (f x) t ((hFsmall p hpF (f x) hfx).trans hrcore)
    exact ⟨fun n ↦ by simpa only [dist_comm] using hp.1 n, ht.2⟩

end HolomorphicAnosov.Dynamics.Bowen
