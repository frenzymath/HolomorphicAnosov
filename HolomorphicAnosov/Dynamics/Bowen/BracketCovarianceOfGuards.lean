import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData

namespace HolomorphicAnosov.Dynamics.Bowen

open Set

/-- Bowen's one-step bracket transport, with the source and receiving close-pair
conditions and the unstable time-zero guard explicit. Source: Bowen (1970),
Lemma 11(a), pp.730–731. Forward stable membership follows by shifting its orbit
inequalities; backward unstable membership shifts for positive times and uses
the supplied image-distance guard at time zero. Uniqueness identifies the bracket. -/
theorem bracket_covariance_of_guards
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ lam : ℝ) (H : CompactLocalProductData f γ lam)
    {x y : X} (hxy : dist x y ≤ H.closeRadius)
    (hfxfy : dist (f x) (f y) ≤ H.closeRadius)
    (himage : dist (f (H.bracket x y)) (f y) ≤ γ) :
    f (H.bracket x y) = H.bracket (f x) (f y) := by
  apply H.bracket_unique (f x) (f y) _ hfxfy
  have hb := H.bracket_mem x y hxy
  constructor
  · intro n
    simpa only [Function.iterate_succ_apply] using hb.1 (n + 1)
  · intro n
    cases n with
    | zero => exact himage
    | succ n =>
      simpa only [Function.iterate_succ_apply, Homeomorph.symm_apply_apply] using hb.2 n

end HolomorphicAnosov.Dynamics.Bowen
