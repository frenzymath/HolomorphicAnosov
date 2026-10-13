import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductData

namespace HolomorphicAnosov.Dynamics.Bowen
open Set

/-- Plaque-slice density at an ambient interior basepoint, as used in Bowen's
Lemma 24, p.739, from the rectangle product structure of Lemmas 8–9, pp.729–730.
The interior-bracket premise is supplied for small rectangles by
`exists_interior_bracket_radius`.

Approximate a point y of a closed stable slice by points z in the ambient
interior of R, then project them with [x,z]. Interior bracket closure keeps
these points in the ambient interior, and bracket membership puts them in the
stable slice at x. Bracket continuity on the guarded pair domain gives limit
[x,y]=y, the last equality following from uniqueness. For the unstable slice,
use [z,x] instead. This proves density in the ambient metric space; no equality
between ambient interiors and relative plaque interiors is assumed.
DAG: `dynamics.bowen_plaque_slice_interior_density_g17`. -/
theorem plaque_slice_interior_density
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ lam : ℝ) (H : CompactLocalProductData f γ lam)
    (R : Set X) (hreg : R = closure (interior R))
    (hcore : ∀ x ∈ R, ∀ y ∈ R, dist x y ≤ H.closeRadius)
    (hinterior : ∀ x ∈ interior R, ∀ y ∈ interior R,
      H.bracket x y ∈ interior R)
    (x : X) (hx : x ∈ interior R) :
    (R ∩ relativeClosedStablePlaque f γ x ⊆
      closure (interior R ∩ relativeClosedStablePlaque f γ x)) ∧
    (R ∩ relativeClosedUnstablePlaque f γ x ⊆
      closure (interior R ∩ relativeClosedUnstablePlaque f γ x)) := by
  constructor
  · intro y hy
    have hc : ContinuousOn (fun z ↦ H.bracket x z) (closure (interior R)) := by
      rw [← hreg]
      exact H.bracket_continuous.comp
        (continuous_const.prodMk continuous_id).continuousOn
        (fun z hz ↦ hcore x (interior_subset hx) z hz)
    have himage : (fun z ↦ H.bracket x z) '' interior R ⊆
        interior R ∩ relativeClosedStablePlaque f γ x := by
      rintro z ⟨p, hp, rfl⟩
      exact ⟨hinterior x hx p hp,
        (H.bracket_mem x p (hcore x (interior_subset hx) p (interior_subset hp))).1⟩
    have hxy : H.bracket x y = y := by
      symm
      apply H.bracket_unique x y y (hcore x (interior_subset hx) y hy.1)
      exact ⟨hy.2, fun n ↦ by simpa using H.gamma_pos.le⟩
    have hycl : y ∈ closure (interior R) := hreg ▸ hy.1
    simpa only [hxy] using closure_mono himage (hc.image_closure ⟨y, hycl, rfl⟩)
  · intro y hy
    have hc : ContinuousOn (fun z ↦ H.bracket z x) (closure (interior R)) := by
      rw [← hreg]
      exact H.bracket_continuous.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun z hz ↦ hcore z hz x (interior_subset hx))
    have himage : (fun z ↦ H.bracket z x) '' interior R ⊆
        interior R ∩ relativeClosedUnstablePlaque f γ x := by
      rintro z ⟨p, hp, rfl⟩
      exact ⟨hinterior p hp x hx,
        (H.bracket_mem p x (hcore p (interior_subset hp) x (interior_subset hx))).2⟩
    have hyx : H.bracket y x = y := by
      symm
      apply H.bracket_unique y x y (hcore y hy.1 x (interior_subset hx))
      exact ⟨fun n ↦ by simpa using H.gamma_pos.le, hy.2⟩
    have hycl : y ∈ closure (interior R) := hreg ▸ hy.1
    simpa only [hyx] using closure_mono himage (hc.image_closure ⟨y, hycl, rfl⟩)

end HolomorphicAnosov.Dynamics.Bowen
