import HolomorphicAnosov.Topology.BoundedPiDisplacementFixedPoint
import HolomorphicAnosov.Topology.TorusCoordinateCover

/-! Surjectivity of the bounded correction used by Franks (1970),
Proposition (2.1), pp.70–71, and the original-cover proof of Franks–Manning.
The fixed-point argument takes place in real coordinates and requires no
smooth structure on the coordinate homeomorphism. -/

namespace HolomorphicAnosov.Topology

/-- A torus-valued map is onto if it has a real lift at bounded distance from
surjective real coordinates. This includes the centered coordinates of the
original pullback cover.

Proof: For a prescribed real target y, the map v ↦ v − H(v) + y is bounded,
so the bounded-displacement fixed-point theorem (with linear part zero) gives
v − H(v) + y = v, hence H(v)=y. Given a torus target, choose a real
representative and then a preimage under H. The lifted projection equation
supplies its preimage downstairs. This works also in dimension zero.
Source: Franks, Anosov Diffeomorphisms (1970), Proposition (2.1), pp.70–71;
Dold (1965), pp.1–8, for the fixed-point laws used by the existing provider. -/
theorem surjective_of_bounded_real_lift
    {n : ℕ} {M : Type*} (p : (Fin n → ℝ) → M)
    (h : M → UnitAddTorus (Fin n))
    (H : C((Fin n → ℝ), (Fin n → ℝ)))
    (K : ℝ) (hK : 0 ≤ K) (hbound : ∀ v, ‖v - H v‖ ≤ K)
    (hlift : ∀ v, coordinateProjection n (H v) = h (p v)) :
    Function.Surjective h := by
  have hH : Function.Surjective H := by
    intro y
    let G : C((Fin n → ℝ), (Fin n → ℝ)) :=
      ⟨fun v ↦ v - H v + y, (continuous_id.sub H.continuous).add continuous_const⟩
    obtain ⟨v, hv⟩ := bounded_pi_displacement_fixed_point n G 0
      (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)) (by intro x; simp)
      (K + ‖y‖) (add_nonneg hK (norm_nonneg _)) (by
        intro v
        change ‖v - H v + y - 0‖ ≤ K + ‖y‖
        simpa only [sub_zero] using (norm_add_le (v - H v) y).trans
          (add_le_add (hbound v) le_rfl))
    refine ⟨v, ?_⟩
    change v - H v + y = v at hv
    have heq : y - H v = 0 := by
      calc
        y - H v = (v - H v + y) - v := by abel
        _ = 0 := by rw [hv]; exact sub_self _
    exact (sub_eq_zero.mp heq).symm
  intro z
  obtain ⟨y, hy⟩ := (coordinateProjection_cover n).toIsQuotientMap.surjective z
  obtain ⟨v, hv⟩ := hH y
  exact ⟨p v, (hlift v).symm.trans (by rw [hv]; exact hy)⟩

end HolomorphicAnosov.Topology
