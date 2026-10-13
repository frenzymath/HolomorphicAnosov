import HolomorphicAnosov.Topology.CairnsResidualStarRefinement

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar

/-- Affine chord parametrization is unchanged when the endpoint pair is
reversed: substitute the complementary parameter 1-t. This removes arbitrary
orientations when matching gap representatives. -/
theorem cairns_affine_chord_unordered_endpoints
    {X : Type*} (σ τ : X → ℂ) (f : ℂ → ℂ) (p q u v : X)
    (he : ({p,q} : Set X) = {u,v})
    (hf : ∀ t : I, f ((1-(t : ℝ)) • σ u + (t : ℝ) • σ v) =
      (1-(t : ℝ)) • τ u + (t : ℝ) • τ v) :
    ∀ t : I, f ((1-(t : ℝ)) • σ p + (t : ℝ) • σ q) =
      (1-(t : ℝ)) • τ p + (t : ℝ) • τ q := by
  rcases pair_eq_pair_iff.mp he with he | he
  · simpa only [he.1,he.2] using hf
  · intro t
    have hh := hf (unitInterval.symm t)
    simp only [unitInterval.coe_symm_eq,sub_sub_cancel] at hh
    rw [he.1,he.2]
    simpa only [he.1,he.2,unitInterval.coe_symm_eq,sub_sub_cancel,add_comm] using hh

end HolomorphicAnosov.Topology.Plane
