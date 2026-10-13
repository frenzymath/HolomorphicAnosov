import Mathlib.Analysis.Complex.Circle

/-!
# Radial normalization away from an apex

This is the elementary analytic component used by Cairns' half-sector
construction.  It records continuity of normalization by distance from a fixed
apex on sets that avoid that apex; the geometric front construction remains in
`HolomorphicAnosov.Topology.HalfSectorConvexFront`.

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem*
(1951), §4(A), printed p.864 / supplied PDF p.6.  The continuity argument is
expanded with the exact Mathlib `ContinuousOn.div` theorem.
-/

namespace HolomorphicAnosov.Topology

open Set

/--
Radial normalization about `M` is continuous on every set that omits `M`.

The denominator is the norm of the translated point, viewed in `ℂ`; the
hypothesis supplies its nonvanishing on the domain.
-/
theorem continuousOn_radial_normalization
    (M : ℂ) (S : Set ℂ) (hM : ∀ Q ∈ S, Q ≠ M) :
    ContinuousOn (fun Q : ℂ ↦ (Q - M) / (‖Q - M‖ : ℂ)) S := by
  have hnum : ContinuousOn (fun Q : ℂ ↦ Q - M) S :=
    continuousOn_id.sub continuousOn_const
  have hden : ContinuousOn (fun Q : ℂ ↦ (‖Q - M‖ : ℂ)) S := by
    fun_prop
  apply hnum.div hden
  intro Q hQ
  exact_mod_cast (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hM Q hQ)))

end HolomorphicAnosov.Topology
