import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
namespace HolomorphicAnosov
universe u
/-- Every element of a based fundamental group has an endpoint-fixed path
representative. Source: Hatcher, Algebraic Topology, §1.1 and Mathlib's
fundamental-group quotient API. -/
theorem cw_target_loop_representative_g6
    {Y : Type u} [TopologicalSpace Y] (y₀ : Y)
    (a : FundamentalGroup Y y₀) :
    ∃ γ : Path y₀ y₀,
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) = a := by
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective a
  exact ⟨γ, hγ⟩
end HolomorphicAnosov
