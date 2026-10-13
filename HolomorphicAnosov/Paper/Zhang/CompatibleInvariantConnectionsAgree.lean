import HolomorphicAnosov.Paper.Zhang.CompatibleDifferenceOnSubbundle
import HolomorphicAnosov.Paper.Zhang.InvariantConnectionsAgreeOfUnstable

open Set TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection








theorem compatible_invariant_connections_agree
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsCompactComplexManifold d X]
    (f : Biholomorph d d X X) (a : AnosovDatum f)
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)} {r : ℕ}
    (hUhol : IsHolomorphicTangentSubbundle r U)
    (hUreal : ∀ x, ((U x).restrictScalars ℝ).map
      (complexTangentToReal d x).toLinearEquiv.toLinearMap =
        a.splitting.unstable.toDistribution x)
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧ Nonempty (HolomorphicFrame U V))
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    (D D' : Connection U) (hc : IsContinuous D) (hc' : IsContinuous D')
    (hcomp : IsCompatible D) (hcomp' : IsCompatible D')
    (hi : IsInvariant D f hU) (hi' : IsInvariant D' f hU) : Agrees D' D := by
  apply invariant_connections_agree_of_unstable f a hcover hU D D' hc hc' hi hi'
  intro V e x hx v hv
  rw [← hUreal x] at hv
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  exact compatible_difference_on_subbundle hUhol D D' hcomp hcomp' V e x hx w hw

end HolomorphicAnosov
