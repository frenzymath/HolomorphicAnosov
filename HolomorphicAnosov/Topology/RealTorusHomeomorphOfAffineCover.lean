import HolomorphicAnosov.Topology.ClosedAsphericalAbelianTorus
import HolomorphicAnosov.Topology.HomotopyTorusRigidity
import Mathlib.Analysis.Complex.Basic

/-!
# Torus homeomorphism from a Euclidean affine cover

Source: Ghys, Holomorphic Anosov systems, proof of Theorem B, p.598;
Zhang, Proposition 2.9, p.10. The allowed rigidity premise applies
only after homotopy-torus recognition and in real dimension at least five.
DAG node: `topo.real_torus_homeomorph_of_affine_cover_g11`.
-/

namespace HolomorphicAnosov.Proposition29Cover
universe u
open scoped ContDiff Manifold

/-- Zhang Proposition 2.9, higher-dimensional recognition from the actual affine-cover
outputs (Ghys p.598). A faithful complex translation representation makes the original
fundamental group abelian and torsion-free. The supplied Euclidean homeomorphism makes
the actual covering space contractible. The existing aspherical recognition theorem
then supplies a genuine homotopy equivalence, to which precisely the allowed rigidity
premise applies. The Euclidean atlas is the one already selected on the original base;
neither the torus homeomorphism nor the cover homeomorphism is differentiated. -/
theorem real_torus_homeomorph_of_affine_cover
    {d : ℕ} (hd : 3 ≤ d) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 * d))) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * d))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [T2Space M] [SecondCountableTopology M]
    {E : Type*} [TopologicalSpace E]
    (p : E → M) (hp : IsCoveringMap p) (hsurj : Function.Surjective p) (e0 : E)
    (e : E ≃ₜ (Fin (2 * d) → ℝ))
    (tau : FundamentalGroup M (p e0) →* Multiplicative ℂ)
    (htau : Function.Injective tau) (HS : HomotopyTorusRigidity.{u}) :
    Nonempty (M ≃ₜ UnitAddTorus (Fin (2 * d))) := by
  have : ContractibleSpace E := e.contractibleSpace
  have hcomm : ∀ a b : FundamentalGroup M (p e0), a * b = b * a := by
    intro a b
    apply htau
    rw [map_mul, map_mul, mul_comm]
  have htorsion : ∀ a : FundamentalGroup M (p e0), ∀ k : ℕ,
      0 < k → a ^ k = 1 → a = 1 := by
    intro a k hk ha
    apply htau
    rw [map_one]
    apply (pow_eq_one_iff_left (Nat.ne_of_gt hk)).mp
    rw [← map_pow, ha, map_one]
  have hequiv := closed_aspherical_abelian_torus (2 * d) M p hp hsurj (p e0)
    hcomm htorsion
  have hclosed : ClosedSmoothRealManifold (2 * d) M := {}
  exact HS (2 * d) (by omega) M hclosed hequiv


end HolomorphicAnosov.Proposition29Cover

