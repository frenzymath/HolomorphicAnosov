import HolomorphicAnosov.Dynamics.ProperRelativeMarkovPartitionG7

/-!
# Compact metric canonical-coordinate data

Source: Bowen, *Markov Partitions for Axiom A Diffeomorphisms* (1970),
closed orbit plaques and Fact 1 pp.726–727, small open plaque products in
Lemmas 7–8 pp.728–729. DAG: `dynamics.def_bowen_compact_local_product_data_g1`.
The original homeomorphism and inherited metric are fixed throughout. This
definition records given canonical-coordinate hypotheses; it asserts neither
their existence nor existence of a Markov partition. It allows the empty space.
-/

namespace HolomorphicAnosov.Dynamics.Bowen

open Set

/-- Given contracting canonical coordinates on a compact metric space.

The bracket is stable-first. Its total-function representation imposes no condition
outside the closed close-pair domain. The open factors carry the subspace topologies
of the full closed γ-plaques, and their product maps to an ambient open subset of X.
The product radius may depend on the center. This is qualitative local product
data, not a connectedness, manifold, differentiability, or transitivity assumption.
The two orbit plaques are the original public definitions from the definition-only
module `ProperRelativeMarkovPartitionG7`, including time zero and inverse iterates.
Source: Bowen (1970), Fact 1 pp.726–727 and Lemmas 7–8 pp.728–729.
-/
structure CompactLocalProductData {X : Type*} [MetricSpace X] [CompactSpace X]
    (f : X ≃ₜ X) (γ lam : ℝ) where
  gamma_pos : 0 < γ
  lambda_pos : 0 < lam
  lambda_lt_one : lam < 1
  stable_contraction : ∀ (x y z : X),
    y ∈ relativeClosedStablePlaque f γ x → z ∈ relativeClosedStablePlaque f γ x →
    ∀ n : ℕ, dist ((f : X → X)^[n] y) ((f : X → X)^[n] z) ≤ lam ^ n * dist y z
  unstable_contraction : ∀ (x y z : X),
    y ∈ relativeClosedUnstablePlaque f γ x → z ∈ relativeClosedUnstablePlaque f γ x →
    ∀ n : ℕ,
      dist ((f.symm : X → X)^[n] y) ((f.symm : X → X)^[n] z) ≤ lam ^ n * dist y z
  closeRadius : ℝ
  closeRadius_pos : 0 < closeRadius
  bracket : X → X → X
  bracket_mem : ∀ x y : X, dist x y ≤ closeRadius →
    bracket x y ∈ relativeClosedStablePlaque f γ x ∩ relativeClosedUnstablePlaque f γ y
  bracket_unique : ∀ x y z : X, dist x y ≤ closeRadius →
    z ∈ relativeClosedStablePlaque f γ x ∩ relativeClosedUnstablePlaque f γ y →
    z = bracket x y
  bracket_continuous : ContinuousOn (fun p : X × X ↦ bracket p.1 p.2)
    {p | dist p.1 p.2 ≤ closeRadius}
  product_chart : ∀ x : X, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ γ ∧ 2 * ρ ≤ closeRadius ∧
    ∀ U V : Set X,
      U ⊆ relativeClosedUnstablePlaque f ρ x →
      V ⊆ relativeClosedStablePlaque f ρ x →
      IsOpen {u : relativeClosedUnstablePlaque f γ x | (u : X) ∈ U} →
      IsOpen {v : relativeClosedStablePlaque f γ x | (v : X) ∈ V} →
      IsOpen (image2 bracket U V) ∧
        ∃ h :
            ({u : relativeClosedUnstablePlaque f γ x // (u : X) ∈ U} ×
              {v : relativeClosedStablePlaque f γ x // (v : X) ∈ V}) ≃ₜ
            {z : X // z ∈ image2 bracket U V},
          ∀ p, (h p : X) = bracket (p.1 : X) (p.2 : X)

end HolomorphicAnosov.Dynamics.Bowen
