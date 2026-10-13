import HolomorphicAnosov.Topology.Homology.SignedShuffleBoundaryInduction
import HolomorphicAnosov.Topology.Homology.SignedShuffleData

/-! For arbitrary topological spaces X,Y, positive integers p,q, and singular simplices σ of degree p and τ of degree q, the boundary of the finite rational signed staircase sum is the shuffle of ∂[σ] with [τ] plus (−1)^p times the shuffle of [σ] with ∂[τ], with the canonical equality transports of the degree indices.

Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §5 Theorem5.2, equations (5.8), (5.11), (5.12), and their written recursion proof, pp.66–67; Hatcher Algebraic Topology §3.B pp.277–278 identifies the finite staircase convention. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF. -/


noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

namespace HolomorphicAnosov.SignedShuffle

universe u

/-- For arbitrary topological spaces X,Y, positive integers p,q, and singular simplices σ of degree p and τ of degree q, the boundary of the finite rational signed staircase sum is the shuffle of ∂[σ] with [τ] plus (−1)^p times the shuffle of [σ] with ∂[τ], with the canonical equality transports of the degree indices.

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §5 Theorem5.2, equations (5.8), (5.11), (5.12), and their written recursion proof, pp.66–67; Hatcher Algebraic Topology §3.B pp.277–278 identifies the finite staircase convention. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: For nonzero natural degrees p,q, write each as a successor. Apply the completed arbitrary-universe successor-degree boundary theorem, obtained from the exact EM recursion, derived-face transfer, explicit (1,1) case, degree-one edge laws, and strong induction on universal model input degrees. The output is definitionally the original boundary expression with its firstBoundaryTerm, secondBoundaryTerm, Koszul sign, and canonical index transports. -/
theorem shuffle_positive_boundary_generator (X Y : TopCat.{u})
    (p q : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (σ : Simplex X p) (τ : Simplex Y q) :
    boundary (TopCat.of (X × Y)) (p + q) (shuffleGenerator X Y σ τ) =
      firstBoundaryTerm X Y p q (generator X σ) (generator Y τ) +
        (-1 : ℚ) ^ p • secondBoundaryTerm X Y p q (generator X σ) (generator Y τ) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact shuffle_positive_boundary_generator_proved X Y p q σ τ

end HolomorphicAnosov.SignedShuffle
