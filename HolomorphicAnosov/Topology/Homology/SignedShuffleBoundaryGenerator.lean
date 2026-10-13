import HolomorphicAnosov.Topology.Homology.SignedShuffleData

/-! For every topological space X and singular simplex σ of degree n+1, the boundary of its unit rational generator is the sum over all n+2 faces of the face generator multiplied by (−1) to its index.

Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §2 alternating boundary definition (2.6), p.57; native Mathlib SSet.ιChainComplex_d. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF. -/


noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct
namespace HolomorphicAnosov.SignedShuffle
universe u
set_option backward.isDefEq.respectTransparency false in
/-- For every topological space X and singular simplex σ of degree n+1, the boundary of its unit rational generator is the sum over all n+2 faces of the face generator multiplied by (−1) to its index.

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §2 alternating boundary definition (2.6), p.57; native Mathlib SSet.ιChainComplex_d. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: Evaluate the native inclusion-morphism differential formula at the unit rational coefficient. Evaluation commutes with the finite sum and integer scalar multiplication; each inclusion evaluated at one is the corresponding generator. The predecessor of n+1 is n. -/
theorem boundary_generator_succ (X : TopCat.{u}) (n : ℕ) (σ : Simplex X (n + 1)) :
    boundary X (n + 1) (generator X σ) =
      ∑ i : Fin (n + 2), (-1 : ℤ)^i.val • generator X ((TopCat.toSSet.obj X).δ i σ) := by
  change (((TopCat.toSSet.obj X).chainComplex
    (ModuleCat.of ℚ (ULift.{u} ℚ))).d (n + 1) n).hom (generator X σ) = _
  have hδ := congrArg (fun f => f.hom (ULift.up (1 : ℚ)))
    (SSet.ιChainComplex_d (TopCat.toSSet.obj X)
      (R := ModuleCat.of ℚ (ULift.{u} ℚ)) σ)
  simpa only [boundary, generator, Nat.add_sub_cancel, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul,
    LinearMap.smul_apply] using hδ

end HolomorphicAnosov.SignedShuffle
