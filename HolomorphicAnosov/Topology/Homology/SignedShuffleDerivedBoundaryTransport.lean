import HolomorphicAnosov.Topology.Homology.SignedShuffleData
import HolomorphicAnosov.Algebra.Homology.SimplicialDerivedFaces
import HolomorphicAnosov.Topology.Homology.SignedShuffleOperatorModel
import HolomorphicAnosov.Topology.Homology.SignedShuffleBoundaryGenerator

/-! For the actual rational singular chain modules, the full boundary is the initial face minus the alternating positive-face differential, and the initial degeneracy satisfies ∂*D₀=id−D₀∂* in positive input degree. If a finite chain of universal paired affine simplices has a specified finite affine boundary, then after priming every paired vertex operator and evaluating on arbitrary singular input simplices, the positive boundary of the resulting chain equals the similarly primed original boundary. The primed source degree is at least two.

Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 Theorem3.2 equation (3.5), derived boundary (3.4), pp.59–60, splitting (3.6) and degeneracy identity (3.11), p.60; implemented using the separately attributed agent-written singular affine coefficient bridge. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.SignedShuffle
universe u
abbrev simplicialChains (X : TopCat.{u}) : SimplicialObject (ModuleCat.{u} ℚ) :=
  (TopCat.toSSet.obj X) ⋙ (sigmaConst.obj (ModuleCat.of ℚ (ULift.{u} ℚ)))
def faceChain (X : TopCat.{u}) (n : ℕ) (i : Fin (n + 2)) : Chain X (n + 1) →ₗ[ℚ] Chain X n :=
  ((simplicialChains X).δ i).hom
theorem faceChain_generator (X : TopCat.{u}) (n : ℕ) (i : Fin (n + 2)) (σ : Simplex X (n + 1)) :
  faceChain X n i (generator X σ) = generator X ((TopCat.toSSet.obj X).δ i σ) := by
  simp [faceChain, simplicialChains, generator, SSet.ιChainComplex, SimplicialObject.δ, Sigma.map']

/-- The native positive-face differential F₁−F₂+⋯. -/
def positiveBoundary (X : TopCat.{u}) (n : ℕ) : Chain X (n + 1) →ₗ[ℚ] Chain X n :=
  (SimplicialDerivedFaces.positiveFaces (simplicialChains X) n).hom

/-- On a singular generator, the positive boundary is its signed positive-face sum. -/
theorem positiveBoundary_generator (X : TopCat.{u}) (n : ℕ) (σ : Simplex X (n + 1)) :
    positiveBoundary X n (generator X σ) =
      ∑ i : Fin (n + 1), (-1 : ℤ)^i.val •
        generator X ((TopCat.toSSet.obj X).δ i.succ σ) := by
  unfold positiveBoundary SimplicialDerivedFaces.positiveFaces
  simp only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul,
    LinearMap.smul_apply]
  change ∑ i : Fin (n + 1), (-1 : ℤ)^i.val • faceChain X n i.succ (generator X σ) = _
  simp only [faceChain_generator]

/-- The native full boundary splits into its initial and positive-face terms. -/
theorem boundary_eq_initial_sub_positive (X : TopCat.{u}) (n : ℕ) (c : Chain X (n + 1)) :
    boundary X (n + 1) c = faceChain X n 0 c - positiveBoundary X n c := by
  have h := congrArg (fun f ↦ f.hom c)
    (SimplicialDerivedFaces.boundary_eq_first_sub_positive (simplicialChains X) n)
  change ((AlgebraicTopology.AlternatingFaceMapComplex.obj (simplicialChains X)).d
    (n + 1) n).hom c = _
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  exact h

/-- The native initial degeneracy. -/
def degeneracyZeroChain (X : TopCat.{u}) (n : ℕ) : Chain X n →ₗ[ℚ] Chain X (n + 1) :=
  ((simplicialChains X).σ (0 : Fin (n + 1))).hom

/-- Initial degeneracy evaluated on a generator is the native degenerate simplex. -/
theorem degeneracyZeroChain_generator (X : TopCat.{u}) (n : ℕ) (σ : Simplex X n) :
    degeneracyZeroChain X n (generator X σ) =
      generator X ((TopCat.toSSet.obj X).σ 0 σ) := by
  simp [degeneracyZeroChain, simplicialChains, generator, SSet.ιChainComplex,
    SimplicialObject.σ, Sigma.map']

/-- EM (3.11) on the actual native rational chains. -/
theorem positiveBoundary_degeneracyZero (X : TopCat.{u}) (n : ℕ) (c : Chain X (n + 1)) :
    positiveBoundary X (n + 1) (degeneracyZeroChain X (n + 1) c) =
      c - degeneracyZeroChain X n (positiveBoundary X n c) := by
  have h := congrArg (fun f ↦ f.hom c)
    (SimplicialDerivedFaces.degeneracyZero_positiveFaces (simplicialChains X) n)
  exact h

/-- For the actual rational singular chain modules, the full boundary is the initial face minus the alternating positive-face differential, and the initial degeneracy satisfies ∂*D₀=id−D₀∂* in positive input degree. If a finite chain of universal paired affine simplices has a specified finite affine boundary, then after priming every paired vertex operator and evaluating on arbitrary singular input simplices, the positive boundary of the resulting chain equals the similarly primed original boundary. The primed source degree is at least two.

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 Theorem3.2 equation (3.5), derived boundary (3.4), pp.59–60, splitting (3.6) and degeneracy identity (3.11), p.60; implemented using the separately attributed agent-written singular affine coefficient bridge. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: Realize the native chain groups as the simplicial object obtained by composing the singular simplicial set with the rational coefficient coproduct functor. Its faces and degeneracies act on generators by the native simplicial faces and degeneracies, by the coproduct inclusion formula. Evaluate the abstract positive-face splitting and initial-degeneracy identity on arbitrary native chains. This yields the full boundary decomposition and ∂*D₀=id−D₀∂* with no change of chain model.

Expand the assumed finite universal boundary equality using the exact alternating generator boundary formula. Apply the explicit affine-operator coefficient retraction and then the free linear map sending each paired operator to its primed evaluation on the new singular inputs. Every face term transfers to its primed vertex-deletion operator. The proved prime/delete relation identifies this with the corresponding positive-index face of the primed input. The alternating signs remain unchanged because the derived differential is indexed starting at the first positive face. Finite-sum and scalar linearity now give the asserted transported equality. -/
theorem derived_boundary_transfer {p q n : ℕ} {I J : Type*} (s : Finset I) (t : Finset J)
    (a : I → OperatorModel.Operators p q (n + 1))
    (b : J → OperatorModel.Operators p q n) (r : I → ℚ) (v : J → ℚ)
    (h : boundary (OperatorModel.Space p q) (n + 1)
      (∑ i ∈ s, r i • generator (OperatorModel.Space p q)
        (OperatorModel.simplex (a i).1 (a i).2)) =
      ∑ j ∈ t, v j • generator (OperatorModel.Space p q)
        (OperatorModel.simplex (b j).1 (b j).2))
    (X Y : TopCat.{u}) (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    positiveBoundary (TopCat.of (X × Y)) (n + 1)
      (∑ i ∈ s, r i • generator (TopCat.of (X × Y))
        (OperatorModel.evaluate X Y (OperatorModel.prime (a i)) σ τ)) =
      ∑ j ∈ t, v j • generator (TopCat.of (X × Y))
        (OperatorModel.evaluate X Y (OperatorModel.prime (b j)) σ τ) := by
  let f : OperatorModel.Operators p q n → Chain (TopCat.of (X × Y)) (n + 1) :=
    fun ab ↦ generator (TopCat.of (X × Y))
      (OperatorModel.evaluate X Y (OperatorModel.prime ab) σ τ)
  have hh := congrArg ((Finsupp.linearCombination ℚ f).comp (OperatorModel.coefficients p q n)) h
  simp only [map_sum, map_smul, boundary_generator_succ, map_zsmul,
    OperatorModel.simplex_face, LinearMap.comp_apply, OperatorModel.coefficients_simplex,
    Finsupp.linearCombination_single, one_smul] at hh
  simpa only [map_sum, map_smul, positiveBoundary_generator, OperatorModel.evaluate_prime_face,
    f] using hh
end HolomorphicAnosov.SignedShuffle
