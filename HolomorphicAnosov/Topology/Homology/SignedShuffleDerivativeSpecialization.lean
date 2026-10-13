import HolomorphicAnosov.Topology.Homology.SignedShuffleBasic
import HolomorphicAnosov.Topology.Homology.SignedShuffleDerivedRecursion
import HolomorphicAnosov.Topology.Homology.SignedShuffleDerivedBoundaryTransport
import HolomorphicAnosov.Topology.Homology.SignedShuffleData
import HolomorphicAnosov.Topology.Homology.SignedShuffleOperatorModel
import HolomorphicAnosov.Topology.Homology.SignedShuffleBoundaryGenerator

/-! If the full native shuffle boundary identity holds on the universal identity inputs in bidegree (p+1,q+1), then the positive boundary of the derived shuffle of arbitrary inputs in degrees (p+2,q+2) equals the signed sum of their positive input faces, with sign (−1)^(p+1) on the second term and the exact output degree transports.

Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 Theorem3.2 equation (3.5), p.60; §5 derived boundary law (5.8′), p.66, and its use in the induction, p.67; the singular affine realization is supplied by the separately attributed operator-model dependency. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct
namespace HolomorphicAnosov.SignedShuffle
universe u
open SignedSingularCrossProduct OperatorModel

/-- A standard simplex as a topological test space for universal affine operators. -/
abbrev ModelSpace (p : ℕ) : TopCat := TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1)))

/-- The universal singular simplex specified by a vertex map. -/
def modelInput {p r : ℕ} (a : Fin (r + 1) → Fin (p + 1)) : Simplex (ModelSpace p) r :=
  (TopCat.toSSetObjEquiv (ModelSpace p) (Opposite.op ⦋r⦌)).symm
    ⟨Convexity.StdSimplex.map a, Convexity.StdSimplex.continuous_map ℝ a⟩

/-- Compose a singular input with an affine vertex map. -/
def evaluateInput (X : TopCat.{u}) {p r : ℕ} (a : Fin (r + 1) → Fin (p + 1))
    (σ : Simplex X p) : Simplex X r :=
  (TopCat.toSSetObjEquiv X (Opposite.op ⦋r⦌)).symm
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ).comp
      ⟨Convexity.StdSimplex.map a, Convexity.StdSimplex.continuous_map ℝ a⟩)

/-- Prime one affine vertex map. -/
def primeInput {p r : ℕ} (a : Fin (r + 1) → Fin (p + 1)) :
    Fin (r + 2) → Fin (p + 2) := Fin.cases 0 (fun i ↦ (a i).succ)

/-- Priming preserves composition of arbitrary affine vertex maps. -/
theorem primeInput_comp {p r s : ℕ} (a : Fin (r + 1) → Fin (p + 1))
    (b : Fin (s + 1) → Fin (r + 1)) :
    primeInput (a ∘ b) = primeInput a ∘ primeInput b := by
  funext i
  cases i using Fin.cases <;> rfl

/-- The linear derivation operator on universal affine model chains. -/
def deriveChain (X Y : TopCat.{u}) (p q n : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    Chain (Space p q) n →ₗ[ℚ] Chain (TopCat.of (X × Y)) (n + 1) :=
  (Finsupp.linearCombination ℚ
    (fun ab ↦ generator (TopCat.of (X × Y)) (evaluate X Y (prime ab) σ τ))).comp
      (coefficients p q n)

/-- Derivation of an affine generator is the generator of the primed operator. -/
theorem deriveChain_simplex (X Y : TopCat.{u}) {p q n : ℕ}
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1))
    (a : Fin (n + 1) → Fin (p + 1)) (b : Fin (n + 1) → Fin (q + 1)) :
    deriveChain X Y p q n σ τ (generator (Space p q) (simplex a b)) =
      generator (TopCat.of (X × Y)) (evaluate X Y (prime (a,b)) σ τ) := by
  simp [deriveChain, coefficients_simplex]

/-- Derivation commutes with canonical transport of the output degree. -/
theorem deriveChain_regrade (X Y : TopCat.{u}) {p q n m : ℕ} (h : n = m)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) (c : Chain (Space p q) n) :
    deriveChain X Y p q m σ τ (regrade (Space p q) h c) =
      regrade (TopCat.of (X × Y)) (congrArg (· + 1) h) (deriveChain X Y p q n σ τ c) := by
  subst m
  rfl

/-- The product of universal affine inputs is the paired composite operator. -/
theorem product_modelInput {p q r s : ℕ} (w : GridPath r s)
    (a : Fin (r + 1) → Fin (p + 1)) (b : Fin (s + 1) → Fin (q + 1)) :
    productSimplex (ModelSpace p) (ModelSpace q) w (modelInput a) (modelInput b) =
      simplex (a ∘ fun k ↦ (w k).1) (b ∘ fun k ↦ (w k).2) := by
  apply (TopCat.toSSetObjEquiv (Space p q) (Opposite.op ⦋r + s⦌)).injective
  apply ContinuousMap.ext
  intro z
  change (Convexity.StdSimplex.map a (Convexity.StdSimplex.map (fun k ↦ (w k).1) z),
    Convexity.StdSimplex.map b (Convexity.StdSimplex.map (fun k ↦ (w k).2) z)) = _
  simp only [← Convexity.StdSimplex.map_comp]
  rfl

/-- Evaluation of paired operators commutes with affine changes in either input. -/
theorem evaluate_inputs (X Y : TopCat.{u}) {p q r s n : ℕ}
    (ab : Operators r s n) (a : Fin (r + 1) → Fin (p + 1))
    (b : Fin (s + 1) → Fin (q + 1)) (σ : Simplex X p) (τ : Simplex Y q) :
    evaluate X Y ab (evaluateInput X a σ) (evaluateInput Y b τ) =
      evaluate X Y (a ∘ ab.1, b ∘ ab.2) σ τ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
      (Convexity.StdSimplex.map a (Convexity.StdSimplex.map ab.1 z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)
      (Convexity.StdSimplex.map b (Convexity.StdSimplex.map ab.2 z))) = _
  simp only [← Convexity.StdSimplex.map_comp]
  rfl

/-- Applying derivation to a shuffle of universal affine inputs gives precisely
the derived shuffle of the correspondingly primed input operators. -/
theorem deriveChain_shuffle_modelInput (X Y : TopCat.{u}) {p q r s : ℕ}
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1))
    (a : Fin (r + 1) → Fin (p + 1)) (b : Fin (s + 1) → Fin (q + 1)) :
    deriveChain X Y p q (r + s) σ τ
      (shuffleGenerator (ModelSpace p) (ModelSpace q) (modelInput a) (modelInput b)) =
      derivedShuffleGenerator X Y
        (evaluateInput X (primeInput a) σ) (evaluateInput Y (primeInput b) τ) := by
  classical
  unfold shuffleGenerator derivedShuffleGenerator
  simp only [map_sum, map_smul, product_modelInput, deriveChain_simplex, evaluate_inputs]
  apply Finset.sum_congr rfl
  intro w hw
  congr 3
  change (primeInput (a ∘ fun k ↦ (w k).1), primeInput (b ∘ fun k ↦ (w k).2)) = _
  rw [primeInput_comp, primeInput_comp]
  rfl

/-- The identity affine input is unchanged by priming and evaluation. -/
theorem evaluateInput_prime_id (X : TopCat.{u}) {p : ℕ} (σ : Simplex X (p + 1)) :
    evaluateInput X (primeInput (id : Fin (p + 1) → Fin (p + 1))) σ = σ := by
  apply (TopCat.toSSetObjEquiv X (Opposite.op ⦋p + 1⦌)).injective
  apply ContinuousMap.ext
  intro z
  change (TopCat.toSSetObjEquiv X (Opposite.op ⦋p + 1⦌) σ)
    (Convexity.StdSimplex.map (primeInput id) z) = _
  have hi : primeInput (id : Fin (p + 1) → Fin (p + 1)) = id := by
    funext i
    cases i using Fin.cases <;> rfl
  rw [hi, Convexity.StdSimplex.map_id]

/-- A face of the universal identity input is its affine vertex-deletion map. -/
theorem modelInput_identity_face (p : ℕ) (i : Fin (p + 2)) :
    (TopCat.toSSet.obj (ModelSpace (p + 1))).δ i (modelInput id) =
      modelInput i.succAbove := by
  apply (TopCat.toSSetObjEquiv (ModelSpace (p + 1)) (Opposite.op ⦋p⦌)).injective
  apply ContinuousMap.ext
  intro z
  change Convexity.StdSimplex.map id (Convexity.StdSimplex.map i.succAbove z) = _
  rw [Convexity.StdSimplex.map_id]
  rfl

/-- A derived input face has the original face index raised by one. -/
theorem evaluateInput_prime_face (X : TopCat.{u}) {p : ℕ}
    (σ : Simplex X (p + 2)) (i : Fin (p + 2)) :
    evaluateInput X (primeInput i.succAbove) σ = (TopCat.toSSet.obj X).δ i.succ σ := by
  apply (TopCat.toSSetObjEquiv X (Opposite.op ⦋p + 1⦌)).injective
  apply ContinuousMap.ext
  intro z
  change (TopCat.toSSetObjEquiv X (Opposite.op ⦋p + 2⦌) σ)
    (Convexity.StdSimplex.map (primeInput i.succAbove) z) =
      (TopCat.toSSetObjEquiv X (Opposite.op ⦋p + 2⦌) σ)
        (Convexity.StdSimplex.map i.succ.succAbove z)
  congr 2
  funext k
  cases k using Fin.cases <;> simp [primeInput]

/-- The boundary of the universal shuffle transfers to the positive boundary
of the exact derived shuffle in arbitrary spaces. -/
theorem deriveChain_boundary_shuffle (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 2)) (τ : Simplex Y (q + 2)) :
    deriveChain X Y (p + 1) (q + 1) (p + 1 + q) σ τ
      (boundary (Space (p + 1) (q + 1)) (p + 1 + (q + 1))
        (shuffleGenerator (ModelSpace (p + 1)) (ModelSpace (q + 1))
          (modelInput id) (modelInput id))) =
      positiveBoundary (TopCat.of (X × Y)) (p + 1 + (q + 1))
        (derivedShuffleGenerator X Y σ τ) := by
  classical
  unfold shuffleGenerator derivedShuffleGenerator
  simp only [map_sum, map_smul, product_modelInput, positiveBoundary_generator,
    Function.id_comp]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  change deriveChain X Y (p + 1) (q + 1) (p + 1 + q) σ τ
    (boundary (Space (p + 1) (q + 1)) (p + 1 + q + 1)
      (generator (Space (p + 1) (q + 1))
        (simplex (fun k ↦ (w k).1) (fun k ↦ (w k).2)))) = _
  rw [boundary_generator_succ (Space (p + 1) (q + 1)) (p + 1 + q)]
  simp only [map_sum, map_zsmul, simplex_face, deriveChain_simplex, evaluate_prime_face]
  rfl

/-- Evaluation of the bilinear shuffle on two native generators. -/
theorem shuffleBilinear_generators (X Y : TopCat.{u}) {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) :
    shuffleBilinear X Y p q (generator X σ) (generator Y τ) = shuffleGenerator X Y σ τ := by
  simpa only [shuffle, TensorProduct.lift.tmul] using shuffle_tmul_generator X Y p q σ τ

/-- If the full native shuffle boundary identity holds on the universal identity inputs in bidegree (p+1,q+1), then the positive boundary of the derived shuffle of arbitrary inputs in degrees (p+2,q+2) equals the signed sum of their positive input faces, with sign (−1)^(p+1) on the second term and the exact output degree transports.

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 Theorem3.2 equation (3.5), p.60; §5 derived boundary law (5.8′), p.66, and its use in the induction, p.67; the singular affine realization is supplied by the separately attributed operator-model dependency. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: Let the universal input spaces be the standard p- and q-simplices. Define derivation on their product chains by composing the affine coefficient retraction with the free linear map sending a paired vertex operator to its primed evaluation on the chosen new singular inputs. This map is rational-linear and commutes with equality transport of degrees.

Composition of affine input maps composes vertex maps. Priming preserves composition, so derivation of a universal shuffle after two affine input substitutions equals the derived shuffle after the two primed substitutions. Identity substitutions remain identities; vertex deletion at i primes to deletion at i+1.

Expand the universal shuffle boundary on generators and apply derivation. Face/prime compatibility identifies it with the positive boundary of the derived shuffle. Apply the same linear map to the assumed native Leibniz equality; expand both input boundary sums, evaluate the bilinear shuffle on each pair of generators and use the primed substitution identity. This gives the asserted shifted input faces, unchanged lower-degree Koszul sign, and canonical transports. This is EM (3.5) specialized to (5.8′). -/
theorem derivedShuffle_boundary_of_model_boundary (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 2)) (τ : Simplex Y (q + 2))
    (h : boundary (Space (p + 1) (q + 1)) (p + 1 + (q + 1))
      (shuffleGenerator (ModelSpace (p + 1)) (ModelSpace (q + 1))
        (modelInput id) (modelInput id)) =
      firstBoundaryTerm (ModelSpace (p + 1)) (ModelSpace (q + 1)) (p + 1) (q + 1)
        (generator _ (modelInput id)) (generator _ (modelInput id)) +
      (-1 : ℚ)^(p + 1) •
        secondBoundaryTerm (ModelSpace (p + 1)) (ModelSpace (q + 1)) (p + 1) (q + 1)
          (generator _ (modelInput id)) (generator _ (modelInput id))) :
    positiveBoundary (TopCat.of (X × Y)) (p + 1 + (q + 1))
      (derivedShuffleGenerator X Y σ τ) =
      regrade (TopCat.of (X × Y)) (by omega : p + (q + 1) + 1 = p + 1 + (q + 1))
        (∑ i : Fin (p + 2), (-1 : ℤ)^i.val •
          derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).δ i.succ σ) τ) +
      (-1 : ℚ)^(p + 1) •
        regrade (TopCat.of (X × Y)) (by omega : p + 1 + q + 1 = p + 1 + (q + 1))
          (∑ j : Fin (q + 2), (-1 : ℤ)^j.val •
            derivedShuffleGenerator X Y σ ((TopCat.toSSet.obj Y).δ j.succ τ)) := by
  have hh := congrArg (deriveChain X Y (p + 1) (q + 1) (p + 1 + q) σ τ) h
  rw [deriveChain_boundary_shuffle] at hh
  simp only [firstBoundaryTerm, secondBoundaryTerm, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, dite_false,
    boundary_generator_succ, map_sum, map_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, modelInput_identity_face,
    map_add, map_smul, deriveChain_regrade] at hh
  apply hh.trans
  simp only [map_sum, map_zsmul]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    congr 1
    congr 1
    change deriveChain X Y (p + 1) (q + 1) (p + (q + 1)) σ τ
      (shuffleBilinear (ModelSpace (p + 1)) (ModelSpace (q + 1)) p (q + 1)
        (generator _ (modelInput i.succAbove)) (generator _ (modelInput id))) = _
    rw [shuffleBilinear_generators, deriveChain_shuffle_modelInput,
      evaluateInput_prime_face, evaluateInput_prime_id]
  · congr 1
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    congr 1
    change deriveChain X Y (p + 1) (q + 1) (p + 1 + q) σ τ
      (shuffleBilinear (ModelSpace (p + 1)) (ModelSpace (q + 1)) (p + 1) q
        (generator _ (modelInput id)) (generator _ (modelInput j.succAbove))) = _
    rw [shuffleBilinear_generators, deriveChain_shuffle_modelInput,
      evaluateInput_prime_id, evaluateInput_prime_face]

end HolomorphicAnosov.SignedShuffle
