import HolomorphicAnosov.Topology.Homology.SignedShuffleData
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! In the product of two topological standard simplices, the affine singular simplex defined by a pair of vertex maps uniquely determines that pair. There is an explicit rational linear coefficient extraction retraction on these affine generators. Consequently every finite rational chain identity among the paired affine operators remains true under any assignment of those operators to vectors. In particular the identity remains true after priming both vertex maps and evaluating on arbitrary singular simplices in any universe. Positive-index faces commute with priming, input faces compose the corresponding vertex map with deletion, and input initial degeneracies compose with merging.

Agent-written affine singular-chain realization of the formal operator model used by parent topo.rational_signed_shuffle_positive_boundary_g3. Eilenberg–Mac Lane (1953), §2 model K(r), p.58, Theorem3.1 and definition (3.3), p.59, and Theorem3.2 equation (3.5), p.60, work in formally free monotone-map complexes. They do not provide the total vertex decoder and rational linear retraction for arbitrary paired affine singular simplices proved here. -/


noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

namespace HolomorphicAnosov.SignedShuffle.OperatorModel

/-- The product of two topological standard simplices is our singular-chain
realization of the paired formal operator model. EM1953 §3 uses a formally free
monotone-map model; the affine coefficient retraction here is an agent-written bridge. -/
abbrev Space (p q : ℕ) : TopCat :=
  TopCat.of (Convexity.StdSimplex ℝ (Fin (p + 1)) ×
    Convexity.StdSimplex ℝ (Fin (q + 1)))

/-- The universal affine simplex for a pair of vertex maps. All vertex maps are
allowed here; the shuffle terms are the monotone special cases. -/
def simplex {p q n : ℕ} (a : Fin (n + 1) → Fin (p + 1))
    (b : Fin (n + 1) → Fin (q + 1)) : Simplex (Space p q) n :=
  (TopCat.toSSetObjEquiv (Space p q) (Opposite.op ⦋n⦌)).symm
    ((⟨Convexity.StdSimplex.map a, Convexity.StdSimplex.continuous_map ℝ a⟩ :
      C(Convexity.StdSimplex ℝ (Fin (n + 1)), Convexity.StdSimplex ℝ (Fin (p + 1)))).prodMk
      ⟨Convexity.StdSimplex.map b, Convexity.StdSimplex.continuous_map ℝ b⟩)

/-- Decode a standard vertex. The fallback makes this a total function on the
whole simplex; only its value on standard vertices matters for the free model. -/
def vertexIndex {n : ℕ} (x : Convexity.StdSimplex ℝ (Fin (n + 1))) : Fin (n + 1) := by
  classical
  exact if h : ∃ i, Convexity.StdSimplex.single i = x then h.choose else 0

/-- The standard vertices have their exact original indices under decoding. -/
theorem vertexIndex_single {n : ℕ} (i : Fin (n + 1)) :
    vertexIndex (Convexity.StdSimplex.single (R := ℝ) i) = i := by
  unfold vertexIndex
  rw [dite_eq_left ⟨i, rfl⟩]
  have h : ∃ j, Convexity.StdSimplex.single (R := ℝ) j =
      Convexity.StdSimplex.single i := ⟨i, rfl⟩
  exact Convexity.StdSimplex.single_injective h.choose_spec

/-- Read the two vertex maps of a singular simplex in the universal model. -/
def decode {p q n : ℕ} (s : Simplex (Space p q) n) :
    (Fin (n + 1) → Fin (p + 1)) × (Fin (n + 1) → Fin (q + 1)) :=
  (fun i ↦ vertexIndex ((TopCat.toSSetObjEquiv (Space p q) (Opposite.op ⦋n⦌) s)
      (Convexity.StdSimplex.single i)).1,
   fun i ↦ vertexIndex ((TopCat.toSSetObjEquiv (Space p q) (Opposite.op ⦋n⦌) s)
      (Convexity.StdSimplex.single i)).2)

/-- Evaluation at standard vertices recovers each universal affine operator.
This supplies the explicit retraction required for coefficient-wise transport,
rather than assuming that equal singular chains have equal affine coefficients. -/
theorem decode_simplex {p q n : ℕ} (a : Fin (n + 1) → Fin (p + 1))
    (b : Fin (n + 1) → Fin (q + 1)) : decode (simplex a b) = (a, b) := by
  apply Prod.ext <;> funext i <;>
    simp [decode, simplex, Convexity.StdSimplex.map_single, vertexIndex_single]

/-- Distinct paired affine vertex operators give distinct universal singular simplices. -/
theorem simplex_injective (p q n : ℕ) :
    Function.Injective (fun ab : (Fin (n + 1) → Fin (p + 1)) ×
      (Fin (n + 1) → Fin (q + 1)) ↦ simplex ab.1 ab.2) := by
  intro ab cd h
  have hh := congrArg decode h
  simpa only [decode_simplex] using hh

/-- Deleting a vertex precomposes both vertex maps with the same deletion map. -/
theorem simplex_face {p q n : ℕ} (a : Fin (n + 2) → Fin (p + 1))
    (b : Fin (n + 2) → Fin (q + 1)) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (Space p q)).δ i (simplex a b) =
      simplex (a ∘ i.succAbove) (b ∘ i.succAbove) := by
  apply (TopCat.toSSetObjEquiv (Space p q) (Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  change (Convexity.StdSimplex.map a (Convexity.StdSimplex.map i.succAbove z),
    Convexity.StdSimplex.map b (Convexity.StdSimplex.map i.succAbove z)) = _
  simp only [← Convexity.StdSimplex.map_comp]
  rfl

/-- Paired vertex maps index the free affine operators in a fixed tridegree. -/
abbrev Operators (p q n : ℕ) :=
  (Fin (n + 1) → Fin (p + 1)) × (Fin (n + 1) → Fin (q + 1))

/-- Extract the free paired-operator coefficients by a linear extension of the
vertex decoder. Its values on nonaffine simplices are irrelevant to its retraction law. -/
def coefficients (p q n : ℕ) : Chain (Space p q) n →ₗ[ℚ] (Operators p q n →₀ ℚ) :=
  (Sigma.desc fun s : Simplex (Space p q) n ↦ ModuleCat.ofHom
    (((LinearMap.ringLmapEquivSelf ℚ ℕ _).symm
      (Finsupp.single (decode s) (1 : ℚ))).comp
        (ULift.moduleEquiv : ULift ℚ ≃ₗ[ℚ] ℚ).toLinearMap)).hom

/-- An affine model generator decodes to its own free coefficient basis vector. -/
theorem coefficients_generator (p q n : ℕ) (ab : Operators p q n) :
    coefficients p q n (generator (Space p q) (simplex ab.1 ab.2)) =
      Finsupp.single ab (1 : ℚ) := by
  simp [coefficients, generator, SSet.ιChainComplex, decode_simplex]

/-- Coefficient extraction on explicitly supplied paired coordinate functions. -/
theorem coefficients_simplex {p q n : ℕ} (a : Fin (n + 1) → Fin (p + 1))
    (b : Fin (n + 1) → Fin (q + 1)) :
    coefficients p q n (generator (Space p q) (simplex a b)) =
      Finsupp.single (a, b) (1 : ℚ) := coefficients_generator p q n (a, b)

/-- A universal affine identity remains valid under any assignment of paired
vertex operators to vectors. Agent-written singular-chain realization of the formal
model argument of EM1953 Theorem3.1, p.59, and Theorem3.2 equation (3.5), p.60.
Apply coefficient extraction and then the chosen free linear extension. This
explicit argument justifies priming coefficient identities without an axiom
about formal natural operators. -/
theorem identity_transfer {p q n : ℕ} {I J : Type*} (s : Finset I) (t : Finset J)
    (a : I → Operators p q n) (b : J → Operators p q n)
    (r : I → ℚ) (v : J → ℚ)
    (h : ∑ i ∈ s, r i • generator (Space p q) (simplex (a i).1 (a i).2) =
      ∑ j ∈ t, v j • generator (Space p q) (simplex (b j).1 (b j).2))
    {M : Type*} [AddCommGroup M] [Module ℚ M] (f : Operators p q n → M) :
    ∑ i ∈ s, r i • f (a i) = ∑ j ∈ t, v j • f (b j) := by
  have hh := congrArg ((Finsupp.linearCombination ℚ f).comp (coefficients p q n)) h
  simpa only [LinearMap.comp_apply, map_sum, map_smul, coefficients_generator,
    Finsupp.linearCombination_single, one_smul] using hh

universe u

/-- Evaluate a paired vertex operator on two arbitrary singular input simplices. -/
def evaluate (X Y : TopCat.{u}) {p q n : ℕ} (ab : Operators p q n)
    (σ : Simplex X p) (τ : Simplex Y q) : Simplex (TopCat.of (X × Y)) n :=
  (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋n⦌)).symm
    (((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ).comp
      ⟨Convexity.StdSimplex.map ab.1, Convexity.StdSimplex.continuous_map ℝ ab.1⟩).prodMk
     ((TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ).comp
      ⟨Convexity.StdSimplex.map ab.2, Convexity.StdSimplex.continuous_map ℝ ab.2⟩))

/-- Evaluate the paired coordinate maps of a grid path to recover exactly the
prescribed product simplex, without requiring that the path be a staircase. -/
theorem evaluate_gridPath (X Y : TopCat.{u}) {p q : ℕ}
    (w : SignedSingularCrossProduct.GridPath p q) (σ : Simplex X p) (τ : Simplex Y q) :
    evaluate X Y (fun i ↦ (w i).1, fun i ↦ (w i).2) σ τ =
      SignedSingularCrossProduct.productSimplex X Y w σ τ := rfl

/-- Prime both vertex maps by fixing a new initial vertex and shifting all other
vertices. Source: EM1953 §3, pp.58–60. -/
def prime {p q n : ℕ} (ab : Operators p q n) : Operators (p + 1) (q + 1) (n + 1) :=
  (Fin.cases 0 (fun i ↦ (ab.1 i).succ), Fin.cases 0 (fun i ↦ (ab.2 i).succ))

/-- Deleting a positive-index vertex after priming is the prime of the old deletion. -/
theorem prime_delete {p q n : ℕ} (ab : Operators p q (n + 1)) (i : Fin (n + 2)) :
    ((prime ab).1 ∘ i.succ.succAbove, (prime ab).2 ∘ i.succ.succAbove) =
      prime (ab.1 ∘ i.succAbove, ab.2 ∘ i.succAbove) := by
  apply Prod.ext <;> funext k <;> cases k using Fin.cases <;>
    simp [prime]

/-- Native faces precompose the paired vertex maps. -/
theorem evaluate_face (X Y : TopCat.{u}) {p q n : ℕ} (ab : Operators p q (n + 1))
    (σ : Simplex X p) (τ : Simplex Y q) (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ i (evaluate X Y ab σ τ) =
      evaluate X Y (ab.1 ∘ i.succAbove, ab.2 ∘ i.succAbove) σ τ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
      (Convexity.StdSimplex.map ab.1 (Convexity.StdSimplex.map i.succAbove z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)
      (Convexity.StdSimplex.map ab.2 (Convexity.StdSimplex.map i.succAbove z))) = _
  simp only [← Convexity.StdSimplex.map_comp]
  rfl

/-- A primed affine operator commutes with positive-index faces. This is the
pointwise operator identity needed to derive a boundary equation. -/
theorem evaluate_prime_face (X Y : TopCat.{u}) {p q n : ℕ}
    (ab : Operators p q (n + 1)) (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1))
    (i : Fin (n + 2)) :
    (TopCat.toSSet.obj (TopCat.of (X × Y))).δ i.succ (evaluate X Y (prime ab) σ τ) =
      evaluate X Y (prime (ab.1 ∘ i.succAbove, ab.2 ∘ i.succAbove)) σ τ := by
  rw [evaluate_face, prime_delete]

/-- In the product of two topological standard simplices, the affine singular simplex defined by a pair of vertex maps uniquely determines that pair. There is an explicit rational linear coefficient extraction retraction on these affine generators. Consequently every finite rational chain identity among the paired affine operators remains true under any assignment of those operators to vectors. In particular the identity remains true after priming both vertex maps and evaluating on arbitrary singular simplices in any universe. Positive-index faces commute with priming, input faces compose the corresponding vertex map with deletion, and input initial degeneracies compose with merging.

Source and proof origin: Agent-written affine singular-chain realization of the formal operator model used by parent topo.rational_signed_shuffle_positive_boundary_g3. Eilenberg–Mac Lane (1953), §2 model K(r), p.58, Theorem3.1 and definition (3.3), p.59, and Theorem3.2 equation (3.5), p.60, work in formally free monotone-map complexes. They do not provide the total vertex decoder and rational linear retraction for arbitrary paired affine singular simplices proved here.

Proof: Evaluate each affine singular simplex at every standard vertex. Each output coordinate is the standard vertex indexed by the corresponding input vertex map, by map_single. Decode standard vertices using their injectivity; a default index on all other points makes the decoder total. Extend this decoder rational-linearly from the native singular generator coproduct into the free module on paired vertex maps. On every affine generator it is exactly its basis coefficient, so this is an explicit retraction.

For a finite chain identity apply the coefficient retraction and then the free linear combination map attached to an arbitrary assignment. Both maps preserve finite sums and rational scalar multiples, giving the transferred identity. For the derived identity assign each pair to the generator obtained by adjoining a new fixed initial vertex, shifting both old target maps up, and evaluating on the two new singular inputs.

Precomposition of affine maps composes their vertex maps. The finite-ordinal relation that deleting vertex i+1 after adjoining a new initial vertex equals adjoining that vertex after deleting i proves positive-face compatibility. The same affine composition rule gives both input-face and initial-degeneracy formulas. Degree transport merely reindexes the source vertices by the equality cast. -/
theorem derived_identity_transfer {p q n : ℕ} {I J : Type*} (s : Finset I) (t : Finset J)
    (a : I → Operators p q n) (b : J → Operators p q n)
    (r : I → ℚ) (v : J → ℚ)
    (h : ∑ i ∈ s, r i • generator (Space p q) (simplex (a i).1 (a i).2) =
      ∑ j ∈ t, v j • generator (Space p q) (simplex (b j).1 (b j).2))
    (X Y : TopCat.{u}) (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    ∑ i ∈ s, r i • generator (TopCat.of (X × Y)) (evaluate X Y (prime (a i)) σ τ) =
      ∑ j ∈ t, v j • generator (TopCat.of (X × Y)) (evaluate X Y (prime (b j)) σ τ) :=
  identity_transfer s t a b r v h
    (fun ab ↦ generator (TopCat.of (X × Y)) (evaluate X Y (prime ab) σ τ))

/-- Evaluating an input face composes the corresponding vertex map with its
vertex-deletion map. Source: EM1953 §2, pp.56–58. -/
theorem evaluate_face_left (X Y : TopCat.{u}) {p q n : ℕ} (ab : Operators p q n)
    (σ : Simplex X (p + 1)) (τ : Simplex Y q) (i : Fin (p + 2)) :
    evaluate X Y ab ((TopCat.toSSet.obj X).δ i σ) τ =
      evaluate X Y (i.succAbove ∘ ab.1, ab.2) σ τ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p + 1⦌) σ)
      (Convexity.StdSimplex.map i.succAbove (Convexity.StdSimplex.map ab.1 z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)
      (Convexity.StdSimplex.map ab.2 z)) = _
  simp only [← Convexity.StdSimplex.map_comp]
  rfl

/-- The second input face composes the second vertex map with deletion. -/
theorem evaluate_face_right (X Y : TopCat.{u}) {p q n : ℕ} (ab : Operators p q n)
    (σ : Simplex X p) (τ : Simplex Y (q + 1)) (i : Fin (q + 2)) :
    evaluate X Y ab σ ((TopCat.toSSet.obj Y).δ i τ) =
      evaluate X Y (ab.1, i.succAbove ∘ ab.2) σ τ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
      (Convexity.StdSimplex.map ab.1 z),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q + 1⦌) τ)
      (Convexity.StdSimplex.map i.succAbove (Convexity.StdSimplex.map ab.2 z))) = _
  simp only [← Convexity.StdSimplex.map_comp]
  rfl

/-- Evaluating an initial input degeneracy composes the corresponding vertex map
with the initial vertex-merging map. Source: EM1953 §2, pp.56–58. -/
theorem evaluate_degeneracyZero_left (X Y : TopCat.{u}) {p q n : ℕ}
    (ab : Operators (p + 1) q n) (σ : Simplex X p) (τ : Simplex Y q) :
    evaluate X Y ab ((TopCat.toSSet.obj X).σ 0 σ) τ =
      evaluate X Y ((0 : Fin (p + 1)).predAbove ∘ ab.1, ab.2) σ τ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
      (Convexity.StdSimplex.map (0 : Fin (p + 1)).predAbove
        (Convexity.StdSimplex.map ab.1 z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)
      (Convexity.StdSimplex.map ab.2 z)) = _
  simp only [← Convexity.StdSimplex.map_comp]
  rfl

/-- The second input initial degeneracy composes its vertex map with merging. -/
theorem evaluate_degeneracyZero_right (X Y : TopCat.{u}) {p q n : ℕ}
    (ab : Operators p (q + 1) n) (σ : Simplex X p) (τ : Simplex Y q) :
    evaluate X Y ab σ ((TopCat.toSSet.obj Y).σ 0 τ) =
      evaluate X Y (ab.1, (0 : Fin (q + 1)).predAbove ∘ ab.2) σ τ := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × Y)) (Opposite.op ⦋n⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
      (Convexity.StdSimplex.map ab.1 z),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)
      (Convexity.StdSimplex.map (0 : Fin (q + 1)).predAbove
        (Convexity.StdSimplex.map ab.2 z))) = _
  simp only [← Convexity.StdSimplex.map_comp]
  rfl

/-- Degree transport of an evaluated operator simply reindexes its source vertices. -/
theorem regrade_evaluate_generator (X Y : TopCat.{u}) {p q n m : ℕ}
    (h : n = m) (ab : Operators p q n) (σ : Simplex X p) (τ : Simplex Y q) :
    regrade (TopCat.of (X × Y)) h (generator (TopCat.of (X × Y)) (evaluate X Y ab σ τ)) =
      generator (TopCat.of (X × Y))
        (evaluate X Y (ab.1 ∘ Fin.cast (congrArg (· + 1) h.symm),
          ab.2 ∘ Fin.cast (congrArg (· + 1) h.symm)) σ τ) := by
  subst m
  rfl
end HolomorphicAnosov.SignedShuffle.OperatorModel
