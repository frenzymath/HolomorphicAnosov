import HolomorphicAnosov.Topology.Homology.SignedShuffleInitialFace
import HolomorphicAnosov.Topology.Homology.SignedShuffleDerivativeSpecialization
import HolomorphicAnosov.Topology.Homology.SignedShuffleData
import HolomorphicAnosov.Topology.Homology.SignedShuffleDerivedBoundaryTransport

/-! The exact positive-face Leibniz law for the prescribed signed shuffle, together with its established initial-face formula, implies the original full native generator boundary identity in every positive bidegree. Initial degeneracy positive faces split into the input minus the degenerated positive-face sum after any additive evaluation.

Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 degeneracy identity (3.11), p.60; §5 statement that (5.8) follows from (5.11) and (5.12), p.66. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct
namespace HolomorphicAnosov.SignedShuffle
universe u

/-- Canonical degree transports compose. -/
theorem regrade_trans (X : TopCat.{u}) {n m k : ℕ} (h : n = m) (h' : m = k)
    (c : Chain X n) : regrade X h' (regrade X h c) = regrade X (h.trans h') c := by
  subst m
  subst k
  rfl

/-- The positive-face differential commutes with canonical degree transport. -/
theorem positiveBoundary_regrade (X : TopCat.{u}) {n m : ℕ} (h : n = m)
    (c : Chain X (n + 1)) :
    positiveBoundary X m (regrade X (congrArg (· + 1) h) c) =
      regrade X h (positiveBoundary X n c) := by
  subst m
  rfl

/-- Applying the first positive face to the initial degeneracy returns the input. -/
theorem positiveFace_degeneracyZero_first (X : TopCat.{u}) (n : ℕ) (σ : Simplex X n) :
    (TopCat.toSSet.obj X).δ (0 : Fin (n + 1)).succ
      ((TopCat.toSSet.obj X).σ 0 σ) = σ :=
  ConcreteCategory.congr_hom ((TopCat.toSSet.obj X).δ_comp_σ_succ (i := 0)) σ

/-- All subsequent positive faces commute past the initial degeneracy with their
index reduced by one. -/
theorem positiveFace_degeneracyZero_succ (X : TopCat.{u}) (n : ℕ)
    (σ : Simplex X (n + 1)) (i : Fin (n + 1)) :
    (TopCat.toSSet.obj X).δ i.succ.succ ((TopCat.toSSet.obj X).σ 0 σ) =
      (TopCat.toSSet.obj X).σ 0 ((TopCat.toSSet.obj X).δ i.succ σ) :=
  ConcreteCategory.congr_hom ((TopCat.toSSet.obj X).δ_comp_σ_of_gt
    (j := (0 : Fin (n + 1))) (i := i.succ) (by change 0 < i.val + 1; omega)) σ

/-- The signed positive faces of an initially degenerated input split into the
input itself minus the degenerated positive-face sum, after any evaluation.
Source: the finite face-by-face expansion of EM1953 (3.11). -/
theorem positiveFace_degeneracy_sum (X : TopCat.{u}) (n : ℕ) (σ : Simplex X (n + 1))
    {M : Type*} [AddCommGroup M] (f : Simplex X (n + 1) → M) :
    (∑ i : Fin (n + 2), (-1 : ℤ)^i.val •
      f ((TopCat.toSSet.obj X).δ i.succ ((TopCat.toSSet.obj X).σ 0 σ))) =
      f σ - ∑ i : Fin (n + 1), (-1 : ℤ)^i.val •
        f ((TopCat.toSSet.obj X).σ 0 ((TopCat.toSSet.obj X).δ i.succ σ)) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_smul, positiveFace_degeneracyZero_first,
    positiveFace_degeneracyZero_succ, Fin.val_succ, pow_succ, mul_neg, mul_one,
    neg_smul, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The coproduct initial-face map agrees with the explicit affine initial face. -/
theorem faceChain_zero_eq_initialFaceChain (X : TopCat.{u}) (n : ℕ) :
    faceChain X n 0 = initialFaceChain X rfl := by
  apply chain_linearMap_ext X (n + 1) (ModuleCat.of ℚ (Chain X n))
  intro σ
  rw [faceChain_generator, initialFaceChain_generator, initialFaceSimplex_eq_delta]

/-- The exact positive-face Leibniz law for the prescribed signed shuffle, together with its established initial-face formula, implies the original full native generator boundary identity in every positive bidegree. Initial degeneracy positive faces split into the input minus the degenerated positive-face sum after any additive evaluation.

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §3 degeneracy identity (3.11), p.60; §5 statement that (5.8) follows from (5.11) and (5.12), p.66. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: The first positive face of D₀ is the identity. For all subsequent positive faces use the simplicial relation F_(i+2)D₀=D₀F_(i+1). Split the finite sum at its initial term and expand (−1)^(i+1)=−(−1)^i. This gives the finite evaluated form of (3.11).

Equality transports compose and commute with the positive-boundary linear map, by equality elimination. The coproduct initial-face map agrees on every generator with the explicit affine initial-face map, hence the maps agree.

Write the full output boundary as F₀ minus the positive boundary. Substitute the proved initial-face shuffle formula and the assumed positive-face law. On both input boundaries make the same decomposition, expand the bilinear map over differences and finite sums, and use its generator formula. The resulting additive identity is exactly the original firstBoundaryTerm plus the Koszul-signed secondBoundaryTerm. -/
theorem shuffle_boundary_of_positive_faces (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1))
    (hp : positiveBoundary (TopCat.of (X × Y)) (p + 1 + q) (shuffleGenerator X Y (p := p + 1) (q := q + 1) σ τ) =
      regrade (TopCat.of (X × Y)) (by omega : p + (q + 1) = p + 1 + q)
        (∑ i : Fin (p + 1), (-1 : ℤ)^i.val •
          shuffleGenerator X Y ((TopCat.toSSet.obj X).δ i.succ σ) τ) +
      (-1 : ℚ)^(p + 1) •
        (∑ j : Fin (q + 1), (-1 : ℤ)^j.val •
          shuffleGenerator X Y σ ((TopCat.toSSet.obj Y).δ j.succ τ))) :
    boundary (TopCat.of (X × Y)) (p + 1 + (q + 1)) (shuffleGenerator X Y (p := p + 1) (q := q + 1) σ τ) =
      firstBoundaryTerm X Y (p + 1) (q + 1) (generator X σ) (generator Y τ) +
      (-1 : ℚ)^(p + 1) •
        secondBoundaryTerm X Y (p + 1) (q + 1) (generator X σ) (generator Y τ) := by
  simp only [firstBoundaryTerm, secondBoundaryTerm, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, dite_false]
  change boundary (TopCat.of (X × Y)) (p + 1 + q + 1) (shuffleGenerator X Y (p := p + 1) (q := q + 1) σ τ) =
    regrade (TopCat.of (X × Y)) (by omega : p + (q + 1) = p + 1 + q)
      (shuffleBilinear X Y p (q + 1) (boundary X (p + 1) (generator X σ)) (generator Y τ)) +
    (-1 : ℚ)^(p + 1) •
      regrade (TopCat.of (X × Y)) rfl
        (shuffleBilinear X Y (p + 1) q (generator X σ) (boundary Y (q + 1) (generator Y τ)))
  rw [boundary_eq_initial_sub_positive, faceChain_zero_eq_initialFaceChain,
    initialFace_shuffleGenerator, hp]
  simp only [boundary_eq_initial_sub_positive, faceChain_generator, positiveBoundary_generator,
    map_sub, map_sum, map_zsmul, LinearMap.sub_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, shuffleBilinear_generators, regrade, LinearMap.id_apply]
  simp only [smul_sub]
  module
end HolomorphicAnosov.SignedShuffle
