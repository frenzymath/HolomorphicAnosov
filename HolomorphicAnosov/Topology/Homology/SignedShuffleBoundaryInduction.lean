import HolomorphicAnosov.Topology.Homology.SignedShuffleBoundaryAssembly
import HolomorphicAnosov.Topology.Homology.SignedShuffleDerivedRows
import HolomorphicAnosov.Topology.Homology.SignedShuffleOneOneBoundary
import HolomorphicAnosov.Topology.Homology.SignedShuffleData
import HolomorphicAnosov.Topology.Homology.SignedShuffleDerivativeSpecialization
import HolomorphicAnosov.Topology.Homology.SignedShuffleDerivedRecursion

/-! For arbitrary topological spaces in any universe and singular simplices in degrees p+1 and q+1, the actual rational signed staircase sum satisfies the exact native generator boundary Leibniz identity with sign (−1)^(p+1). The proof uses EM Theorem5.2 total-degree induction on the paired universal input models, then evaluates its derived identities on arbitrary inputs.

Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §5 degree-one edge induction (5.13)–(5.14), p.66, and total-degree induction applying (5.8′) to both recurrence terms, p.67. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct
namespace HolomorphicAnosov.SignedShuffle
universe u
open OperatorModel

/-- The positive-face induction step when both input degrees exceed one. -/
theorem shuffle_positive_faces_interior (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 2)) (τ : Simplex Y (q + 2))
    (hA : positiveBoundary (TopCat.of (X × Y)) (p + 1 + (q + 2))
      (derivedShuffleGenerator X Y σ ((TopCat.toSSet.obj Y).σ 0 τ)) =
      regrade (TopCat.of (X × Y)) (by omega : p + (q + 2) + 1 = p + 1 + (q + 2))
        (∑ i : Fin (p + 2), (-1 : ℤ)^i.val •
          derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).δ i.succ σ) ((TopCat.toSSet.obj Y).σ 0 τ)) +
      (-1 : ℚ)^(p + 1) •
        regrade (TopCat.of (X × Y)) (by omega : p + 1 + (q + 1) + 1 = p + 1 + (q + 2))
          (∑ j : Fin (q + 3), (-1 : ℤ)^j.val •
            derivedShuffleGenerator X Y σ ((TopCat.toSSet.obj Y).δ j.succ ((TopCat.toSSet.obj Y).σ 0 τ))))
    (hB : positiveBoundary (TopCat.of (X × Y)) (p + 2 + (q + 1))
      (derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).σ 0 σ) τ) =
      regrade (TopCat.of (X × Y)) (by omega : p + 1 + (q + 1) + 1 = p + 2 + (q + 1))
        (∑ i : Fin (p + 3), (-1 : ℤ)^i.val •
          derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).δ i.succ ((TopCat.toSSet.obj X).σ 0 σ)) τ) +
      (-1 : ℚ)^(p + 2) •
        regrade (TopCat.of (X × Y)) (by omega : p + 2 + q + 1 = p + 2 + (q + 1))
          (∑ j : Fin (q + 2), (-1 : ℤ)^j.val •
            derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).σ 0 σ) ((TopCat.toSSet.obj Y).δ j.succ τ))) :
    positiveBoundary (TopCat.of (X × Y)) (p + 2 + (q + 1))
        (shuffleGenerator X Y (p := p + 2) (q := q + 2) σ τ) =
      regrade (TopCat.of (X × Y)) (by omega : (p + 1) + (q + 2) = p + 2 + (q + 1))
        (∑ i : Fin (p + 2), (-1 : ℤ)^i.val •
          shuffleGenerator X Y ((TopCat.toSSet.obj X).δ i.succ σ) τ) +
      (-1 : ℚ)^(p + 2) •
        (∑ j : Fin (q + 2), (-1 : ℤ)^j.val •
          shuffleGenerator X Y σ ((TopCat.toSSet.obj Y).δ j.succ τ)) := by
  rw [shuffleGenerator_derived_recursion X Y (p + 1) (q + 1)]
  simp only [map_add, map_smul]
  rw [positiveBoundary_regrade (h := (by omega : p + 1 + (q + 2) = p + 2 + (q + 1))),
    positiveBoundary_regrade (h := (rfl : p + 2 + (q + 1) = p + 2 + (q + 1))), hA, hB]
  rw [positiveFace_degeneracy_sum Y (q + 1), positiveFace_degeneracy_sum X (p + 1) σ
    (fun s ↦ derivedShuffleGenerator X Y s τ)]
  simp only [shuffleGenerator_derived_recursion, map_add, map_sub, map_smul, map_sum,
    map_zsmul, regrade_trans, smul_add, smul_sub, Finset.sum_add_distrib,
    Finset.smul_sum]
  have hc (z : ℤ) (r : ℚ) (c : Chain (TopCat.of (X × Y)) (p + 2 + (q + 1))) :
      z • r • c = r • z • c := smul_comm z r c
  simp only [hc, ← Finset.smul_sum, pow_succ]
  module

/-- The first-degree left edge of the positive-face induction. -/
theorem shuffle_positive_faces_left_edge (X Y : TopCat.{u}) (q : ℕ)
    (σ : Simplex X 1) (τ : Simplex Y (q + 2))
    (hB : positiveBoundary (TopCat.of (X × Y)) (1 + (q + 1))
      (derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).σ 0 σ) τ) =
      regrade (TopCat.of (X × Y)) (by omega : 0 + (q + 1) + 1 = 1 + (q + 1))
        (∑ i : Fin 2, (-1 : ℤ)^i.val •
          derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).δ i.succ ((TopCat.toSSet.obj X).σ 0 σ)) τ) +
      (-1 : ℚ)^1 •
        regrade (TopCat.of (X × Y)) (by omega : 1 + q + 1 = 1 + (q + 1))
          (∑ j : Fin (q + 2), (-1 : ℤ)^j.val •
            derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).σ 0 σ) ((TopCat.toSSet.obj Y).δ j.succ τ))) :
    positiveBoundary (TopCat.of (X × Y)) (1 + (q + 1))
        (shuffleGenerator X Y (p := 1) (q := q + 2) σ τ) =
      regrade (TopCat.of (X × Y)) (by omega : 0 + (q + 2) = 1 + (q + 1))
        (∑ i : Fin 1, (-1 : ℤ)^i.val •
          shuffleGenerator X Y ((TopCat.toSSet.obj X).δ i.succ σ) τ) +
      (-1 : ℚ)^1 •
        (∑ j : Fin (q + 2), (-1 : ℤ)^j.val •
          shuffleGenerator X Y σ ((TopCat.toSSet.obj Y).δ j.succ τ)) := by
  have hA := derivedShuffleGenerator_left_row_boundary X Y (q + 1) σ
    ((TopCat.toSSet.obj Y).σ 0 τ)
  rw [shuffleGenerator_derived_recursion X Y 0 (q + 1)]
  simp only [map_add, map_smul]
  rw [positiveBoundary_regrade (h := (by omega : 0 + (q + 2) = 1 + (q + 1))),
    positiveBoundary_regrade (h := (rfl : 1 + (q + 1) = 1 + (q + 1))), hB]
  have hA' := congrArg (regrade (TopCat.of (X × Y)) (by omega : q + 2 = 0 + (q + 2))) hA
  rw [positiveBoundary_regrade (h := (by omega : 0 + (q + 2) = q + 2))] at hA'
  simp only [map_sum, map_zsmul, regrade_trans] at hA'
  change positiveBoundary _ (0 + (q + 2)) _ = _ at hA'
  rw [hA']
  rw [positiveFace_degeneracy_sum X 0 σ (fun s ↦ derivedShuffleGenerator X Y s τ)]
  simp only [map_add, map_sub, map_smul, map_sum, map_zsmul, regrade_trans]
  simp only [← map_sum, ← map_zsmul]
  rw [positiveFace_degeneracy_sum Y (q + 1)]
  simp only [derivedShuffle_degenerate_point_left, shuffleGenerator_derived_recursion,
    map_sub, map_sum, map_zsmul,
    smul_add, smul_sub, Finset.sum_add_distrib, Finset.smul_sum, pow_one,
    neg_smul, one_smul, smul_neg, Finset.sum_neg_distrib]
  simp only [Nat.zero_add, pow_one, neg_smul, one_smul, smul_neg, Finset.sum_neg_distrib]
  module

/-- The first-degree right edge of the positive-face induction. -/
theorem shuffle_positive_faces_right_edge (X Y : TopCat.{u}) (p : ℕ)
    (σ : Simplex X (p + 2)) (τ : Simplex Y 1)
    (hA : positiveBoundary (TopCat.of (X × Y)) (p + 1 + 1)
      (derivedShuffleGenerator X Y (p := p + 1) (q := 1) σ ((TopCat.toSSet.obj Y).σ 0 τ)) =
      regrade (TopCat.of (X × Y)) (by omega : p + 1 + 1 = p + 1 + 1)
        (∑ i : Fin (p + 2), (-1 : ℤ)^i.val •
          derivedShuffleGenerator X Y ((TopCat.toSSet.obj X).δ i.succ σ) ((TopCat.toSSet.obj Y).σ 0 τ)) +
      (-1 : ℚ)^(p + 1) •
        regrade (TopCat.of (X × Y)) (by omega : p + 1 + 0 + 1 = p + 1 + 1)
          (∑ j : Fin 2, (-1 : ℤ)^j.val •
            derivedShuffleGenerator X Y σ ((TopCat.toSSet.obj Y).δ j.succ ((TopCat.toSSet.obj Y).σ 0 τ)))) :
    positiveBoundary (TopCat.of (X × Y)) (p + 2 + 0)
        (shuffleGenerator X Y (p := p + 2) (q := 1) σ τ) =
      regrade (TopCat.of (X × Y)) (by omega : p + 1 + 1 = p + 2 + 0)
        (∑ i : Fin (p + 2), (-1 : ℤ)^i.val •
          shuffleGenerator X Y ((TopCat.toSSet.obj X).δ i.succ σ) τ) +
      (-1 : ℚ)^(p + 2) •
        (∑ j : Fin 1, (-1 : ℤ)^j.val •
          shuffleGenerator X Y σ ((TopCat.toSSet.obj Y).δ j.succ τ)) := by
  have hB := derivedShuffleGenerator_right_row_boundary X Y (p + 1)
    ((TopCat.toSSet.obj X).σ 0 σ) τ
  rw [shuffleGenerator_derived_recursion X Y (p + 1) 0]
  simp only [map_add, map_smul]
  rw [positiveBoundary_regrade (h := (rfl : p + 1 + 1 = p + 2)),
    positiveBoundary_regrade (h := (rfl : p + 2 + 0 = p + 2)), hA, hB]
  rw [positiveFace_degeneracy_sum Y 0, positiveFace_degeneracy_sum X (p + 1) σ
    (fun s ↦ derivedShuffleGenerator X Y s τ)]
  simp only [derivedShuffle_degenerate_point_right, shuffleGenerator_derived_recursion,
    map_add, map_sub, map_smul, map_sum, map_zsmul, regrade_trans, smul_add, smul_sub,
    Finset.sum_add_distrib, Finset.smul_sum]
  have hc (z : ℤ) (r : ℚ) (c : Chain (TopCat.of (X × Y)) (p + 2)) :
      z • r • c = r • z • c := smul_comm z r c
  simp only [hc, ← Finset.smul_sum, pow_succ, regrade, LinearMap.id_apply]
  module

end HolomorphicAnosov.SignedShuffle
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct
namespace HolomorphicAnosov.SignedShuffle
universe u
open OperatorModel

/-- The native shuffle boundary law on the pair of universal identity inputs. -/
def ModelBoundaryLaw (p q : ℕ) : Prop :=
  boundary (Space (p + 1) (q + 1)) (p + 1 + (q + 1))
    (shuffleGenerator (ModelSpace (p + 1)) (ModelSpace (q + 1))
      (modelInput id) (modelInput id)) =
    firstBoundaryTerm (ModelSpace (p + 1)) (ModelSpace (q + 1)) (p + 1) (q + 1)
      (generator _ (modelInput id)) (generator _ (modelInput id)) +
    (-1 : ℚ)^(p + 1) •
      secondBoundaryTerm (ModelSpace (p + 1)) (ModelSpace (q + 1)) (p + 1) (q + 1)
        (generator _ (modelInput id)) (generator _ (modelInput id))

/-- EM (5.11): lower universal boundary identities imply the next boundary
identity for arbitrary singular input simplices. -/
theorem shuffle_boundary_induction_step (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1))
    (ih : ∀ r s, r + s < p + q → ModelBoundaryLaw r s) :
    boundary (TopCat.of (X × Y)) (p + 1 + (q + 1)) (shuffleGenerator X Y (p := p + 1) (q := q + 1) σ τ) =
      firstBoundaryTerm X Y (p + 1) (q + 1) (generator X σ) (generator Y τ) +
      (-1 : ℚ)^(p + 1) •
        secondBoundaryTerm X Y (p + 1) (q + 1) (generator X σ) (generator Y τ) := by
  cases p with
  | zero =>
    cases q with
    | zero => exact shuffle_one_one_boundary_generator X Y σ τ
    | succ q =>
      apply shuffle_boundary_of_positive_faces X Y 0 (q + 1) σ τ
      apply shuffle_positive_faces_left_edge X Y q σ τ
      exact derivedShuffle_boundary_of_model_boundary X Y 0 q
        ((TopCat.toSSet.obj X).σ 0 σ) τ (ih 0 q (by omega))
  | succ p =>
    cases q with
    | zero =>
      apply shuffle_boundary_of_positive_faces X Y (p + 1) 0 σ τ
      apply shuffle_positive_faces_right_edge X Y p σ τ
      exact derivedShuffle_boundary_of_model_boundary X Y p 0
        σ ((TopCat.toSSet.obj Y).σ 0 τ) (ih p 0 (by omega))
    | succ q =>
      apply shuffle_boundary_of_positive_faces X Y (p + 1) (q + 1) σ τ
      apply shuffle_positive_faces_interior X Y p q σ τ
      · exact derivedShuffle_boundary_of_model_boundary X Y p (q + 1)
          σ ((TopCat.toSSet.obj Y).σ 0 τ) (ih p (q + 1) (by omega))
      · exact derivedShuffle_boundary_of_model_boundary X Y (p + 1) q
          ((TopCat.toSSet.obj X).σ 0 σ) τ (ih (p + 1) q (by omega))

/-- Strong induction proves all universal positive-positive boundary laws. -/
theorem modelBoundaryLaw (p q : ℕ) : ModelBoundaryLaw p q := by
  have h (n : ℕ) : ∀ p q, p + q = n → ModelBoundaryLaw p q := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p q hpq
      apply shuffle_boundary_induction_step (ModelSpace (p + 1)) (ModelSpace (q + 1))
        p q (modelInput id) (modelInput id)
      intro r s hrs
      exact ih (r + s) (by omega) r s rfl
  exact h (p + q) p q rfl

/-- For arbitrary topological spaces in any universe and singular simplices in degrees p+1 and q+1, the actual rational signed staircase sum satisfies the exact native generator boundary Leibniz identity with sign (−1)^(p+1). The proof uses EM Theorem5.2 total-degree induction on the paired universal input models, then evaluates its derived identities on arbitrary inputs.

Source and proof origin: Eilenberg–Mac Lane, On the Groups H(Π,n), I (1953), §5 degree-one edge induction (5.13)–(5.14), p.66, and total-degree induction applying (5.8′) to both recurrence terms, p.67. Supplied original: literature/G2-EM1953-full-supplied.txt and corresponding PDF.

Proof: In bidegrees at least two, expand the actual shuffle by the proved initial-degeneracy recurrence. Apply the two lower derived boundary laws. Expand positive faces of each initial degeneracy as input minus its degenerated positive-face sum. The two middle derived shuffles have opposite signs and cancel; factor scalar signs out of the finite sums and apply the same shuffle recurrence to every remaining input-face term. This is (5.11) in the interior.

If the first degree is one, the first derived recurrence term uses the exceptional left-row boundary law (5.13) and the second uses the lower positive-positive derived law (5.14). Expand both positive-face degeneracy sums. The middle terms cancel, the degenerated point term becomes the ordinary zero-degree row, and the remaining face terms recombine by (5.7). The right edge uses exactly the symmetric right-row calculation. No negative-degree product or false assertion F₁=0 is used.

Define the universal boundary proposition at successor indices p,q, and prove it by strong induction on p+q. At zero use the explicit (1,1) calculation. On each edge use the corresponding preceding universal identity. In the interior both required universal identities have index sum one smaller. Transfer those lower identities by derivation to the recurrence terms. Apply the edge or interior positive-face step and then subtract it from the initial-face formula.

Having proved every universal model identity in universe zero, apply the same induction step to arbitrary X,Y in any universe using those universal laws. The coefficient derivation already has arbitrary target universe, so this specialization needs no universe resizing axiom. The result is precisely the unchanged native generator statement. -/
theorem shuffle_positive_boundary_generator_proved (X Y : TopCat.{u}) (p q : ℕ)
    (σ : Simplex X (p + 1)) (τ : Simplex Y (q + 1)) :
    boundary (TopCat.of (X × Y)) (p + 1 + (q + 1)) (shuffleGenerator X Y (p := p + 1) (q := q + 1) σ τ) =
      firstBoundaryTerm X Y (p + 1) (q + 1) (generator X σ) (generator Y τ) +
      (-1 : ℚ)^(p + 1) •
        secondBoundaryTerm X Y (p + 1) (q + 1) (generator X σ) (generator Y τ) :=
  shuffle_boundary_induction_step X Y p q σ τ (fun r s _ ↦ modelBoundaryLaw r s)

end HolomorphicAnosov.SignedShuffle
