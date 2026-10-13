import HolomorphicAnosov.Topology.Homology.SignedShuffleDerivedRows

/-!
# Associativity of the signed singular shuffle

Source: Hatcher, Algebraic Topology, §3.B pp.277–278 and Bredon,
Topology and Geometry, VI §§1,3 pp.316–325. Both parenthesizations enumerate
the same three-coordinate staircases, with the same total inversion sign.
-/

noncomputable section
namespace HolomorphicAnosov.SignedSingularCrossProduct

/-- Extend a finite staircase constantly after its last vertex. -/
def trace {p q : ℕ} (w : GridPath p q) : ℕ → ℕ × ℕ := fun k ↦
  let j : Fin (p + q + 1) := ⟨min k (p + q), by omega⟩
  ((w j).1.val, (w j).2.val)

/-- Three coordinate vertex sequences, with constant tails. -/
abbrev TripleTrace := ℕ → ℕ × ℕ × ℕ

/-- Flatten the left parenthesization of coordinate sequences. -/
def leftTriple (a b : ℕ → ℕ × ℕ) : TripleTrace :=
  fun k ↦ ((a (b k).1).1, (a (b k).1).2, (b k).2)

/-- Flatten the right parenthesization of coordinate sequences. -/
def rightTriple (a b : ℕ → ℕ × ℕ) : TripleTrace :=
  fun k ↦ ((a k).1, (b (a k).2).1, (b (a k).2).2)

/-- Evaluate a function on extended staircases, with the original signs. -/
def signedSum {M : Type*} [AddCommGroup M] (p q : ℕ)
    (f : (ℕ → ℕ × ℕ) → M) : M :=
  ∑ a ∈ staircases p q, orientation a • f (trace a)

/-- The signed left-associated sum, before choosing singular simplices. -/
def leftTripleSum {M : Type*} [AddCommGroup M] (p q r : ℕ)
    (f : TripleTrace → M) : M :=
  signedSum p q (fun a ↦ signedSum (p + q) r (fun b ↦ f (leftTriple a b)))

/-- The signed right-associated sum on the same vertex sequences. -/
def rightTripleSum {M : Type*} [AddCommGroup M] (p q r : ℕ)
    (f : TripleTrace → M) : M :=
  signedSum p (q + r) (fun a ↦ signedSum q r (fun b ↦ f (rightTriple a b)))

@[simp] theorem orientation_right_path (p : ℕ) :
    @orientation p 0 (fun k ↦ (k, 0)) = 1 := by
  simp [orientation, inversionCount]

@[simp] theorem orientation_left_path (q : ℕ) :
    orientation (fun k ↦ (0, (⟨k.val, by omega⟩ : Fin (q + 1))) : GridPath 0 q) = 1 := by
  simp [orientation, inversionCount]

/-- A horizontal prefix on an unrestricted coordinate sequence. -/
def prefixH (a : ℕ → ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | k + 1 => ((a k).1 + 1, (a k).2)

/-- A vertical prefix on an unrestricted coordinate sequence. -/
def prefixV (a : ℕ → ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | k + 1 => ((a k).1, (a k).2 + 1)

@[simp] theorem trace_prependHorizontal {p q : ℕ} (a : GridPath p q) :
    trace (prependHorizontal a) = prefixH (trace a) := by
  funext k
  cases k with
  | zero => simp [trace, prependHorizontal, prefixH]
  | succ k =>
    simp only [trace, prependHorizontal, prefixH]
    have h : min (k + 1) (p + 1 + q) = min k (p + q) + 1 := by omega
    simp [h]

@[simp] theorem trace_prependVertical {p q : ℕ} (a : GridPath p q) :
    trace (prependVertical a) = prefixV (trace a) := by
  funext k
  cases k with
  | zero => simp [trace, prependVertical, prefixV]
  | succ k =>
    simp only [trace, prependVertical, prefixV]
    have h : min (k + 1) (p + (q + 1)) = min k (p + q) + 1 := by omega
    simp [h]

/-- Prefix in the first of three coordinate directions. -/
def prefixA (t : TripleTrace) : TripleTrace
  | 0 => (0, 0, 0)
  | k + 1 => ((t k).1 + 1, (t k).2.1, (t k).2.2)

/-- Prefix in the second coordinate direction. -/
def prefixB (t : TripleTrace) : TripleTrace
  | 0 => (0, 0, 0)
  | k + 1 => ((t k).1, (t k).2.1 + 1, (t k).2.2)

/-- Prefix in the third coordinate direction. -/
def prefixC (t : TripleTrace) : TripleTrace
  | 0 => (0, 0, 0)
  | k + 1 => ((t k).1, (t k).2.1, (t k).2.2 + 1)

@[simp] theorem leftTriple_HH (a b : ℕ → ℕ × ℕ) :
    leftTriple (prefixH a) (prefixH b) = prefixA (leftTriple a b) := by
  funext k
  cases k <;> rfl

@[simp] theorem leftTriple_VH (a b : ℕ → ℕ × ℕ) :
    leftTriple (prefixV a) (prefixH b) = prefixB (leftTriple a b) := by
  funext k
  cases k <;> rfl

@[simp] theorem leftTriple_V (a b : ℕ → ℕ × ℕ) (ha : a 0 = (0, 0)) :
    leftTriple a (prefixV b) = prefixC (leftTriple a b) := by
  funext k
  cases k with
  | zero => simp [leftTriple, prefixV, prefixC, ha]
  | succ k => rfl

@[simp] theorem rightTriple_H (a b : ℕ → ℕ × ℕ) (hb : b 0 = (0, 0)) :
    rightTriple (prefixH a) b = prefixA (rightTriple a b) := by
  funext k
  cases k with
  | zero => simp [rightTriple, prefixH, prefixA, hb]
  | succ k => rfl

@[simp] theorem rightTriple_VH (a b : ℕ → ℕ × ℕ) :
    rightTriple (prefixV a) (prefixH b) = prefixB (rightTriple a b) := by
  funext k
  cases k <;> rfl

@[simp] theorem rightTriple_VV (a b : ℕ → ℕ × ℕ) :
    rightTriple (prefixV a) (prefixV b) = prefixC (rightTriple a b) := by
  funext k
  cases k <;> rfl

@[simp] theorem trace_zero {p q : ℕ} (w : GridPath p q)
    (hw : w ∈ staircases p q) : trace w 0 = (0, 0) := by
  have h := (Finset.mem_filter.mp hw).2.1
  simpa [trace] using congrArg (fun z ↦ (z.1.val, z.2.val)) h

/-- All values of the extended path stay inside its rectangular bounds. -/
theorem trace_bounds {p q : ℕ} (w : GridPath p q) (k : ℕ) :
    (trace w k).1 ≤ p ∧ (trace w k).2 ≤ q := by
  dsimp [trace]
  constructor <;> omega

@[simp] theorem trace_clamp {p q : ℕ} (w : GridPath p q) (k : ℕ) :
    trace w (min k (p + q)) = trace w k := by
  simp [trace]

@[simp] theorem trace_right_path (p k : ℕ) :
    @trace p 0 (fun j ↦ (j, 0)) k = (min k p, 0) := rfl

@[simp] theorem trace_left_path (q k : ℕ) :
    @trace 0 q (fun j ↦ (0, ⟨j.val, by omega⟩)) k = (0, min k q) := by
  simp [trace]

@[simp] theorem signedSum_add {M : Type*} [AddCommGroup M] (p q : ℕ)
    (f g : (ℕ → ℕ × ℕ) → M) :
    signedSum p q (fun a ↦ f a + g a) = signedSum p q f + signedSum p q g := by
  simp [signedSum, smul_add, Finset.sum_add_distrib]

@[simp] theorem signedSum_smul {M : Type*} [AddCommGroup M] (p q : ℕ)
    (z : ℤ) (f : (ℕ → ℕ × ℕ) → M) :
    signedSum p q (fun a ↦ z • f a) = z • signedSum p q f := by
  simp only [signedSum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  exact smul_comm _ _ _

theorem signedSum_comm {M : Type*} [AddCommGroup M] (p q s t : ℕ)
    (f : (ℕ → ℕ × ℕ) → (ℕ → ℕ × ℕ) → M) :
    signedSum p q (fun a ↦ signedSum s t (f a)) =
      signedSum s t (fun b ↦ signedSum p q (fun a ↦ f a b)) := by
  simp only [signedSum, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  exact smul_comm _ _ _

theorem signedSum_congr {M : Type*} [AddCommGroup M] (p q : ℕ)
    (f g : (ℕ → ℕ × ℕ) → M)
    (h : ∀ w ∈ staircases p q, f (trace w) = g (trace w)) :
    signedSum p q f = signedSum p q g := by
  apply Finset.sum_congr rfl
  intro w hw
  rw [h w hw]

theorem signedSum_recursion {M : Type*} [AddCommGroup M] (p q : ℕ)
    (f : (ℕ → ℕ × ℕ) → M) :
    signedSum (p + 1) (q + 1) f =
      signedSum p (q + 1) (fun a ↦ f (prefixH a)) +
      (-1 : ℤ) ^ (p + 1) • signedSum (p + 1) q (fun a ↦ f (prefixV a)) := by
  simpa only [signedSum, trace_prependHorizontal, trace_prependVertical] using
    signed_staircase_sum_recursion p q (fun w ↦ f (trace w))

@[simp] theorem signedSum_right_zero {M : Type*} [AddCommGroup M] (p : ℕ)
    (f : (ℕ → ℕ × ℕ) → M) :
    signedSum p 0 f = f (fun k ↦ (min k p, 0)) := by
  simp only [signedSum, SignedShuffle.right_staircase, Finset.sum_singleton,
    orientation_right_path, one_smul]
  rfl

@[simp] theorem signedSum_left_zero {M : Type*} [AddCommGroup M] (q : ℕ)
    (f : (ℕ → ℕ × ℕ) → M) :
    signedSum 0 q f = f (fun k ↦ (0, min k q)) := by
  simp only [signedSum, SignedShuffle.staircases_zero_left, Finset.sum_singleton]
  change orientation (fun k ↦ (0, (⟨k.val, by omega⟩ : Fin (q + 1))) : GridPath 0 q) •
    f (trace (fun k ↦ (0, (⟨k.val, by omega⟩ : Fin (q + 1))) : GridPath 0 q)) = _
  rw [orientation_left_path, one_smul]
  congr 1
  funext k
  exact trace_left_path q k

/-- Zero in the third degree leaves the same two-coordinate signed sum. -/
theorem tripleSum_right_zero {M : Type*} [AddCommGroup M] (p q : ℕ)
    (f : TripleTrace → M) : leftTripleSum p q 0 f = rightTripleSum p q 0 f := by
  simp only [leftTripleSum, rightTripleSum, signedSum_right_zero, Nat.add_zero]
  apply signedSum_congr
  intro w hw
  congr 1
  funext k
  simp [leftTriple, rightTriple, Nat.min_eq_left (trace_bounds w k).2]

/-- Zero in the middle degree leaves the same two-coordinate signed sum. -/
theorem tripleSum_middle_zero {M : Type*} [AddCommGroup M] (p r : ℕ)
    (f : TripleTrace → M) : leftTripleSum p 0 r f = rightTripleSum p 0 r f := by
  simp only [leftTripleSum, rightTripleSum, signedSum_right_zero,
    signedSum_left_zero, Nat.add_zero, Nat.zero_add]
  apply signedSum_congr
  intro w hw
  congr 1
  funext k
  simp [leftTriple, rightTriple, Nat.min_eq_left (trace_bounds w k).1,
    Nat.min_eq_left (trace_bounds w k).2]

/-- Zero in the first degree leaves the same two-coordinate signed sum. -/
theorem tripleSum_left_zero {M : Type*} [AddCommGroup M] (q r : ℕ)
    (f : TripleTrace → M) : leftTripleSum 0 q r f = rightTripleSum 0 q r f := by
  simp only [leftTripleSum, rightTripleSum, signedSum_left_zero, Nat.zero_add]
  apply signedSum_congr
  intro w hw
  congr 1
  funext k
  simp [leftTriple, rightTriple, Nat.min_eq_left (trace_bounds w k).1]

/-- Split the left-associated sum by the first of the three coordinate steps.
Source: EM1953 (5.7), p.65. Split the outer grid first, and then the inner grid
when the outer first step moves its combined coordinate. Prefix identities
identify the three smaller sums; integer scalar multiplication distributes. -/
theorem leftTripleSum_recursion {M : Type*} [AddCommGroup M] (p q r : ℕ)
    (f : TripleTrace → M) :
    leftTripleSum (p + 1) (q + 1) (r + 1) f =
      leftTripleSum p (q + 1) (r + 1) (fun t ↦ f (prefixA t)) +
      (-1 : ℤ) ^ (p + 1) •
        leftTripleSum (p + 1) q (r + 1) (fun t ↦ f (prefixB t)) +
      (-1 : ℤ) ^ ((p + 1) + (q + 1)) •
        leftTripleSum (p + 1) (q + 1) r (fun t ↦ f (prefixC t)) := by
  unfold leftTripleSum
  have ht : p + 1 + (q + 1) = (p + q + 1) + 1 := by omega
  rw [ht]
  simp_rw [signedSum_recursion (p + q + 1) r]
  rw [signedSum_add, signedSum_smul]
  apply congrArg₂ (· + ·)
  · rw [signedSum_comm (p + 1) (q + 1) (p + q + 1) (r + 1)]
    simp_rw [signedSum_recursion p q]
    simp only [leftTriple_HH, leftTriple_VH, signedSum_add, signedSum_smul]
    rw [signedSum_comm (p + q + 1) (r + 1) p (q + 1),
      signedSum_comm (p + q + 1) (r + 1) (p + 1) q]
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  · congr 1
    apply signedSum_congr
    intro a ha
    apply signedSum_congr
    intro b hb
    rw [leftTriple_V _ _ (trace_zero a ha)]

/-- Split the right-associated sum by its first coordinate step. The two
successive vertical signs multiply to (-1)^(p+q), exactly the left-associated
third-coordinate sign. Source: the signed staircase formula and EM1953 (5.7). -/
theorem rightTripleSum_recursion {M : Type*} [AddCommGroup M] (p q r : ℕ)
    (f : TripleTrace → M) :
    rightTripleSum (p + 1) (q + 1) (r + 1) f =
      rightTripleSum p (q + 1) (r + 1) (fun t ↦ f (prefixA t)) +
      (-1 : ℤ) ^ (p + 1) •
        rightTripleSum (p + 1) q (r + 1) (fun t ↦ f (prefixB t)) +
      (-1 : ℤ) ^ ((p + 1) + (q + 1)) •
        rightTripleSum (p + 1) (q + 1) r (fun t ↦ f (prefixC t)) := by
  unfold rightTripleSum
  have ht : q + 1 + (r + 1) = (q + r + 1) + 1 := by omega
  rw [ht, signedSum_recursion p (q + r + 1)]
  have hA :
      (signedSum p (q + r + 1 + 1) fun a ↦
        signedSum (q + 1) (r + 1) fun b ↦ f (rightTriple (prefixH a) b)) =
      signedSum p (q + r + 1 + 1) (fun a ↦
        signedSum (q + 1) (r + 1) fun b ↦ f (prefixA (rightTriple a b))) := by
    apply signedSum_congr
    intro a ha
    apply signedSum_congr
    intro b hb
    rw [rightTriple_H _ _ (trace_zero b hb)]
  rw [hA]
  simp_rw [signedSum_recursion q r]
  simp only [rightTriple_VH, rightTriple_VV, signedSum_add, signedSum_smul]
  rw [smul_add, smul_smul, ← pow_add, ← add_assoc]
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Both parenthesizations enumerate the same signed three-coordinate paths.
Source: Hatcher §3.B pp.277–278. In a zero degree both sums reduce to the same
straight-path sum. Otherwise their proved first-step recursions have the same
three terms and signs. Strong induction on the sum of the degrees proves the
identity for every test function, including every prefixed test function. -/
theorem signed_triple_staircase_associativity {M : Type*} [AddCommGroup M]
    (p q r : ℕ) (f : TripleTrace → M) :
    leftTripleSum p q r f = rightTripleSum p q r f := by
  generalize hn : p + q + r = n
  induction n using Nat.strong_induction_on generalizing p q r f with
  | h n ih =>
    cases p with
    | zero => exact tripleSum_left_zero q r f
    | succ p =>
      cases q with
      | zero => exact tripleSum_middle_zero (p + 1) r f
      | succ q =>
        cases r with
        | zero => exact tripleSum_right_zero (p + 1) (q + 1) f
        | succ r =>
          rw [leftTripleSum_recursion, rightTripleSum_recursion]
          rw [ih (p + (q + 1) + (r + 1)) (by omega) p (q + 1) (r + 1) _ rfl,
            ih ((p + 1) + q + (r + 1)) (by omega) (p + 1) q (r + 1) _ rfl,
            ih ((p + 1) + (q + 1) + r) (by omega) (p + 1) (q + 1) r _ rfl]

end HolomorphicAnosov.SignedSingularCrossProduct

namespace HolomorphicAnosov.SignedSingularCrossProduct

/-- At a genuine vertex the constant extension is the original path. -/
@[simp] theorem trace_at {p q : ℕ} (w : GridPath p q) (k : Fin (p + q + 1)) :
    trace w k.val = ((w k).1.val, (w k).2.val) := by
  simp only [trace, Nat.min_eq_left (Nat.le_of_lt_succ k.isLt)]

/-- Clamp a natural coordinate to a simplex vertex. The clamp disappears on
all the bounded coordinates of an actual staircase. -/
def vertex (p k : ℕ) : Fin (p + 1) := ⟨min k p, by omega⟩

@[simp] theorem vertex_val (p : ℕ) (k : Fin (p + 1)) : vertex p k.val = k := by
  apply Fin.ext
  exact Nat.min_eq_left (Nat.le_of_lt_succ k.isLt)

end HolomorphicAnosov.SignedSingularCrossProduct

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial TensorProduct

namespace HolomorphicAnosov.SignedShuffle
open SignedSingularCrossProduct (GridPath TripleTrace trace leftTriple rightTriple vertex)
universe u

/-- Evaluate three coordinate vertex maps affinely, followed by the three
singular simplices. Source: Hatcher §3.B pp.277–278. -/
def tripleSimplex (X Y Z : TopCat.{u}) {p q r : ℕ} (n : ℕ)
    (σ : Simplex X p) (τ : Simplex Y q) (υ : Simplex Z r) (t : TripleTrace) :
    Simplex (TopCat.of (X × (Y × Z))) n :=
  (TopCat.toSSetObjEquiv (TopCat.of (X × (Y × Z))) (Opposite.op ⦋n⦌)).symm
    (((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ).comp
      ⟨Convexity.StdSimplex.map (fun k : Fin (n + 1) ↦ vertex p (t k.val).1),
        Convexity.StdSimplex.continuous_map ℝ _⟩).prodMk
      (((TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ).comp
        ⟨Convexity.StdSimplex.map (fun k : Fin (n + 1) ↦ vertex q (t k.val).2.1),
          Convexity.StdSimplex.continuous_map ℝ _⟩).prodMk
        ((TopCat.toSSetObjEquiv Z (Opposite.op ⦋r⦌) υ).comp
          ⟨Convexity.StdSimplex.map (fun k : Fin (n + 1) ↦ vertex r (t k.val).2.2),
            Convexity.StdSimplex.continuous_map ℝ _⟩)))

/-- The ordinary product associator, as a continuous map. -/
def associate (X Y Z : TopCat.{u}) : C((X × Y) × Z, X × (Y × Z)) :=
  ⟨fun w ↦ (w.1.1, w.1.2, w.2),
    (continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)⟩

/-- Affine evaluation of the left flattened path is the associated product
simplex. Composition of barycentric maps composes their vertex functions. -/
theorem tripleSimplex_left (X Y Z : TopCat.{u}) {p q r : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) (υ : Simplex Z r)
    (a : GridPath p q) (b : GridPath (p + q) r) :
    (TopCat.toSSet.map (TopCat.ofHom (associate X Y Z))).app (Opposite.op ⦋p + q + r⦌)
      (SignedSingularCrossProduct.productSimplex (TopCat.of (X × Y)) Z b
        (SignedSingularCrossProduct.productSimplex X Y a σ τ) υ) =
      tripleSimplex X Y Z (p + q + r) σ τ υ (leftTriple (trace a) (trace b)) := by
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × (Y × Z)))
    (Opposite.op ⦋p + q + r⦌)).injective
  apply ContinuousMap.ext
  intro z
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
      (Convexity.StdSimplex.map (fun k ↦ (a k).1)
        (Convexity.StdSimplex.map (fun k ↦ (b k).1) z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)
      (Convexity.StdSimplex.map (fun k ↦ (a k).2)
        (Convexity.StdSimplex.map (fun k ↦ (b k).1) z)),
     (TopCat.toSSetObjEquiv Z (Opposite.op ⦋r⦌) υ)
      (Convexity.StdSimplex.map (fun k ↦ (b k).2) z)) = _
  change _ =
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
      (Convexity.StdSimplex.map (fun k : Fin (p + q + r + 1) ↦
        vertex p (leftTriple (trace a) (trace b) k.val).1) z),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)
      (Convexity.StdSimplex.map (fun k : Fin (p + q + r + 1) ↦
        vertex q (leftTriple (trace a) (trace b) k.val).2.1) z),
     (TopCat.toSSetObjEquiv Z (Opposite.op ⦋r⦌) υ)
      (Convexity.StdSimplex.map (fun k : Fin (p + q + r + 1) ↦
        vertex r (leftTriple (trace a) (trace b) k.val).2.2) z))
  simp only [← Convexity.StdSimplex.map_comp]
  simp only [leftTriple, SignedSingularCrossProduct.trace_at,
    SignedSingularCrossProduct.vertex_val, Function.comp_def]

/-- Regrading a unit generator reindexes its affine domain by the finite cast. -/
theorem regrade_generator_map (X : TopCat.{u}) {n m : ℕ} (h : n = m)
    (σ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), X)) :
    regrade X h (generator X ((TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)).symm σ)) =
      generator X ((TopCat.toSSetObjEquiv X (Opposite.op ⦋m⦌)).symm
        (σ.comp ⟨Convexity.StdSimplex.map
          (fun k : Fin (m + 1) ↦ (⟨k.val, by omega⟩ : Fin (n + 1))),
          Convexity.StdSimplex.continuous_map ℝ _⟩)) := by
  subst m
  change generator X _ = generator X _
  apply congrArg (generator X)
  apply congrArg (TopCat.toSSetObjEquiv X (Opposite.op ⦋n⦌)).symm
  apply ContinuousMap.ext
  intro z
  change σ z = σ (Convexity.StdSimplex.map id z)
  rw [Convexity.StdSimplex.map_id]

end HolomorphicAnosov.SignedShuffle

namespace HolomorphicAnosov.SignedShuffle
open SignedSingularCrossProduct (GridPath TripleTrace trace leftTriple rightTriple vertex)
universe u

/-- Affine evaluation of the right flattened path is the right product simplex,
transported to the common total degree. The only reindexing is the finite cast
associated with (p+q)+r=p+(q+r). -/
theorem tripleSimplex_right (X Y Z : TopCat.{u}) {p q r : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) (υ : Simplex Z r)
    (a : GridPath p (q + r)) (b : GridPath q r) :
    regrade (TopCat.of (X × (Y × Z))) (Nat.add_assoc p q r).symm
      (generator (TopCat.of (X × (Y × Z)))
        (SignedSingularCrossProduct.productSimplex X (TopCat.of (Y × Z)) a σ
          (SignedSingularCrossProduct.productSimplex Y Z b τ υ))) =
      generator (TopCat.of (X × (Y × Z)))
        (tripleSimplex X Y Z (p + q + r) σ τ υ (rightTriple (trace a) (trace b))) := by
  rw [SignedSingularCrossProduct.productSimplex, regrade_generator_map]
  apply congrArg (generator (TopCat.of (X × (Y × Z))))
  apply (TopCat.toSSetObjEquiv (TopCat.of (X × (Y × Z)))
    (Opposite.op ⦋p + q + r⦌)).injective
  apply ContinuousMap.ext
  intro z
  let c : Fin (p + q + r + 1) → Fin (p + (q + r) + 1) := fun k ↦ ⟨k.val, by omega⟩
  have ht (k : Fin (p + q + r + 1)) :
      rightTriple (trace a) (trace b) k.val =
        ((a (c k)).1.val, (b (a (c k)).2).1.val, (b (a (c k)).2).2.val) := by
    have he : k.val = (c k).val := rfl
    rw [he]
    simp only [rightTriple, SignedSingularCrossProduct.trace_at]
  change
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
      (Convexity.StdSimplex.map (fun k ↦ (a k).1) (Convexity.StdSimplex.map c z)),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)
      (Convexity.StdSimplex.map (fun k ↦ (b k).1)
        (Convexity.StdSimplex.map (fun k ↦ (a k).2) (Convexity.StdSimplex.map c z))),
     (TopCat.toSSetObjEquiv Z (Opposite.op ⦋r⦌) υ)
      (Convexity.StdSimplex.map (fun k ↦ (b k).2)
        (Convexity.StdSimplex.map (fun k ↦ (a k).2) (Convexity.StdSimplex.map c z)))) =
    ((TopCat.toSSetObjEquiv X (Opposite.op ⦋p⦌) σ)
      (Convexity.StdSimplex.map (fun k : Fin (p + q + r + 1) ↦
        vertex p (rightTriple (trace a) (trace b) k.val).1) z),
     (TopCat.toSSetObjEquiv Y (Opposite.op ⦋q⦌) τ)
      (Convexity.StdSimplex.map (fun k : Fin (p + q + r + 1) ↦
        vertex q (rightTriple (trace a) (trace b) k.val).2.1) z),
     (TopCat.toSSetObjEquiv Z (Opposite.op ⦋r⦌) υ)
      (Convexity.StdSimplex.map (fun k : Fin (p + q + r + 1) ↦
        vertex r (rightTriple (trace a) (trace b) k.val).2.2) z))
  simp only [← Convexity.StdSimplex.map_comp]
  simp only [ht, SignedSingularCrossProduct.vertex_val, Function.comp_def]

end HolomorphicAnosov.SignedShuffle

namespace HolomorphicAnosov.SignedShuffle
open SignedSingularCrossProduct
universe u

/-- The original rational shuffle is associative on unit singular generators.
Source: Hatcher §3.B pp.277–278. Expand both bilinear products into their finite
signed sums, use the two affine composition identities, and apply the proved
three-coordinate signed staircase identity to the generator-valued function. -/
theorem shuffleBilinear_assoc_generator (X Y Z : TopCat.{u}) (p q r : ℕ)
    (σ : Simplex X p) (τ : Simplex Y q) (υ : Simplex Z r) :
    pushforward (associate X Y Z) (p + q + r)
      (shuffleBilinear (TopCat.of (X × Y)) Z (p + q) r
        (shuffleBilinear X Y p q (generator X σ) (generator Y τ)) (generator Z υ)) =
    regrade (TopCat.of (X × (Y × Z))) (Nat.add_assoc p q r).symm
      (shuffleBilinear X (TopCat.of (Y × Z)) p (q + r) (generator X σ)
        (shuffleBilinear Y Z q r (generator Y τ) (generator Z υ))) := by
  classical
  have gen (U V : TopCat.{u}) (i j : ℕ) (a : Simplex U i) (b : Simplex V j) :
      shuffleBilinear U V i j (generator U a) (generator V b) = shuffleGenerator U V a b :=
    shuffle_tmul_generator U V i j a b
  rw [gen X Y p q σ τ, gen Y Z q r τ υ]
  simp only [shuffleGenerator, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    gen, pushforward_generator]
  have h := signed_triple_staircase_associativity p q r
    (fun t ↦ generator (TopCat.of (X × (Y × Z)))
      (tripleSimplex X Y Z (p + q + r) σ τ υ t))
  simp only [leftTripleSum, rightTripleSum, signedSum] at h
  simp_rw [← tripleSimplex_left X Y Z σ τ υ, ← tripleSimplex_right X Y Z σ τ υ] at h
  simp only [Int.cast_smul_eq_zsmul] at *
  simp only [Finset.smul_sum] at h ⊢
  rw [h, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  exact smul_comm _ _ _

end HolomorphicAnosov.SignedShuffle

namespace HolomorphicAnosov.SignedShuffle
universe u

/-- The signed singular shuffle is strictly associative under the ordinary
product associator and the natural-number degree transport.

Source: Hatcher §3.B pp.277–278; Bredon VI §§1,3 pp.316–325. The signed
three-coordinate staircase identity proves equality on three unit generators.
Both expressions are linear in every variable. Apply native singular-chain
coproduct extensionality successively in all three variables. -/
theorem shuffleBilinear_assoc (X Y Z : TopCat.{u}) (p q r : ℕ)
    (a : Chain X p) (b : Chain Y q) (c : Chain Z r) :
    pushforward (associate X Y Z) (p + q + r)
      (shuffleBilinear (TopCat.of (X × Y)) Z (p + q) r
        (shuffleBilinear X Y p q a b) c) =
    regrade (TopCat.of (X × (Y × Z))) (Nat.add_assoc p q r).symm
      (shuffleBilinear X (TopCat.of (Y × Z)) p (q + r) a
        (shuffleBilinear Y Z q r b c)) := by
  let T := Chain (TopCat.of (X × (Y × Z))) (p + q + r)
  let L : Chain X p →ₗ[ℚ] Chain Y q →ₗ[ℚ] Chain Z r →ₗ[ℚ] T :=
    LinearMap.mk₂ ℚ
      (fun a b ↦ (pushforward (associate X Y Z) (p + q + r)).comp
        (shuffleBilinear (TopCat.of (X × Y)) Z (p + q) r (shuffleBilinear X Y p q a b)))
      (by intros; ext; simp)
      (by intros; ext; simp)
      (by intros; ext; simp)
      (by intros; ext; simp)
  let R : Chain X p →ₗ[ℚ] Chain Y q →ₗ[ℚ] Chain Z r →ₗ[ℚ] T :=
    LinearMap.mk₂ ℚ
      (fun a b ↦ (regrade (TopCat.of (X × (Y × Z))) (Nat.add_assoc p q r).symm).comp
        ((shuffleBilinear X (TopCat.of (Y × Z)) p (q + r) a).comp
          (shuffleBilinear Y Z q r b)))
      (by intros; ext; simp)
      (by intros; ext; simp)
      (by intros; ext; simp)
      (by intros; ext; simp)
  have h : L = R := by
    apply chain_linearMap_ext X p (ModuleCat.of ℚ (Chain Y q →ₗ[ℚ] Chain Z r →ₗ[ℚ] T))
    intro σ
    apply chain_linearMap_ext Y q (ModuleCat.of ℚ (Chain Z r →ₗ[ℚ] T))
    intro τ
    apply chain_linearMap_ext Z r (ModuleCat.of ℚ T)
    intro υ
    exact shuffleBilinear_assoc_generator X Y Z p q r σ τ υ
  exact LinearMap.congr_fun (LinearMap.congr_fun (LinearMap.congr_fun h a) b) c

end HolomorphicAnosov.SignedShuffle

