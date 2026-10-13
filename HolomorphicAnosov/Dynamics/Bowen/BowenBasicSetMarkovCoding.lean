import HolomorphicAnosov.Dynamics.Bowen.StablePlaqueInteriorIntegerChart
import HolomorphicAnosov.Dynamics.Bowen.LocalPredecessorCollisionFrontier
import HolomorphicAnosov.Dynamics.Bowen.PredecessorTraceDensity
import HolomorphicAnosov.Dynamics.Bowen.StablePlaqueIntegerChart
import HolomorphicAnosov.Dynamics.Bowen.PlaqueRebase
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import HolomorphicAnosov.Dynamics.Bowen.FactOneNarrowBracketModulus
import HolomorphicAnosov.Dynamics.Bowen.FactOneRefinementScales
import HolomorphicAnosov.Dynamics.Bowen.StableTransitiveOnSmallCell
import HolomorphicAnosov.Dynamics.Bowen.UnstableCoverAtClosedOverlap
import HolomorphicAnosov.Dynamics.Bowen.StableInclusionAtClosedOverlap
import HolomorphicAnosov.Dynamics.Bowen.OriginalFactOneGivesCompactProductData
import HolomorphicAnosov.Dynamics.Bowen.CompactLocalProductProperPartition
import HolomorphicAnosov.Dynamics.Bowen.ProductChart
import HolomorphicAnosov.Dynamics.Bowen.RectangleSlices
import HolomorphicAnosov.Dynamics.Bowen.RegularClosedProduct
import HolomorphicAnosov.Dynamics.Bowen.StablePlaqueBackwardChart
import HolomorphicAnosov.Dynamics.Bowen.StableDirectionalBoundaryTrace
import HolomorphicAnosov.Topology.DenseRestrictRegularClosed
import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import Mathlib.Data.Set.Card
import Mathlib.Dynamics.SymbolicDynamics.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order

/-!
# Bowen coding of a locally maximal transitive hyperbolic set

Sources: Bowen, *Markov Partitions for Axiom A Diffeomorphisms*, AJM 92 (1970),
pp. 725–747, especially Fact 1, Theorem 12, Lemmas 25–27 and Theorem 28;
and *Markov Partitions and Minimal Sets for Axiom A Diffeomorphisms*,
AJM 92 (1970), pp. 907–918, especially Proposition 10, Corollary 11 and
Proposition 12. The full natural-language source proof is attached below.

All stable/unstable plaques and rectangle properties are actual definitions.
The continuous tangent distributions need only be defined continuously over
the invariant set; values outside that set are unrestricted and carry no
hyperbolicity assumption. The adapted metric is an output witness, not an
extra local-product/bracket hypothesis. Diameters and splice estimates use
the original metric throughout.
-/

noncomputable section

namespace HolomorphicAnosov
namespace BowenBasicSetCoding

open Set Filter Manifold Bundle
open scoped _root_.Topology ContDiff Bundle ENNReal

section Symbolic

variable {X : Type*} [TopologicalSpace X]

/-- Restrict the original map to its invariant set, using Mathlib's native
subtype homeomorphism. Source: Bowen 1970, p. 725. The invariance equivalence
is equivalent to f(Λ)=Λ because f is bijective. -/
def restrictedDynamics (f : X ≃ₜ X) (Λ : Set X)
    (hΛ : ∀ x : X, x ∈ Λ ↔ f x ∈ Λ) : Λ ≃ₜ Λ :=
  f.subtype hΛ

/-- The closed local stable orbit plaque in the specified metric, Bowen p. 726. -/
def localStable (f : X ≃ₜ X) (d : X → X → ℝ) (γ : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, d ((f ^ n) y) ((f ^ n) x) ≤ γ}

/-- The closed local unstable orbit plaque, with genuine negative integer
iterates, Bowen p. 726. -/
def localUnstable (f : X ≃ₜ X) (d : X → X → ℝ) (γ : ℝ) (x : X) : Set X :=
  {y | ∀ n : ℕ, d ((f ^ (-(n : ℤ))) y) ((f ^ (-(n : ℤ))) x) ≤ γ}

/-- A nonempty compact proper rectangle closed under the unique local
stable/unstable intersection. Source: Bowen pp. 727,729. All topology here
is the invariant set's relative topology, including zero-dimensional factors. -/
def IsRectangle (f : X ≃ₜ X) (d : X → X → ℝ) (γ : ℝ) (R : Set X) : Prop :=
  R.Nonempty ∧ IsCompact R ∧ R = closure (interior R) ∧
    ∀ x ∈ R, ∀ y ∈ R, ∃ z ∈ R, ∀ w : X,
      (w ∈ localStable f d γ x ∧ w ∈ localUnstable f d γ y) ↔ w = z

/-- The stable slice of a rectangle, Bowen p. 729. -/
def stableSlice (f : X ≃ₜ X) (d : X → X → ℝ) (γ : ℝ) (x : X) (R : Set X) : Set X :=
  R ∩ localStable f d γ x

/-- The unstable slice of a rectangle, Bowen p. 729. -/
def unstableSlice (f : X ≃ₜ X) (d : X → X → ℝ) (γ : ℝ) (x : X) (R : Set X) : Set X :=
  R ∩ localUnstable f d γ x

/-- The witnessed Markov inclusions, Bowen p. 731. The source and target
interiors are in the invariant set, not in the ambient manifold. -/
def HasMarkovInclusions {N : ℕ} (f : X ≃ₜ X) (d : X → X → ℝ)
    (γ : ℝ) (R : Fin N → Set X) : Prop :=
  ∀ i j : Fin N, ∀ x : X, x ∈ interior (R i) → f x ∈ interior (R j) →
    f '' stableSlice f d γ x (R i) ⊆ stableSlice f d γ (f x) (R j) ∧
    unstableSlice f d γ (f x) (R j) ⊆ f '' unstableSlice f d γ x (R i)

/-- The binary transition relation: true (matrix entry one) exactly for an
interior-to-interior transition. Source: Bowen pp. 740–741. -/
def transition {N : ℕ} (f : X ≃ₜ X) (R : Fin N → Set X) (i j : Fin N) : Prop :=
  (f '' interior (R i) ∩ interior (R j)).Nonempty

/-- The complete two-sided code space for a finite binary transition relation,
with its native subtype-of-product topology. Source: Bowen pp. 740–742. -/
abbrev CodeSpace {N : ℕ} (B : Fin N → Fin N → Prop) :=
  {a : ℤ → Fin N // ∀ j : ℤ, B (a j) (a (j + 1))}

/-- The native Mathlib left shift, restricted to legal codes. Source: Bowen
p. 741. Its structural proof merely reindexes the same adjacency condition. -/
def codeShift {N : ℕ} (B : Fin N → Fin N → Prop) (a : CodeSpace B) : CodeSpace B :=
  ⟨SymbolicDynamics.FullShift.shift (1 : ℤ) a.val, fun j => by
    simpa only [SymbolicDynamics.FullShift.shift_apply, add_assoc] using a.property (1 + j)⟩

/-- Bowen 1970a, p.740: the legal two-sided sequence space is closed in the compact
finite-alphabet product. Each adjacency condition is the inverse image of a closed subset
of the finite discrete pair alphabet under two coordinate evaluations. -/
private theorem isCompact_codeSpace_univ {N : ℕ} (B : Fin N → Fin N → Prop) :
    IsCompact (Set.univ : Set (CodeSpace B)) := by
  have hclosed : IsClosed {a : ℤ → Fin N | ∀ j : ℤ, B (a j) (a (j + 1))} := by
    simp only [ofPred_forall]
    refine isClosed_iInter fun j ↦ ?_
    have hc : Continuous (fun a : ℤ → Fin N ↦ (a j, a (j + 1))) :=
      (continuous_apply j).prodMk (continuous_apply (j + 1))
    exact IsClosed.preimage hc (isClosed_discrete {p : Fin N × Fin N | B p.1 p.2})
  let : CompactSpace (CodeSpace B) := isCompact_iff_compactSpace.mp hclosed.isCompact
  exact isCompact_univ

/-- Bowen 1970a, p.740: the restricted left shift is continuous by coordinate evaluation. -/
private theorem continuous_codeShift {N : ℕ} (B : Fin N → Fin N → Prop) :
    Continuous (codeShift B) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun j ↦ (continuous_apply (1 + j)).comp continuous_subtype_val

/-- Bowen 1970a, p.740: the shift has the genuine predecessor sequence as its inverse.
This works also for an empty alphabet/code space; no existence of a legal sequence is assumed. -/
private theorem bijective_codeShift {N : ℕ} (B : Fin N → Fin N → Prop) :
    Function.Bijective (codeShift B) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    funext j
    have hj := congrArg (fun c : CodeSpace B ↦ c.val (j - 1)) hab
    simpa [codeShift, SymbolicDynamics.FullShift.shift_apply] using hj
  · intro a
    let b : CodeSpace B := ⟨fun j ↦ a.val (j - 1), fun j ↦ by
      simpa using a.property (j - 1)⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    funext j
    simp [b, codeShift, SymbolicDynamics.FullShift.shift_apply]

/-- Bowen 1970a, Theorem28 and the bracket-code splice: use the past of a through zero
and the future of b after zero. The only mixed transition is 0→1; its legality follows
from the common zero symbol. In particular no transitions are added to B. -/
private theorem exists_spliced_code {N : ℕ} (B : Fin N → Fin N → Prop)
    (a b : CodeSpace B) (hzero : a.val 0 = b.val 0) :
    ∃ c : CodeSpace B,
      (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
      (∀ j : ℤ, 0 ≤ j → c.val j = b.val j) := by
  let v : ℤ → Fin N := fun j ↦ if j ≤ 0 then a.val j else b.val j
  have hv : ∀ j : ℤ, B (v j) (v (j + 1)) := by
    intro j
    by_cases hj : j < 0
    · have hj0 : j ≤ 0 := le_of_lt hj
      have hj1 : j + 1 ≤ 0 := by omega
      simpa [v, hj0, hj1] using a.property j
    · have hj0 : 0 ≤ j := le_of_not_gt hj
      by_cases heq : j = 0
      · subst j
        simpa [v, hzero] using b.property 0
      · have hjpos : ¬ j ≤ 0 := by omega
        have hj1 : ¬ j + 1 ≤ 0 := by omega
        simpa [v, hjpos, hj1] using b.property j
  refine ⟨⟨v, hv⟩, ?_, ?_⟩
  · intro j hj
    simp [v, hj]
  · intro j hj
    by_cases heq : j = 0
    · subst j
      simpa [v] using hzero
    · have hjpos : ¬ j ≤ 0 := by omega
      simp [v, hjpos]

/-- Bowen Lemma27: membership in the singleton all-time itinerary is literal membership
in every indexed rectangle, including the zero and negative integer times. -/
private theorem coding_mem_rectangle {N : ℕ} (F : X ≃ₜ X) (R : Fin N → Set X)
    (coding : CodeSpace (transition F R) → X)
    (hit : ∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a})
    (a : CodeSpace (transition F R)) (j : ℤ) :
    (F ^ j) (coding a) ∈ R (a.val j) := by
  have hmem : coding a ∈ {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} := by
    rw [hit a]
    exact mem_singleton _
  exact hmem j

/-- Bowen Theorem28: shift covariance is a consequence of the singleton itinerary,
not an additional hypothesis on a selected coding map. Integer powers use the original F. -/
private theorem coding_shift_covariance {N : ℕ} (F : X ≃ₜ X) (R : Fin N → Set X)
    (coding : CodeSpace (transition F R) → X)
    (hit : ∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a})
    (a : CodeSpace (transition F R)) : coding (codeShift (transition F R) a) = F (coding a) := by
  have hmem : F (coding a) ∈
      {x : X | ∀ j : ℤ, (F ^ j) x ∈ R ((codeShift (transition F R) a).val j)} := by
    intro j
    have hj := coding_mem_rectangle F R coding hit a (j + 1)
    simpa [codeShift, SymbolicDynamics.FullShift.shift_apply, zpow_add,
      Homeomorph.mul_apply, add_comm] using hj
  rw [hit (codeShift (transition F R) a)] at hmem
  exact (mem_singleton_iff.mp hmem).symm

/-- Bowen 1970b, Corollary11 p.913: over a periodic point a finite fibre is permuted
by a positive iterate of the shift. Restrict that iterate to the actual fibre, use
injectivity on its finite subtype, and multiply the two positive return times. -/
private theorem periodic_code_of_finite_fibre {N : ℕ} (B : Fin N → Fin N → Prop)
    (F : X ≃ₜ X) (coding : CodeSpace B → X)
    (hcov : ∀ a, coding (codeShift B a) = F (coding a))
    (x : X) (hfinite : {a : CodeSpace B | coding a = x}.Finite)
    (m : ℕ) (hm : 0 < m) (hx : (F ^ m) x = x)
    (a : CodeSpace B) (ha : coding a = x) :
    ∃ k : ℕ, 0 < k ∧ (codeShift B)^[k] a = a := by
  have hsemi : Function.Semiconj coding (codeShift B) (F : X → X) := hcov
  have hiter : ∀ n : ℕ, ∀ b : CodeSpace B,
      coding ((codeShift B)^[n] b) = (F ^ n) (coding b) := by
    intro n b
    have hpow : (F : X → X)^[n] = (F ^ n : X ≃ₜ X) := by
      induction n with
      | zero => rfl
      | succ n ih =>
        funext z
        simp only [Function.iterate_succ_apply', pow_succ', Homeomorph.mul_apply, ih]
    rw [← hpow]
    exact hsemi.iterate_right n b
  let S := {b : CodeSpace B | coding b = x}
  let : Finite S := hfinite.to_subtype
  let g : S → S := fun b ↦ ⟨(codeShift B)^[m] b.val, by
    change coding ((codeShift B)^[m] b.val) = x
    rw [hiter, b.property, hx]⟩
  have hg : Function.Injective g := by
    intro b c hbc
    apply Subtype.ext
    exact ((bijective_codeShift B).injective.iterate m) (congrArg Subtype.val hbc)
  obtain ⟨k, hk, hreturn⟩ := Function.mem_periodicPts.mp
    (hg.mem_periodicPts (⟨a, ha⟩ : S))
  have hval : ∀ (k : ℕ) (b : S), (g^[k] b).val = ((codeShift B)^[m])^[k] b.val := by
    intro k b
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [Function.iterate_succ_apply', g]
      exact congrArg ((codeShift B)^[m]) ih
  refine ⟨m * k, Nat.mul_pos hm hk, ?_⟩
  rw [Function.iterate_mul]
  have hret := congrArg Subtype.val hreturn
  simpa only [hval] using hret

/-- The public periodic-code assertion follows from the actual encard fibre bound, without
choosing an enumeration or assuming the coding is injective. This is Corollary11 p.913. -/
private theorem periodic_code_of_bounded_fibre {N : ℕ} (B : Fin N → Fin N → Prop)
    (F : X ≃ₜ X) (coding : CodeSpace B → X)
    (hcov : ∀ a, coding (codeShift B a) = F (coding a)) (D : ℕ)
    (hbound : ∀ x : X, {a : CodeSpace B | coding a = x}.encard ≤ (D : ℕ∞))
    (x : X) (hx : ∃ m : ℕ, 0 < m ∧ (F ^ m) x = x) :
    ∀ a : CodeSpace B, coding a = x →
      ∃ k : ℕ, 0 < k ∧ (codeShift B)^[k] a = a := by
  obtain ⟨m, hm, hx⟩ := hx
  intro a ha
  exact periodic_code_of_finite_fibre B F coding hcov x
    (Set.finite_of_encard_le_coe (hbound x)) m hm hx a ha

/-- Bowen1970b Proposition12: once coordinate rigidity is proved, every-label realization
makes the coordinate map a bijection onto the exact closed rectangle labels at that time. -/
private theorem coordinate_bijOn_of_code_rigidity {N : ℕ} (F : X ≃ₜ X)
    (R : Fin N → Set X) (coding : CodeSpace (transition F R) → X)
    (hlabels : ∀ (x : X) (j : ℤ) (i : Fin N), (F ^ j) x ∈ R i ↔
      ∃ a : CodeSpace (transition F R), coding a = x ∧ a.val j = i)
    (x : X)
    (hrigid : ∀ a b : CodeSpace (transition F R), coding a = x → coding b = x →
      (∃ j : ℤ, a.val j = b.val j) → a = b) (j : ℤ) :
    Set.BijOn (fun a : CodeSpace (transition F R) ↦ a.val j)
      {a | coding a = x} {i | (F ^ j) x ∈ R i} := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    exact (hlabels x j (a.val j)).mpr ⟨a, ha, rfl⟩
  · intro a ha b hb hab
    exact hrigid a b ha hb ⟨j, hab⟩
  · intro i hi
    obtain ⟨a, ha, haj⟩ := (hlabels x j i).mp hi
    exact ⟨a, ha, haj⟩

end Symbolic

section SymbolicMetric

variable {X : Type*} [MetricSpace X]

/-- Bowen Theorem28's splice estimate in the original metric. The legal splice was constructed
above; both coded iterates belong to the same compact rectangle on the relevant half-line.
The diameter bound has a strict margin and is used directly, with no adapted-metric equality. -/
private theorem exists_spliced_code_dist {N : ℕ} (F : X ≃ₜ X)
    (R : Fin N → Set X) (coding : CodeSpace (transition F R) → X)
    (hit : ∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a})
    (hcompact : ∀ i, IsCompact (R i)) (ε : ℝ)
    (hdiam : ∀ i, Metric.diam (R i) < ε)
    (a b : CodeSpace (transition F R)) (hzero : a.val 0 = b.val 0) :
    ∃ c : CodeSpace (transition F R),
      (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
      (∀ j : ℤ, 0 ≤ j → c.val j = b.val j) ∧
      (∀ j : ℤ, 0 ≤ j → dist ((F ^ j) (coding c)) ((F ^ j) (coding b)) < ε) ∧
      (∀ j : ℤ, j ≤ 0 → dist ((F ^ j) (coding c)) ((F ^ j) (coding a)) < ε) := by
  obtain ⟨c, hcneg, hcpos⟩ := exists_spliced_code (transition F R) a b hzero
  refine ⟨c, hcneg, hcpos, ?_, ?_⟩
  · intro j hj
    have hc := coding_mem_rectangle F R coding hit c j
    rw [hcpos j hj] at hc
    exact (Metric.dist_le_diam_of_mem (hcompact (b.val j)).isBounded hc
      (coding_mem_rectangle F R coding hit b j)).trans_lt (hdiam (b.val j))
  · intro j hj
    have hc := coding_mem_rectangle F R coding hit c j
    rw [hcneg j hj] at hc
    exact (Metric.dist_le_diam_of_mem (hcompact (a.val j)).isBounded hc
      (coding_mem_rectangle F R coding hit a j)).trans_lt (hdiam (a.val j))

/-- Bowen Lemma27 uniqueness from the literal public rectangle definition. Two full
itinerary points stay in the same small rectangle at every integer time, so one belongs
to the stable and unstable plaques of the other. The diagonal rectangle pair identifies
that intersection with its center. No existence of itinerary points is assumed or proved here. -/
private theorem itinerary_subsingleton {N : ℕ} (F : X ≃ₜ X) (γ : ℝ)
    (hγ : 0 ≤ γ) (R : Fin N → Set X)
    (hR : ∀ i, IsRectangle F dist γ (R i))
    (hdiam : ∀ i, Metric.diam (R i) ≤ γ)
    (a : ℤ → Fin N) :
    ({x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a j)} : Set X).Subsingleton := by
  intro x hx y hy
  have hx0 : x ∈ R (a 0) := by simpa using hx 0
  obtain ⟨z, hz, hunique⟩ := (hR (a 0)).2.2.2 x hx0 x hx0
  have hdiag : x ∈ localStable F dist γ x ∧ x ∈ localUnstable F dist γ x := by
    constructor <;> intro n <;> simpa using hγ
  have hboth : y ∈ localStable F dist γ x ∧ y ∈ localUnstable F dist γ x := by
    constructor
    · intro n
      have hxn : (F ^ (n : ℤ)) x ∈ R (a n) := hx n
      have hyn : (F ^ (n : ℤ)) y ∈ R (a n) := hy n
      have hpow : ∀ w : X, (F ^ (n : ℤ)) w = (F ^ n) w := by simp
      simp only [hpow] at hxn hyn
      exact (Metric.dist_le_diam_of_mem (hR (a n)).2.1.isBounded hyn hxn).trans (hdiam _)
    · intro n
      exact (Metric.dist_le_diam_of_mem (hR (a (-(n : ℤ)))).2.1.isBounded
        (hy (-(n : ℤ))) (hx (-(n : ℤ)))).trans (hdiam _)
  exact (hunique x |>.mp hdiag).trans (hunique y |>.mp hboth).symm

/-- Bowen Lemma27's singleton identity after finite-word compactness supplies nonemptiness.
Classical choice selects an actual itinerary point; the preceding proved uniqueness forces
exact equality of the whole set with its singleton. This is an existence theorem, not hollow data. -/
private theorem exists_singleton_itinerary {N : ℕ} (F : X ≃ₜ X) (γ : ℝ)
    (hγ : 0 ≤ γ) (R : Fin N → Set X)
    (hR : ∀ i, IsRectangle F dist γ (R i))
    (hdiam : ∀ i, Metric.diam (R i) ≤ γ)
    (a : ℤ → Fin N)
    (hne : ({x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a j)} : Set X).Nonempty) :
    ∃ p : X, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a j)} = {p} := by
  obtain ⟨p, hp⟩ := hne
  refine ⟨p, Set.ext fun x ↦ ?_⟩
  constructor
  · intro hx
    exact mem_singleton_iff.mpr (itinerary_subsingleton F γ hγ R hR hdiam a hx hp)
  · intro hx
    simpa only [mem_singleton_iff.mp hx] using hp

/-- Native iterate bridge: a homeomorphism power acts by the corresponding function iterate. -/
private theorem homeomorph_nat_pow_apply (F : X ≃ₜ X) (n : ℕ) (x : X) :
    (F ^ n) x = (F : X → X)^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Homeomorph.mul_apply,
      Function.iterate_succ_apply', ih]

/-- The canonical product provider and this theorem use exactly the same closed stable plaques. -/
private theorem localStable_eq_relative (F : X ≃ₜ X) (γ : ℝ) (x : X) :
    localStable F dist γ x = Dynamics.relativeClosedStablePlaque F γ x := by
  ext y
  simp only [localStable, Dynamics.relativeClosedStablePlaque, mem_ofPred_eq,
    homeomorph_nat_pow_apply]

/-- Backward orbit plaques agree as well: negative powers are powers of the actual inverse. -/
private theorem localUnstable_eq_relative (F : X ≃ₜ X) (γ : ℝ) (x : X) :
    localUnstable F dist γ x = Dynamics.relativeClosedUnstablePlaque F γ x := by
  ext y
  have hpow : ∀ n : ℕ, (F ^ (-(n : ℤ))) = F.symm ^ n := by
    intro n
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    rfl
  simp only [localUnstable, Dynamics.relativeClosedUnstablePlaque, mem_ofPred_eq,
    hpow, homeomorph_nat_pow_apply]

/-- Bowen Theorem12, using the published proper-partition provider on the same compact
canonical-coordinate datum. Choosing the mesh below its actual close-pair radius makes
bracket closure equivalent to the public unique-plaque rectangle condition. The alphabet
is nonempty because the space is nonempty and covered. No connectedness of cells is inferred. -/
private theorem exists_native_markov_partition [CompactSpace X] [Nonempty X]
    (F : X ≃ₜ X) (γ lam : ℝ) (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (N : ℕ), 1 ≤ N ∧ ∃ R : Fin N → Set X,
      (∀ i, IsRectangle F dist γ (R i) ∧ Metric.diam (R i) < ε) ∧
      (∀ i j, i ≠ j → Disjoint (interior (R i)) (interior (R j))) ∧
      (⋃ i, R i) = univ ∧ HasMarkovInclusions F dist γ R := by
  obtain ⟨N, R, hR, hcover, hdisj, hmarkov⟩ :=
    Dynamics.Bowen.compactLocalProductProperPartition F γ lam H
      (min ε H.closeRadius) (lt_min hε H.closeRadius_pos)
  have hN : 1 ≤ N := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hx : x ∈ ⋃ i, R i := hcover.symm ▸ mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt)
  refine ⟨N, hN, R, ?_, hdisj, hcover, ?_⟩
  · intro i
    obtain ⟨hne, hc, hd, hr, hb⟩ := hR i
    refine ⟨⟨hne, hc, hr, ?_⟩, hd.trans_le (min_le_left _ _)⟩
    intro x hx y hy
    have hxy : dist x y ≤ H.closeRadius :=
      (Metric.dist_le_diam_of_mem hc.isBounded hx hy).trans
        (hd.le.trans (min_le_right _ _))
    refine ⟨H.bracket x y, hb x hx y hy, fun w ↦ ?_⟩
    simp only [localStable_eq_relative, localUnstable_eq_relative]
    constructor
    · exact H.bracket_unique x y w hxy
    · rintro rfl
      exact H.bracket_mem x y hxy
  · intro i j x hx hfx
    simpa only [stableSlice, unstableSlice, localStable_eq_relative,
      localUnstable_eq_relative] using hmarkov i j x hx hfx

/-- Bowen Lemma4: compactness upgrades two-sided expansivity to one uniform finite window.
The decreasing compact sets consist of pairs separated by ζ whose first n forward/backward
orbit distances are at most γ. A point in their intersection contradicts expansivity. -/
theorem exists_finite_expansive_window [CompactSpace X] (F : X ≃ₜ X)
    (γ : ℝ)
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ γ) → x = y)
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ n : ℕ, ∀ x y : X,
      (∀ j : ℤ, |j| ≤ n → dist ((F ^ j) x) ((F ^ j) y) ≤ γ) → dist x y < ζ := by
  let K : ℕ → Set (X × X) := fun n ↦
    {p | ζ ≤ dist p.1 p.2 ∧ ∀ j : ℤ, |j| ≤ n → dist ((F ^ j) p.1) ((F ^ j) p.2) ≤ γ}
  have hclosed : ∀ n, IsClosed (K n) := by
    intro n
    change IsClosed ({p : X × X | ζ ≤ dist p.1 p.2} ∩
      {p : X × X | ∀ j : ℤ, |j| ≤ n → dist ((F ^ j) p.1) ((F ^ j) p.2) ≤ γ})
    apply IsClosed.inter (isClosed_le continuous_const (continuous_fst.dist continuous_snd))
    simp only [ofPred_forall]
    exact isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦ isClosed_le
      (((F ^ j).continuous.comp continuous_fst).dist
        ((F ^ j).continuous.comp continuous_snd)) continuous_const
  have hdec : ∀ n, K (n + 1) ⊆ K n := by
    intro n p hp
    refine ⟨hp.1, fun j hj ↦ hp.2 j (hj.trans ?_)⟩
    exact_mod_cast Nat.le_succ n
  have hempty : ¬ (⋂ n, K n).Nonempty := by
    rintro ⟨⟨x, y⟩, hxy⟩
    have heq : x = y := hexp x y fun j ↦ by
      have hp := mem_iInter.mp hxy j.natAbs
      exact hp.2 j (by simp)
    have hsep := (mem_iInter.mp hxy 0).1
    rw [heq, dist_self] at hsep
    exact (not_le_of_gt hζ) hsep
  have hsome : ∃ n, ¬ (K n).Nonempty := by
    by_contra! hn
    exact hempty (IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      K hdec hn (hclosed 0).isCompact hclosed)
  obtain ⟨n, hn⟩ := hsome
  refine ⟨n, fun x y hxy ↦ ?_⟩
  by_contra! hsep
  exact hn ⟨(x, y), hsep, hxy⟩

/-- Bowen Theorem28's continuity deduction. Finite-window expansivity and the literal
singleton itineraries suffice; coordinate cylinders are open in the given product subtype
and every window distance is bounded by the common rectangle diameter. -/
private theorem continuous_coding_of_singleton_itinerary [CompactSpace X] {N : ℕ}
    (F : X ≃ₜ X) (γ : ℝ) (R : Fin N → Set X)
    (hcompact : ∀ i, IsCompact (R i)) (hdiam : ∀ i, Metric.diam (R i) ≤ γ)
    (hexp : ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ γ) → x = y)
    (coding : CodeSpace (transition F R) → X)
    (hit : ∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a}) :
    Continuous coding := by
  classical
  apply Metric.continuous_iff'.mpr
  intro a ζ hζ
  obtain ⟨n, hn⟩ := exists_finite_expansive_window F γ hexp ζ hζ
  let S : Finset ℤ := Finset.Icc (-(n : ℤ)) n
  have hcoords : ∀ j ∈ S, ∀ᶠ b : CodeSpace (transition F R) in 𝓝 a,
      b.val j = a.val j := by
    intro j hj
    have hc : Continuous (fun b : CodeSpace (transition F R) ↦ b.val j) :=
      (continuous_apply j).comp continuous_subtype_val
    exact hc.continuousAt.eventually (isOpen_discrete {a.val j} |>.mem_nhds rfl)
  have hwindow : ∀ᶠ b : CodeSpace (transition F R) in 𝓝 a,
      ∀ j ∈ S, b.val j = a.val j := (Filter.eventually_all_finite S.finite_toSet).mpr hcoords
  filter_upwards [hwindow] with b hb
  apply hn (coding b) (coding a)
  intro j hj
  have hjS : j ∈ S := by
    simp only [S, Finset.mem_Icc]
    exact abs_le.mp hj
  have hmem := coding_mem_rectangle F R coding hit b j
  rw [hb j hjS] at hmem
  exact (Metric.dist_le_diam_of_mem (hcompact (a.val j)).isBounded hmem
    (coding_mem_rectangle F R coding hit a j)).trans (hdiam _)

/-- Bowen Lemma27's compactness step, separated from the geometric finite-word realization.
Every closed finite window is compact, the windows decrease, and every integer is captured
by its natural absolute-value window. -/
private theorem nonempty_itinerary_of_nonempty_windows [CompactSpace X] {N : ℕ}
    (F : X ≃ₜ X) (R : Fin N → Set X) (hcompact : ∀ i, IsCompact (R i))
    (a : ℤ → Fin N)
    (hwindow : ∀ n : ℕ, ∃ x : X, ∀ j : ℤ, |j| ≤ n → (F ^ j) x ∈ R (a j)) :
    ({x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a j)} : Set X).Nonempty := by
  let K : ℕ → Set X := fun n ↦ {x | ∀ j : ℤ, |j| ≤ n → (F ^ j) x ∈ R (a j)}
  have hc : ∀ n, IsClosed (K n) := by
    intro n
    simp only [K, ofPred_forall]
    exact isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
      IsClosed.preimage (F ^ j).continuous (hcompact (a j)).isClosed
  have hn : ∀ n, (K n).Nonempty := hwindow
  have hd : ∀ n, K (n + 1) ⊆ K n := by
    intro n x hx j hj
    exact hx j (hj.trans (by exact_mod_cast Nat.le_succ n))
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K hd hn (hc 0).isCompact hc
  refine ⟨x, fun j ↦ ?_⟩
  exact mem_iInter.mp hx j.natAbs j (by simp)

/-- Bowen Lemma3 for the public rectangle notion: a cover by rectangles gives expansivity
at the plaque scale, since the diagonal pair in any containing rectangle has a unique
stable/unstable intersection in the entire carrier. -/
private theorem expansive_of_rectangle_cover {N : ℕ} (F : X ≃ₜ X) (γ : ℝ)
    (hγ : 0 ≤ γ) (R : Fin N → Set X) (hR : ∀ i, IsRectangle F dist γ (R i))
    (hcover : (⋃ i, R i) = univ) :
    ∀ x y : X, (∀ j : ℤ, dist ((F ^ j) x) ((F ^ j) y) ≤ γ) → x = y := by
  intro x y hxy
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
  obtain ⟨z, hz, hu⟩ := (hR i).2.2.2 x hi x hi
  have hx : x ∈ localStable F dist γ x ∧ x ∈ localUnstable F dist γ x := by
    constructor <;> intro n <;> simpa using hγ
  have hy : y ∈ localStable F dist γ x ∧ y ∈ localUnstable F dist γ x := by
    constructor
    · intro n
      simpa only [zpow_natCast, dist_comm] using hxy (n : ℤ)
    · intro n
      simpa only [dist_comm] using hxy (-(n : ℤ))
  exact (hu x |>.mp hx).trans (hu y |>.mp hy).symm

/-- Once Bowen Lemma26 has realized every finite legal strip, compactness, uniqueness and
finite-window expansivity construct a continuous actual coding map and prove covariance.
Only existence is chosen; neither an unknown function nor an arbitrary orbit point is supplied.
The finite-fibre and periodic-rigidity arguments remain independent. -/
private theorem exists_continuous_coding_of_finite_words [CompactSpace X] {N : ℕ}
    (F : X ≃ₜ X) (γ : ℝ) (hγ : 0 ≤ γ) (R : Fin N → Set X)
    (hR : ∀ i, IsRectangle F dist γ (R i))
    (hdiam : ∀ i, Metric.diam (R i) ≤ γ)
    (hcover : (⋃ i, R i) = univ)
    (hword : ∀ a : CodeSpace (transition F R), ∀ n : ℕ,
      ∃ x : X, ∀ j : ℤ, |j| ≤ n → (F ^ j) x ∈ R (a.val j)) :
    ∃ coding : CodeSpace (transition F R) → X,
      (∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a}) ∧
      Continuous coding ∧
      (∀ a, coding (codeShift (transition F R) a) = F (coding a)) := by
  classical
  have hexists : ∀ a : CodeSpace (transition F R),
      ∃ p : X, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {p} := by
    intro a
    exact exists_singleton_itinerary F γ hγ R hR hdiam a.val
      (nonempty_itinerary_of_nonempty_windows F R (fun i ↦ (hR i).2.1) a.val (hword a))
  choose coding hit using hexists
  refine ⟨coding, hit, ?_, coding_shift_covariance F R coding hit⟩
  exact continuous_coding_of_singleton_itinerary F γ R (fun i ↦ (hR i).2.1) hdiam
    (expansive_of_rectangle_cover F γ hγ R hR hcover) coding hit

/-- Bowen Theorem28's onto argument on the original compact relative carrier. Regular
closure makes the union of interiors dense; Baire supplies dense boundary-avoiding orbits.
Their literal labels give legal codes, and compactness closes the coding image. -/
private theorem surjective_coding_of_singleton_itinerary [CompactSpace X] {N : ℕ}
    (F : X ≃ₜ X) (R : Fin N → Set X)
    (hproper : ∀ i, R i = closure (interior (R i)))
    (hcover : (⋃ i, R i) = univ)
    (coding : CodeSpace (transition F R) → X) (hcont : Continuous coding)
    (hit : ∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a}) :
    Function.Surjective coding := by
  classical
  let Y : Set X := ⋃ i, interior (R i)
  have hYopen : IsOpen Y := isOpen_iUnion fun i ↦ isOpen_interior
  have hYdense : Dense Y := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
    have hi' : x ∈ closure (interior (R i)) := hproper i ▸ hi
    exact closure_mono (subset_iUnion (fun i ↦ interior (R i)) i) hi'
  let Z : Set X := ⋂ j : ℤ, (F ^ j) ⁻¹' Y
  have hZdense : Dense Z := dense_iInter_of_isOpen
    (fun j ↦ hYopen.preimage (F ^ j).continuous)
    (fun j ↦ hYdense.preimage (F ^ j).isOpenMap)
  have hZimage : Z ⊆ Set.range coding := by
    intro x hx
    have hex : ∀ j : ℤ, ∃ i : Fin N, (F ^ j) x ∈ interior (R i) := by
      intro j
      exact mem_iUnion.mp (mem_iInter.mp hx j)
    choose a ha using hex
    have hlegal : ∀ j : ℤ, transition F R (a j) (a (j + 1)) := by
      intro j
      refine ⟨(F ^ (j + 1)) x, ?_, ha (j + 1)⟩
      refine ⟨(F ^ j) x, ha j, ?_⟩
      rw [add_comm j 1, zpow_add]
      rfl
    let b : CodeSpace (transition F R) := ⟨a, hlegal⟩
    have hxit : x ∈ {y : X | ∀ j : ℤ, (F ^ j) y ∈ R (b.val j)} := by
      intro j
      exact interior_subset (ha j)
    rw [hit b] at hxit
    exact ⟨b, (mem_singleton_iff.mp hxit).symm⟩
  have hclosed : IsClosed (Set.range coding) := by
    have hc := (isCompact_codeSpace_univ (transition F R)).image hcont
    simpa only [image_univ] using hc.isClosed
  intro x
  have hx : x ∈ closure (Set.range coding) :=
    hZdense.mono hZimage x
  rw [hclosed.closure_eq] at hx
  exact hx

/-- Bowen1970b Lemma1(a): every closed rectangle label at every integer time is realized
by a code of that same point. The cylinder image is compact/closed; boundary-avoiding
orbits are dense in each open inverse rectangle interior, and properness closes it. -/
private theorem every_label_realized [CompactSpace X] {N : ℕ}
    (F : X ≃ₜ X) (R : Fin N → Set X)
    (hproper : ∀ i, R i = closure (interior (R i)))
    (hcover : (⋃ i, R i) = univ)
    (coding : CodeSpace (transition F R) → X) (hcont : Continuous coding)
    (hit : ∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a}) :
    ∀ (x : X) (j : ℤ) (i : Fin N), (F ^ j) x ∈ R i ↔
      ∃ a : CodeSpace (transition F R), coding a = x ∧ a.val j = i := by
  classical
  let Y : Set X := ⋃ i, interior (R i)
  have hYopen : IsOpen Y := isOpen_iUnion fun i ↦ isOpen_interior
  have hYdense : Dense Y := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x)
    exact closure_mono (subset_iUnion (fun i ↦ interior (R i)) i) (hproper i ▸ hi)
  let Z : Set X := ⋂ j : ℤ, (F ^ j) ⁻¹' Y
  have hZdense : Dense Z := dense_iInter_of_isOpen
    (fun j ↦ hYopen.preimage (F ^ j).continuous)
    (fun j ↦ hYdense.preimage (F ^ j).isOpenMap)
  intro x j i
  constructor
  · intro hx
    let C : Set (CodeSpace (transition F R)) := {a | a.val j = i}
    have hc : IsClosed C := isClosed_eq
      ((continuous_apply j).comp continuous_subtype_val) continuous_const
    have himage : IsClosed (coding '' C) :=
      ((isCompact_codeSpace_univ (transition F R)).of_isClosed_subset hc (subset_univ C)
        |>.image hcont).isClosed
    let Q : Set X := (F ^ j) ⁻¹' interior (R i)
    have hQopen : IsOpen Q := isOpen_interior.preimage (F ^ j).continuous
    have hQimage : Q ∩ Z ⊆ coding '' C := by
      intro y hy
      have hex : ∀ k : ℤ, ∃ l : Fin N, (F ^ k) y ∈ interior (R l) := by
        intro k
        exact mem_iUnion.mp (mem_iInter.mp hy.2 k)
      choose a ha using hex
      let v : ℤ → Fin N := Function.update a j i
      have hv : ∀ k : ℤ, (F ^ k) y ∈ interior (R (v k)) := by
        intro k
        by_cases hk : k = j
        · subst k
          simpa [v, Q] using hy.1
        · simpa [v, hk] using ha k
      have hlegal : ∀ k : ℤ, transition F R (v k) (v (k + 1)) := by
        intro k
        refine ⟨(F ^ (k + 1)) y, ⟨(F ^ k) y, hv k, ?_⟩, hv (k + 1)⟩
        rw [add_comm k 1, zpow_add]
        rfl
      let b : CodeSpace (transition F R) := ⟨v, hlegal⟩
      have hby : coding b = y := by
        have hyit : y ∈ {z : X | ∀ k : ℤ, (F ^ k) z ∈ R (b.val k)} :=
          fun k ↦ interior_subset (hv k)
        rw [hit b] at hyit
        exact (mem_singleton_iff.mp hyit).symm
      exact ⟨b, by simp [C, b, v], hby⟩
    have hxQ : x ∈ closure Q := by
      apply (F ^ j).isOpenMap.preimage_closure_subset_closure_preimage
      exact hproper i ▸ hx
    have hQclosure : Q ⊆ closure (Q ∩ Z) := by
      intro y hy
      apply hQopen.inter_closure
      exact ⟨hy, hZdense y⟩
    have hximage : x ∈ coding '' C := by
      have hxcl : x ∈ closure (Q ∩ Z) := by
        have ht := closure_mono hQclosure hxQ
        simpa only [closure_closure] using ht
      exact himage.closure_subset_iff.mpr hQimage hxcl
    obtain ⟨a, ha, hax⟩ := hximage
    exact ⟨a, hax, ha⟩
  · rintro ⟨a, hax, ha⟩
    have hm := coding_mem_rectangle F R coding hit a j
    simpa only [hax, ha] using hm

/-- The completed Bowen Lemma27/Theorem28 consumer block, relative only to the genuine
finite-word realization step. This combines the proved compactness, expansivity, Baire,
closed-cylinder and splice deductions for the same chosen partition and coding map. -/
private theorem exists_coding_from_finite_word_realization [CompactSpace X] {N : ℕ}
    (F : X ≃ₜ X) (γ : ℝ) (hγ : 0 ≤ γ) (R : Fin N → Set X)
    (hR : ∀ i, IsRectangle F dist γ (R i))
    (hdiam : ∀ i, Metric.diam (R i) ≤ γ)
    (hcover : (⋃ i, R i) = univ)
    (hword : ∀ a : CodeSpace (transition F R), ∀ n : ℕ,
      ∃ x : X, ∀ j : ℤ, |j| ≤ n → (F ^ j) x ∈ R (a.val j))
    (ε : ℝ) (hmesh : ∀ i, Metric.diam (R i) < ε) :
    ∃ coding : CodeSpace (transition F R) → X,
      (∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a}) ∧
      Continuous coding ∧ Function.Surjective coding ∧
      (∀ a, coding (codeShift (transition F R) a) = F (coding a)) ∧
      (∀ (x : X) (j : ℤ) (i : Fin N), (F ^ j) x ∈ R i ↔
        ∃ a : CodeSpace (transition F R), coding a = x ∧ a.val j = i) ∧
      (∀ a b : CodeSpace (transition F R), a.val 0 = b.val 0 →
        ∃ c : CodeSpace (transition F R),
          (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
          (∀ j : ℤ, 0 ≤ j → c.val j = b.val j) ∧
          (∀ j : ℤ, 0 ≤ j → dist ((F ^ j) (coding c)) ((F ^ j) (coding b)) < ε) ∧
          (∀ j : ℤ, j ≤ 0 → dist ((F ^ j) (coding c)) ((F ^ j) (coding a)) < ε)) := by
  obtain ⟨coding, hit, hcont, hcov⟩ :=
    exists_continuous_coding_of_finite_words F γ hγ R hR hdiam hcover hword
  refine ⟨coding, hit, hcont, ?_, hcov, ?_, ?_⟩
  · exact surjective_coding_of_singleton_itinerary F R
      (fun i ↦ (hR i).2.2.1) hcover coding hcont hit
  · exact every_label_realized F R (fun i ↦ (hR i).2.2.1) hcover coding hcont hit
  · exact fun a b hzero ↦ exists_spliced_code_dist F R coding hit
      (fun i ↦ (hR i).2.1) ε hmesh a b hzero


section FiniteStrips
variable [CompactSpace X]

/-- Weak Lemma26, exactly sufficient for finite words: a nonempty subset saturated
by source unstable slices stays nonempty and saturated in the receiving rectangle.
The source witness supplies one point through [w,z]; closed-overlap covering supplies
saturation. No regularity or properness of the intermediate subset is needed. -/
private theorem nonempty_unstable_saturated_image (F : X ≃ₜ X) (γ lam : ℝ)
    (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (E T A : Set X) (hEc : IsCompact E) (hEd : Metric.diam E ≤ H.closeRadius)
    (hEb : ∀ p ∈ E, ∀ q ∈ E, H.bracket p q ∈ E)
    (hA : A.Nonempty) (hAE : A ⊆ E)
    (hsat : ∀ z ∈ A, E ∩ Dynamics.relativeClosedUnstablePlaque F γ z ⊆ A)
    (w : X) (hw : w ∈ E)
    (hincl : F '' (E ∩ Dynamics.relativeClosedStablePlaque F γ w) ⊆
      T ∩ Dynamics.relativeClosedStablePlaque F γ (F w))
    (hclosedCover : ∀ x ∈ E, F x ∈ T →
      T ∩ Dynamics.relativeClosedUnstablePlaque F γ (F x) ⊆
        F '' (E ∩ Dynamics.relativeClosedUnstablePlaque F γ x)) :
    (F '' A ∩ T).Nonempty ∧ F '' A ∩ T ⊆ T ∧
      ∀ y ∈ F '' A ∩ T, T ∩ Dynamics.relativeClosedUnstablePlaque F γ y ⊆ F '' A ∩ T := by
  obtain ⟨z, hz⟩ := hA
  have hclose : dist w z ≤ H.closeRadius :=
    (Metric.dist_le_diam_of_mem hEc.isBounded hw (hAE hz)).trans hEd
  have hb := H.bracket_mem w z hclose
  have hbE : H.bracket w z ∈ E := hEb w hw z (hAE hz)
  have hbA : H.bracket w z ∈ A := hsat z hz ⟨hbE, hb.2⟩
  have hfb := hincl ⟨H.bracket w z, ⟨hbE, hb.1⟩, rfl⟩
  refine ⟨⟨F (H.bracket w z), ⟨H.bracket w z, hbA, rfl⟩, hfb.1⟩,
    inter_subset_right, ?_⟩
  rintro y ⟨⟨x, hx, rfl⟩, hfx⟩ t ht
  obtain ⟨v, hv, hfv⟩ := hclosedCover x (hAE hx) hfx ht
  exact ⟨⟨v, hsat x hx hv, hfv⟩, ht.1⟩

/-- Apply witnessed Markov laws to their literal interior witness and then the
proved closed-overlap covering. The forward zero-time collar is written explicitly:
it concerns all points of ONE source rectangle, not an arbitrary global bracket. -/
private theorem legal_transition_preserves_unstable_saturation {N : ℕ}
    (F : X ≃ₜ X) (γ lam : ℝ) (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (R : Fin N → Set X) (hc : ∀ i, IsCompact (R i))
    (hd : ∀ i, Metric.diam (R i) ≤ H.closeRadius)
    (hsmall : ∀ i, 2 * Metric.diam (R i) ≤ γ)
    (hb : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, H.bracket p q ∈ R i)
    (hforward : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, dist (F p) (F q) ≤ γ)
    (hmarkov : ∀ i j x, x ∈ interior (R i) → F x ∈ interior (R j) →
      F '' (R i ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆
        R j ∩ Dynamics.relativeClosedStablePlaque F γ (F x) ∧
      R j ∩ Dynamics.relativeClosedUnstablePlaque F γ (F x) ⊆
        F '' (R i ∩ Dynamics.relativeClosedUnstablePlaque F γ x))
    (i j : Fin N) (hlegal : transition F R i j) (A : Set X)
    (hA : A.Nonempty) (hAi : A ⊆ R i)
    (hsat : ∀ x ∈ A, R i ∩ Dynamics.relativeClosedUnstablePlaque F γ x ⊆ A) :
    (F '' A ∩ R j).Nonempty ∧ F '' A ∩ R j ⊆ R j ∧
      ∀ y ∈ F '' A ∩ R j,
        R j ∩ Dynamics.relativeClosedUnstablePlaque F γ y ⊆ F '' A ∩ R j := by
  obtain ⟨t, ⟨w, hw, rfl⟩, hfw⟩ := hlegal
  have hlaws := hmarkov i j w hw hfw
  have hwR := interior_subset hw
  have hfwR := interior_subset hfw
  apply nonempty_unstable_saturated_image F γ lam H (R i) (R j) A (hc i) (hd i)
    (hb i) hA hAi hsat w hwR hlaws.1
  intro x hx hfx
  apply unstable_cover_at_closed_overlap F γ lam H (R i) (R j) (hc i) (hc j)
    (hd i) (hd j) (hsmall j) (hb i) (hb j)
    (fun p hp q hq _ _ ↦ hforward i (H.bracket p q) (hb i p hp q hq) q hq)
    w hwR hfwR hlaws.2 x hx hfx

/-- Bowen Lemmas26--27 finite forward-word induction. The actual recursively transported
sets are nonempty unstable-saturated subsets of their receiving rectangles. Pull back the
chosen final point through the recorded images to obtain a single original starting point. -/
private theorem realize_finite_forward_word {N : ℕ}
    (F : X ≃ₜ X) (γ lam : ℝ) (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (R : Fin N → Set X) (hne : ∀ i, (R i).Nonempty) (hc : ∀ i, IsCompact (R i))
    (hd : ∀ i, Metric.diam (R i) ≤ H.closeRadius)
    (hsmall : ∀ i, 2 * Metric.diam (R i) ≤ γ)
    (hb : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, H.bracket p q ∈ R i)
    (hforward : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, dist (F p) (F q) ≤ γ)
    (hmarkov : ∀ i j x, x ∈ interior (R i) → F x ∈ interior (R j) →
      F '' (R i ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆
        R j ∩ Dynamics.relativeClosedStablePlaque F γ (F x) ∧
      R j ∩ Dynamics.relativeClosedUnstablePlaque F γ (F x) ⊆
        F '' (R i ∩ Dynamics.relativeClosedUnstablePlaque F γ x))
    (a : ℕ → Fin N) (hlegal : ∀ k : ℕ, transition F R (a k) (a (k + 1))) :
    ∀ n : ℕ, ∃ x : X, ∀ k : ℕ, k ≤ n → (F ^ k) x ∈ R (a k) := by
  let T : ℕ → Set X := fun n ↦ Nat.rec (R (a 0))
    (fun k A ↦ F '' A ∩ R (a (k + 1))) n
  have hT : ∀ n : ℕ, (T n).Nonempty ∧ T n ⊆ R (a n) ∧
      (∀ y ∈ T n, R (a n) ∩ Dynamics.relativeClosedUnstablePlaque F γ y ⊆ T n) ∧
      (∀ y ∈ T n, ∃ x : X, (F ^ n) x = y ∧
        ∀ k : ℕ, k ≤ n → (F ^ k) x ∈ R (a k)) := by
    intro n
    induction n with
    | zero =>
      refine ⟨hne (a 0), Subset.rfl, fun _ _ ↦ inter_subset_left, ?_⟩
      intro y hy
      refine ⟨y, rfl, ?_⟩
      intro k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact hy
    | succ n ih =>
      have hnext := legal_transition_preserves_unstable_saturation F γ lam H R hc hd
        hsmall hb hforward hmarkov (a n) (a (n + 1)) (hlegal n) (T n)
        ih.1 ih.2.1 ih.2.2.1
      refine ⟨hnext.1, hnext.2.1, hnext.2.2, ?_⟩
      rintro y ⟨⟨z, hz, hfz⟩, hy⟩
      obtain ⟨x, hxz, hxword⟩ := ih.2.2.2 z hz
      have hxn : (F ^ (n + 1)) x = y := by
        rw [pow_succ', Homeomorph.mul_apply, hxz, hfz]
      refine ⟨x, hxn, ?_⟩
      intro k hk
      by_cases heq : k = n + 1
      · simpa only [heq, hxn] using hy
      · exact hxword k (by omega)
  intro n
  obtain ⟨y, hy⟩ := (hT n).1
  obtain ⟨x, -, hx⟩ := (hT n).2.2.2 y hy
  exact ⟨x, hx⟩

/-- Every finite TWO-sided legal strip is realized by the ORIGINAL map. Index the
forward word from −n to n, realize its 2n transitions, and move its starting point
forward n times. Integer/natural powers are reconciled explicitly. -/
private theorem realize_finite_legal_strip {N : ℕ}
    (F : X ≃ₜ X) (γ lam : ℝ) (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (R : Fin N → Set X) (hne : ∀ i, (R i).Nonempty) (hc : ∀ i, IsCompact (R i))
    (hd : ∀ i, Metric.diam (R i) ≤ H.closeRadius)
    (hsmall : ∀ i, 2 * Metric.diam (R i) ≤ γ)
    (hb : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, H.bracket p q ∈ R i)
    (hforward : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, dist (F p) (F q) ≤ γ)
    (hmarkov : ∀ i j x, x ∈ interior (R i) → F x ∈ interior (R j) →
      F '' (R i ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆
        R j ∩ Dynamics.relativeClosedStablePlaque F γ (F x) ∧
      R j ∩ Dynamics.relativeClosedUnstablePlaque F γ (F x) ⊆
        F '' (R i ∩ Dynamics.relativeClosedUnstablePlaque F γ x))
    (a : CodeSpace (transition F R)) (n : ℕ) :
    ∃ x : X, ∀ j : ℤ, |j| ≤ n → (F ^ j) x ∈ R (a.val j) := by
  let v : ℕ → Fin N := fun k ↦ a.val ((k : ℤ) - n)
  have hv : ∀ k, transition F R (v k) (v (k + 1)) := by
    intro k
    simpa [v, Nat.cast_add, sub_add_eq_add_sub] using a.property ((k : ℤ) - n)
  obtain ⟨x, hx⟩ := realize_finite_forward_word F γ lam H R hne hc hd hsmall hb
    hforward hmarkov v hv (2 * n)
  refine ⟨(F ^ n) x, ?_⟩
  intro j hj
  have hjbounds := abs_le.mp hj
  have hjn : 0 ≤ j + n := by omega
  let k : ℕ := (j + n).toNat
  have hkcast : (k : ℤ) = j + n := Int.toNat_of_nonneg hjn
  have hkle : k ≤ 2 * n := by omega
  have hmem := hx k hkle
  have hvk : v k = a.val j := by
    simp only [v, hkcast, add_sub_cancel_right]
  have hiterate : (F ^ j) ((F ^ n) x) = (F ^ k) x := by
    have hgroup : F ^ j * F ^ (n : ℤ) = F ^ (k : ℤ) := by
      rw [← zpow_add, ← hkcast]
    simpa only [Homeomorph.mul_apply, zpow_natCast] using congrArg (fun g : X ≃ₜ X ↦ g x) hgroup
  simpa only [hiterate, hvk] using hmem

/-- The remaining forward zero-time guard is supplied by compact uniform continuity,
not assumed in the final partition construction: choose one positive mesh radius before
selecting cells; diam<η forces their whole forward images to have pairwise distance<γ. -/
private theorem exists_forward_collar_radius (F : X ≃ₜ X) (γ : ℝ) (hγ : 0 < γ) :
    ∃ η : ℝ, 0 < η ∧ ∀ R : Set X, IsCompact R → Metric.diam R < η →
      ∀ p ∈ R, ∀ q ∈ R, dist (F p) (F q) ≤ γ := by
  have huc : UniformContinuous F :=
    CompactSpace.uniformContinuous_of_continuous F.continuous
  obtain ⟨η, hη, hηmap⟩ := Metric.uniformContinuous_iff.mp huc γ hγ
  refine ⟨η, hη, fun R hc hd p hp q hq ↦ ?_⟩
  exact (hηmap ((Metric.dist_le_diam_of_mem hc.isBounded hp hq).trans_lt hd)).le

/-- The original witnessed transitions retain both closed-overlap laws.
Source: Bowen (1970a), Lemma 25, pp. 739–740. -/
private def ClosedMarkovLaws {N : ℕ} (F : X ≃ₜ X) (γ : ℝ) (R : Fin N → Set X) : Prop :=
  ∀ i j, transition F R i j → ∀ x, x ∈ R i → F x ∈ R j →
    (F '' (R i ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆ R j) ∧
    (R j ∩ Dynamics.relativeClosedUnstablePlaque F γ (F x) ⊆
      F '' (R i ∩ Dynamics.relativeClosedUnstablePlaque F γ x))

/-- Bowen Lemmas25--27 applied to the actual proper-partition provider. All smallness
requirements are fixed BEFORE selecting the partition: close-pair radius, half γ,
and a compact-uniform-continuity forward collar. Thus finite-strip realization is
a conclusion, not an added assumption on the partition or on the main theorem.
Only this final existence statement inherits the named partition provider's proof
obligation; the closed-overlap and strip lemmas above have no admissions. -/
private theorem exists_proper_partition_realizing_legal_strips [Nonempty X]
    (F : X ≃ₜ X) (γ lam : ℝ) (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ R : Fin N → Set X,
      (∀ i, (R i).Nonempty ∧ IsCompact (R i) ∧ Metric.diam (R i) < ε ∧
        R i = closure (interior (R i)) ∧
        ∀ p ∈ R i, ∀ q ∈ R i, H.bracket p q ∈ R i) ∧
      (⋃ i, R i) = univ ∧
      (∀ i j, i ≠ j → Disjoint (interior (R i)) (interior (R j))) ∧
      (∀ i j x, x ∈ interior (R i) → F x ∈ interior (R j) →
        F '' (R i ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆
          R j ∩ Dynamics.relativeClosedStablePlaque F γ (F x) ∧
        R j ∩ Dynamics.relativeClosedUnstablePlaque F γ (F x) ⊆
          F '' (R i ∩ Dynamics.relativeClosedUnstablePlaque F γ x)) ∧
      ClosedMarkovLaws F γ R ∧
      ∀ (a : CodeSpace (transition F R)) (n : ℕ),
        ∃ x : X, ∀ j : ℤ, |j| ≤ n → (F ^ j) x ∈ R (a.val j) := by
  obtain ⟨η, hη, hηmap⟩ := exists_forward_collar_radius F γ H.gamma_pos
  let mesh := min ε (min H.closeRadius (min (γ / 2) η))
  have hmesh : 0 < mesh :=
    lt_min hε (lt_min H.closeRadius_pos (lt_min (by linarith [H.gamma_pos]) hη))
  obtain ⟨N, R, hR, hcover, hdisj, hmarkov⟩ :=
    Dynamics.Bowen.compactLocalProductProperPartition F γ lam H mesh hmesh
  have hN : 1 ≤ N := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hx : x ∈ ⋃ i, R i := hcover.symm ▸ mem_univ x
    obtain ⟨i, -⟩ := mem_iUnion.mp hx
    exact Nat.succ_le_of_lt (Nat.zero_lt_of_lt i.isLt)
  have hclose : ∀ i, Metric.diam (R i) ≤ H.closeRadius := by
    intro i
    exact (hR i).2.2.1.le.trans
      ((min_le_right ε _).trans (min_le_left H.closeRadius _))
  have hsmall : ∀ i, 2 * Metric.diam (R i) ≤ γ := by
    intro i
    have hi : Metric.diam (R i) ≤ γ / 2 :=
      (hR i).2.2.1.le.trans ((min_le_right ε _).trans
        ((min_le_right H.closeRadius _).trans (min_le_left (γ / 2) η)))
    linarith
  have hforward : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, dist (F p) (F q) ≤ γ := by
    intro i
    exact hηmap (R i) (hR i).2.1 ((hR i).2.2.1.trans_le
      ((min_le_right ε _).trans ((min_le_right H.closeRadius _).trans
        (min_le_right (γ / 2) η))))
  refine ⟨N, hN, R, ?_, hcover, hdisj, hmarkov, ?_, ?_⟩
  · intro i
    exact ⟨(hR i).1, (hR i).2.1,
      (hR i).2.2.1.trans_le (min_le_left ε _), (hR i).2.2.2⟩
  · intro i j hlegal x hx hfx
    obtain ⟨t, ⟨w, hw, rfl⟩, hfw⟩ := hlegal
    have hlaws := hmarkov i j w hw hfw
    have hzero : ∀ p ∈ R i, ∀ q ∈ R i, F p ∈ R j → F q ∈ R j →
        dist (F (H.bracket p q)) (F q) ≤ γ :=
      fun p hp q hq _ _ ↦ hforward i (H.bracket p q) ((hR i).2.2.2.2 p hp q hq) q hq
    constructor
    · exact (stable_inclusion_at_closed_overlap F γ lam H (R i) (R j)
        (hR i).2.1 (hR j).2.1 (hclose i) (hclose j)
        (hR i).2.2.2.2 (hR j).2.2.2.2 hzero w (interior_subset hw)
        (interior_subset hfw) hlaws.1 x hx hfx).trans inter_subset_left
    · exact unstable_cover_at_closed_overlap F γ lam H (R i) (R j)
        (hR i).2.1 (hR j).2.1 (hclose i) (hclose j) (hsmall j)
        (hR i).2.2.2.2 (hR j).2.2.2.2 hzero w (interior_subset hw)
        (interior_subset hfw) hlaws.2 x hx hfx
  · exact realize_finite_legal_strip F γ lam H R (fun i ↦ (hR i).1)
      (fun i ↦ (hR i).2.1) hclose hsmall (fun i ↦ (hR i).2.2.2.2)
      hforward hmarkov


/-- Actual coding factory application for the SAME chosen proper partition. The mesh
also controls the close bracket domain and the expansive radius. Finite legal words
are proved above, never supplied as an additional hypothesis. This supplies the whole
singleton-itinerary/continuity/onto/covariance/every-label block. The numerical splice
bound here is explicitly in the metric of H; the original-metric splice is transferred
separately below and is not silently identified with this adapted distance. -/
private theorem exists_canonical_partition_coding [Nonempty X]
    (F : X ≃ₜ X) (γ lam : ℝ) (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ R : Fin N → Set X,
      (∀ i, IsRectangle F dist γ (R i) ∧ Metric.diam (R i) < ε) ∧
      (∀ i j, i ≠ j → Disjoint (interior (R i)) (interior (R j))) ∧
      (⋃ i, R i) = univ ∧ HasMarkovInclusions F dist γ R ∧
      ClosedMarkovLaws F γ R ∧ ∃ coding : CodeSpace (transition F R) → X,
        (∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a}) ∧
        Continuous coding ∧ Function.Surjective coding ∧
        (∀ a, coding (codeShift (transition F R) a) = F (coding a)) ∧
        (∀ (x : X) (j : ℤ) (i : Fin N), (F ^ j) x ∈ R i ↔
          ∃ a : CodeSpace (transition F R), coding a = x ∧ a.val j = i) := by
  let mesh := min ε (min γ H.closeRadius)
  have hmesh : 0 < mesh := lt_min hε (lt_min H.gamma_pos H.closeRadius_pos)
  obtain ⟨N, hN, R, hR, hcover, hdisj, hmarkov, hclosed, hword⟩ :=
    exists_proper_partition_realizing_legal_strips F γ lam H mesh hmesh
  have hclose : ∀ i, Metric.diam (R i) ≤ H.closeRadius := by
    intro i
    exact (hR i).2.2.1.le.trans
      ((min_le_right ε _).trans (min_le_right γ H.closeRadius))
  have hdiam : ∀ i, Metric.diam (R i) ≤ γ := by
    intro i
    exact (hR i).2.2.1.le.trans
      ((min_le_right ε _).trans (min_le_left γ H.closeRadius))
  have hrect : ∀ i, IsRectangle F dist γ (R i) := by
    intro i
    refine ⟨(hR i).1, (hR i).2.1, (hR i).2.2.2.1, ?_⟩
    intro p hp q hq
    have hpq := (Metric.dist_le_diam_of_mem (hR i).2.1.isBounded hp hq).trans
      (hclose i)
    refine ⟨H.bracket p q, (hR i).2.2.2.2 p hp q hq, fun w ↦ ?_⟩
    simp only [localStable_eq_relative, localUnstable_eq_relative]
    constructor
    · exact H.bracket_unique p q w hpq
    · rintro rfl
      exact H.bracket_mem p q hpq
  have hsmall : ∀ i, Metric.diam (R i) < ε := fun i ↦
    (hR i).2.2.1.trans_le (min_le_left ε _)
  obtain ⟨coding, hit, hcont, honto, hcov, hlabels, -⟩ :=
    exists_coding_from_finite_word_realization F γ H.gamma_pos.le R hrect hdiam
      hcover hword ε hsmall
  refine ⟨N, hN, R, fun i ↦ ⟨hrect i, hsmall i⟩, hdisj, hcover, ?_, hclosed,
    coding, hit, hcont, honto, hcov, hlabels⟩
  intro i j x hx hfx
  simpa only [stableSlice, unstableSlice, localStable_eq_relative,
    localUnstable_eq_relative] using hmarkov i j x hx hfx

/-- On the actual compact space, every continuous original distance function vanishing
on the diagonal has a uniform positive adapted-mesh collar. This argument uses continuity
of that distance in the SAME topology, never equality with the current metric. -/
private theorem exists_continuous_diagonal_collar
    (d₀ : X → X → ℝ) (hcont : Continuous (fun p : X × X ↦ d₀ p.1 p.2))
    (hdiag : ∀ x, d₀ x x = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ p q : X, dist p q < η → d₀ p q < ε := by
  have huc := CompactSpace.uniformContinuous_of_continuous hcont
  obtain ⟨η, hη, hbound⟩ := Metric.uniformContinuous_iff.mp huc ε hε
  refine ⟨η, hη, fun p q hpq ↦ ?_⟩
  have hpair : dist (p, q) (p, p) < η := by
    simpa [Prod.dist_eq, dist_comm] using hpq
  have hb := hbound hpair
  rw [hdiag, Real.dist_eq, sub_zero] at hb
  exact (le_abs_self (d₀ p q)).trans_lt hb

omit [CompactSpace X] in
/-- The original-distance splice is controlled by original pairwise bounds on each
rectangle. This is separate from any adapted-distance splice output of the factory. -/
private theorem exists_spliced_code_original_distance {N : ℕ}
    (F : X ≃ₜ X) (R : Fin N → Set X) (coding : CodeSpace (transition F R) → X)
    (hit : ∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a})
    (d₀ : X → X → ℝ) (ε : ℝ)
    (hbound : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, d₀ p q < ε)
    (a b : CodeSpace (transition F R)) (hzero : a.val 0 = b.val 0) :
    ∃ c : CodeSpace (transition F R),
      (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
      (∀ j : ℤ, 0 ≤ j → c.val j = b.val j) ∧
      (∀ j : ℤ, 0 ≤ j → d₀ ((F ^ j) (coding c)) ((F ^ j) (coding b)) < ε) ∧
      (∀ j : ℤ, j ≤ 0 → d₀ ((F ^ j) (coding c)) ((F ^ j) (coding a)) < ε) := by
  obtain ⟨c, hcneg, hcpos⟩ := exists_spliced_code (transition F R) a b hzero
  refine ⟨c, hcneg, hcpos, ?_, ?_⟩
  · intro j hj
    have hc := coding_mem_rectangle F R coding hit c j
    rw [hcpos j hj] at hc
    exact hbound _ _ hc _ (coding_mem_rectangle F R coding hit b j)
  · intro j hj
    have hc := coding_mem_rectangle F R coding hit c j
    rw [hcneg j hj] at hc
    exact hbound _ _ hc _ (coding_mem_rectangle F R coding hit a j)

/-- The actual small-mesh selection supplies original-distance splice bounds. The
conclusion deliberately records original pairwise distance control separately from
the adapted rectangle structure; no equality of the two distances is an input. -/
private theorem exists_canonical_coding_with_original_splice [Nonempty X]
    (F : X ≃ₜ X) (γ lam : ℝ) (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (d₀ : X → X → ℝ) (hcont : Continuous (fun p : X × X ↦ d₀ p.1 p.2))
    (hdiag : ∀ x, d₀ x x = 0) (ε : ℝ) (hε : 0 < ε)
    (adaptedCutoff : ℝ) (hcutoff : 0 < adaptedCutoff) :
    ∃ N : ℕ, 1 ≤ N ∧ ∃ R : Fin N → Set X,
      (∀ i, IsRectangle F dist γ (R i)) ∧
      (∀ i, Metric.diam (R i) < adaptedCutoff) ∧
      (∀ i, ∀ p ∈ R i, ∀ q ∈ R i, d₀ p q < ε / 2) ∧
      (∀ i j, i ≠ j → Disjoint (interior (R i)) (interior (R j))) ∧
      (⋃ i, R i) = univ ∧ HasMarkovInclusions F dist γ R ∧
      ClosedMarkovLaws F γ R ∧ ∃ coding : CodeSpace (transition F R) → X,
        (∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a}) ∧
        Continuous coding ∧ Function.Surjective coding ∧
        (∀ a, coding (codeShift (transition F R) a) = F (coding a)) ∧
        (∀ (x : X) (j : ℤ) (i : Fin N), (F ^ j) x ∈ R i ↔
          ∃ a : CodeSpace (transition F R), coding a = x ∧ a.val j = i) ∧
        (∀ a b : CodeSpace (transition F R), a.val 0 = b.val 0 →
          ∃ c : CodeSpace (transition F R),
            (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
            (∀ j : ℤ, 0 ≤ j → c.val j = b.val j) ∧
            (∀ j : ℤ, 0 ≤ j →
              d₀ ((F ^ j) (coding c)) ((F ^ j) (coding b)) < ε) ∧
            (∀ j : ℤ, j ≤ 0 →
              d₀ ((F ^ j) (coding c)) ((F ^ j) (coding a)) < ε)) := by
  obtain ⟨η, hη, hηmap⟩ := exists_continuous_diagonal_collar d₀ hcont hdiag
    (ε / 2) (by linarith)
  obtain ⟨N, hN, R, hR, hdisj, hcover, hmarkov, hclosed, coding, hit, hcc, honto,
    hcov, hlabels⟩ := exists_canonical_partition_coding F γ lam H
      (min η adaptedCutoff) (lt_min hη hcutoff)
  have hbound : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, d₀ p q < ε / 2 := by
    intro i p hp q hq
    exact hηmap p q ((Metric.dist_le_diam_of_mem (hR i).1.2.1.isBounded hp hq).trans_lt
      ((hR i).2.trans_le (min_le_left _ _)))
  refine ⟨N, hN, R, fun i ↦ (hR i).1,
    fun i ↦ (hR i).2.trans_le (min_le_right _ _), hbound, hdisj, hcover, hmarkov, hclosed,
    coding, hit, hcc, honto, hcov, hlabels, ?_⟩
  intro a b hzero
  exact exists_spliced_code_original_distance F R coding hit d₀ ε
    (fun i p hp q hq ↦ (hbound i p hp q hq).trans (by linarith)) a b hzero

omit [CompactSpace X] in
/-- Proper cells with disjoint interiors meet only in their actual frontiers.
The regular-closed premise is used on BOTH cells, not inferred from compactness. -/
theorem proper_cells_intersection_subset_frontiers
    (E T : Set X) (hE : E = closure (interior E))
    (hT : T = closure (interior T)) (hd : Disjoint (interior E) (interior T)) :
    E ∩ T ⊆ frontier E ∩ frontier T := by
  intro x hx
  constructor
  · apply (mem_frontier_iff_notMem_interior hx.1).mpr
    intro hi
    have ht : x ∈ closure (interior T) := hT ▸ hx.2
    exact Set.disjoint_left.mp (hd.closure_right isOpen_interior) hi ht
  · apply (mem_frontier_iff_notMem_interior hx.2).mpr
    intro hi
    have he : x ∈ closure (interior E) := hE ▸ hx.1
    exact Set.disjoint_left.mp (hd.closure_left isOpen_interior) he hi

/-- Bowen1970b Lemma6(b)'s first actual geometric deduction. Two witnessed
predecessor cells at x force the entire inverse target unstable slice into BOTH
source frontiers. This uses the proved closed-overlap covering, including boundary
points. Converting this to the directional unstable boundary still requires the
relative-plaque product and boundary-avoidance steps, not an ambient-frontier shortcut. -/
private theorem merged_predecessors_force_frontier_slice {N : ℕ}
    (F : X ≃ₜ X) (γ lam : ℝ) (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (R : Fin N → Set X) (hc : ∀ i, IsCompact (R i))
    (hd : ∀ i, Metric.diam (R i) ≤ H.closeRadius)
    (hsmall : ∀ i, 2 * Metric.diam (R i) ≤ γ)
    (hb : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, H.bracket p q ∈ R i)
    (hforward : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, dist (F p) (F q) ≤ γ)
    (hproper : ∀ i, R i = closure (interior (R i)))
    (hdisj : ∀ i j, i ≠ j → Disjoint (interior (R i)) (interior (R j)))
    (hmarkov : ∀ i j x, x ∈ interior (R i) → F x ∈ interior (R j) →
      F '' (R i ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆
        R j ∩ Dynamics.relativeClosedStablePlaque F γ (F x) ∧
      R j ∩ Dynamics.relativeClosedUnstablePlaque F γ (F x) ⊆
        F '' (R i ∩ Dynamics.relativeClosedUnstablePlaque F γ x))
    (i₁ i₂ j : Fin N) (hne : i₁ ≠ i₂)
    (hlegal₁ : transition F R i₁ j) (hlegal₂ : transition F R i₂ j)
    (x : X) (hx₁ : x ∈ R i₁) (hx₂ : x ∈ R i₂) (hfx : F x ∈ R j) :
    F.symm '' (R j ∩ Dynamics.relativeClosedUnstablePlaque F γ (F x)) ⊆
      frontier (R i₁) ∩ frontier (R i₂) := by
  have hcover : ∀ i, transition F R i j → x ∈ R i →
      R j ∩ Dynamics.relativeClosedUnstablePlaque F γ (F x) ⊆
        F '' (R i ∩ Dynamics.relativeClosedUnstablePlaque F γ x) := by
    intro i hi hxi
    obtain ⟨_, ⟨w, hw, rfl⟩, hfw⟩ := hi
    have hzero : ∀ p ∈ R i, ∀ q ∈ R i, F p ∈ R j → F q ∈ R j →
        dist (F (H.bracket p q)) (F q) ≤ γ := by
      intro p hp q hq _ _
      exact hforward i _ (hb i p hp q hq) q hq
    exact unstable_cover_at_closed_overlap F γ lam H (R i) (R j) (hc i) (hc j)
      (hd i) (hd j) (hsmall j) (hb i) (hb j) hzero w (interior_subset hw)
      (interior_subset hfw) (hmarkov i j w hw hfw).2 x hxi hfx
  intro y hy
  obtain ⟨t, ht, rfl⟩ := hy
  have hpre : ∀ i, transition F R i j → x ∈ R i → F.symm t ∈ R i := by
    intro i hi hxi
    obtain ⟨z, hz, hzt⟩ := hcover i hi hxi ht
    have heq : z = F.symm t := (F.eq_symm_apply).mpr hzt
    simpa only [← heq] using hz.1
  exact proper_cells_intersection_subset_frontiers (R i₁) (R i₂)
    (hproper i₁) (hproper i₂) (hdisj i₁ i₂ hne)
    ⟨hpre i₁ hlegal₁ hx₁, hpre i₂ hlegal₂ hx₂⟩

omit [MetricSpace X] [CompactSpace X] in
/-- The local product algebra behind Bowen1970b Lemma6(b). If the unstable
factors have a common open subset while the product interiors are disjoint, each
common stable coordinate is on the first stable-factor frontier. The second
factor's regular-closedness is essential to approximate that coordinate from its
interior; an ambient frontier alone is insufficient. -/
private theorem product_merge_forces_factor_frontier
    {U S : Type*} [TopologicalSpace U] [TopologicalSpace S]
    (C₁ C₂ : Set U) (D₁ D₂ : Set S)
    (hregular₂ : D₂ = closure (interior D₂))
    (hdisj : Disjoint (interior (C₁ ×ˢ D₁)) (interior (C₂ ×ˢ D₂)))
    (hcommon : (interior (C₁ ∩ C₂)).Nonempty)
    {s : S} (hs₁ : s ∈ D₁) (hs₂ : s ∈ D₂) : s ∈ frontier D₁ := by
  apply (mem_frontier_iff_notMem_interior hs₁).mpr
  intro hsint
  have hscl : s ∈ closure (interior D₂) := hregular₂ ▸ hs₂
  obtain ⟨t, ht₁, ht₂⟩ := mem_closure_iff.mp hscl (interior D₁)
    isOpen_interior hsint
  obtain ⟨u, hu⟩ := hcommon
  have hu₁ : u ∈ interior C₁ := interior_mono inter_subset_left hu
  have hu₂ : u ∈ interior C₂ := interior_mono inter_subset_right hu
  have hp₁ : (u, t) ∈ interior (C₁ ×ˢ D₁) := by
    simpa only [interior_prod_eq, mem_prod] using And.intro hu₁ ht₁
  have hp₂ : (u, t) ∈ interior (C₂ ×ˢ D₂) := by
    simpa only [interior_prod_eq, mem_prod] using And.intro hu₂ ht₂
  exact Set.disjoint_left.mp hdisj hp₁ hp₂

omit [MetricSpace X] [CompactSpace X] in
/-- Exact finite predecessor-label injection in a single actual product chart.
A common unstable open core is contained in every candidate predecessor factor.
Away from their stable-factor frontiers, at most one predecessor label survives.
The geometric caller must supply the common-core inclusion from closed-overlap
covering and the SAME local plaque chart; this theorem assumes no global coding
fibre bound and adds no hypothesis to the main theorem. -/
private theorem product_predecessor_labels_subsingleton
    {U S : Type*} [TopologicalSpace U] [TopologicalSpace S] {N : ℕ}
    (C : Fin N → Set U) (D : Fin N → Set S) (V : Set U)
    (hV : (interior V).Nonempty)
    (hregular : ∀ i, D i = closure (interior (D i)))
    (hdisj : ∀ i j, i ≠ j →
      Disjoint (interior (C i ×ˢ D i)) (interior (C j ×ˢ D j)))
    (s : S) (hboundary : ∀ i, s ∉ frontier (D i)) :
    {i : Fin N | s ∈ D i ∧ V ⊆ C i}.Subsingleton := by
  intro i hi j hj
  by_contra hne
  have hcommon : (interior (C i ∩ C j)).Nonempty := by
    apply hV.mono
    exact interior_mono fun u hu ↦ ⟨hi.2 hu, hj.2 hu⟩
  exact hboundary i (product_merge_forces_factor_frontier (C i) (C j)
    (D i) (D j) (hregular j) (hdisj i j hne) hcommon hi.1 hj.1)

omit [CompactSpace X] in
/-- Bowen1970b p.908: finitely many actual label-membership patterns stabilize
near a point. Every sufficiently close representative in G already realizes a
pattern occurring arbitrarily close to x in G. For the stable-pattern application
G is the original stable plaque minus its directional boundary set; no density
or boundary-avoidance premise is inferred by this finite argument. -/
private theorem membership_patterns_eventually_recurrent {N : ℕ}
    (R : Fin N → Set X) (G : Set X) (x : X) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : X, dist z x < δ → z ∈ G →
      x ∈ closure {w : X | w ∈ G ∧ {i : Fin N | w ∈ R i} = {i | z ∈ R i}} := by
  classical
  have hpattern : ∀ P : Set (Fin N), ∀ᶠ z in 𝓝 x,
      z ∈ G → {i : Fin N | z ∈ R i} = P →
        x ∈ closure {w : X | w ∈ G ∧ {i : Fin N | w ∈ R i} = P} := by
    intro P
    by_cases hx : x ∈ closure {w : X | w ∈ G ∧ {i : Fin N | w ∈ R i} = P}
    · exact Filter.Eventually.of_forall fun _ _ _ ↦ hx
    · have hn : (closure {w : X | w ∈ G ∧ {i : Fin N | w ∈ R i} = P})ᶜ ∈
          𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hx
      filter_upwards [hn] with z hz hzG hzP
      exact False.elim (hz (subset_closure ⟨hzG, hzP⟩))
  have hall : ∀ᶠ z in 𝓝 x, ∀ P : Set (Fin N), z ∈ G →
      {i : Fin N | z ∈ R i} = P →
        x ∈ closure {w : X | w ∈ G ∧ {i : Fin N | w ∈ R i} = P} :=
    Filter.eventually_all.mpr hpattern
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hall
  exact ⟨δ, hδ, fun z hz hzG ↦ hball hz {i | z ∈ R i} hzG rfl⟩


end FiniteStrips

end SymbolicMetric

section FiniteFibreRanks

open Function

/-- A monotone natural rank cannot strictly drop twice from the same level.
If m<n, monotonicity gives rank n≤rank(m+1)<rank m. -/
private theorem strict_drop_rank_injective (r : ℕ → ℕ) (hr : Antitone r) :
    Set.InjOn r {n | r (n + 1) < r n} := by
  intro m hm n hn heq
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have h := hr (Nat.succ_le_of_lt hmn)
    change r n ≤ r (m + 1) at h
    change r (m + 1) < r m at hm
    omega
  · exact hmn
  · have h := hr (Nat.succ_le_of_lt hnm)
    change r m ≤ r (n + 1) at h
    change r (n + 1) < r n at hn
    omega

/-- Actual finite records for a family of half-codes whose branch times force
a rank drop. The chosen times depend only on the common physical orbit rank,
never on an individual code; agreement of records therefore gives injectivity.
Source: Bowen (1970b), Proposition 10, p. 913. -/
private theorem half_code_rank_records {N K : ℕ} (r : ℕ → ℕ)
    (hr : Antitone r) (hK : r 0 ≤ K) (S : Set (ℕ → Fin N))
    (hbranch : ∀ a ∈ S, ∀ b ∈ S, ∀ n, a n = b n → a (n + 1) ≠ b (n + 1) →
      r (n + 1) < r n) :
    ∃ record : (ℕ → Fin N) → (Fin (K + 1) → Fin N),
      ∀ a ∈ S, ∀ b ∈ S, a 0 = b 0 → record a = record b → a = b := by
  classical
  let time : Fin (K + 1) → ℕ := fun k ↦
    if h : ∃ n, r n = k.val ∧ r (n + 1) < r n then Classical.choose h else 0
  have htime : ∀ n, r (n + 1) < r n →
      time ⟨r n, Nat.lt_succ_of_le ((hr (Nat.zero_le n)).trans hK)⟩ = n := by
    intro n hn
    have hex : ∃ m, r m = r n ∧ r (m + 1) < r m := ⟨n, rfl, hn⟩
    simp only [time, dite_eq_left hex]
    exact strict_drop_rank_injective r hr (Classical.choose_spec hex).2 hn
      (Classical.choose_spec hex).1
  let record : (ℕ → Fin N) → (Fin (K + 1) → Fin N) :=
    fun a k ↦ a (time k + 1)
  refine ⟨record, ?_⟩
  intro a ha b hb hzero hrecord
  funext n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    by_contra hne
    have hn := hbranch a ha b hb n ih hne
    have he := congrFun hrecord ⟨r n, Nat.lt_succ_of_le ((hr (Nat.zero_le n)).trans hK)⟩
    change a (time _ + 1) = b (time _ + 1) at he
    rw [htime n hn] at he
    exact hne he

/-- Uniform fibre cardinality from the two actual branch ranks. Forward and
backward half-codes have at most K+1 rank records each, with one common zero
symbol. Their combined record takes values in a finite type of size
N·(N^(K+1)·N^(K+1)), independently of the physical point.
Source: Bowen (1970b), Proposition 10, p. 913. -/
private theorem two_sided_codes_encard_of_branch_ranks {N K : ℕ}
    (S : Set (ℤ → Fin N)) (rs ru : ℕ → ℕ)
    (hrs : Antitone rs) (hru : Antitone ru) (hsK : rs 0 ≤ K) (huK : ru 0 ≤ K)
    (hforward : ∀ a ∈ S, ∀ b ∈ S, ∀ n : ℕ,
      a n = b n → a ((n : ℤ) + 1) ≠ b ((n : ℤ) + 1) → rs (n + 1) < rs n)
    (hbackward : ∀ a ∈ S, ∀ b ∈ S, ∀ n : ℕ,
      a (-(n : ℤ)) = b (-(n : ℤ)) →
      a (-((n : ℤ) + 1)) ≠ b (-((n : ℤ) + 1)) → ru (n + 1) < ru n) :
    S.encard ≤ (N * (N ^ (K + 1) * N ^ (K + 1)) : ℕ) := by
  let positive : (ℤ → Fin N) → (ℕ → Fin N) := fun a n ↦ a n
  let negative : (ℤ → Fin N) → (ℕ → Fin N) := fun a n ↦ a (-(n : ℤ))
  obtain ⟨p, hp⟩ := half_code_rank_records rs hrs hsK (positive '' S) (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ n he hn
    exact hforward a ha b hb n he (by simpa [positive] using hn))
  obtain ⟨q, hq⟩ := half_code_rank_records ru hru huK (negative '' S) (by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ n he hn
    exact hbackward a ha b hb n he (by simpa [negative] using hn))
  let record : (ℤ → Fin N) →
      Fin N × ((Fin (K + 1) → Fin N) × (Fin (K + 1) → Fin N)) :=
    fun a ↦ (a 0, p (positive a), q (negative a))
  have hinj : Set.InjOn record S := by
    intro a ha b hb he
    have hzero : a 0 = b 0 := congrArg Prod.fst he
    have hpos : positive a = positive b :=
      hp _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hzero (congrArg (fun z ↦ z.2.1) he)
    have hneg : negative a = negative b :=
      hq _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ (by simpa [negative] using hzero)
        (congrArg (fun z ↦ z.2.2) he)
    funext j
    rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
    · exact congrFun hpos n
    · exact congrFun hneg n
  have hcard := Set.encard_le_encard_of_injOn
    (show Set.MapsTo record S Set.univ from fun _ _ ↦ trivial) hinj
  simpa only [Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_prod,
    Fintype.card_fun, Fintype.card_fin] using hcard


/-- A positive period forbids any strict step of a monotone integer-time
rank: rank(j+m)≤rank(j+1)≤rank(j), and periodicity identifies the endpoints.
Source: Bowen (1970b), Proposition 12, p. 914. -/
private theorem periodic_antitone_rank_step_eq (r : ℤ → ℕ)
    (hr : ∀ j, r (j + 1) ≤ r j) (m : ℕ) (hm : 0 < m)
    (hperiod : ∀ j, r (j + m) = r j) : ∀ j, r (j + 1) = r j := by
  intro j
  apply Nat.le_antisymm (hr j)
  have h := antitone_int_of_succ_le hr (show j + 1 ≤ j + m by omega)
  rw [hperiod] at h
  exact h

/-- Coordinate rigidity follows from the forward and backward branch-rank
rules on a periodic physical orbit. Both ranks are constant along the orbit,
so agreement at one coordinate propagates in both directions. No assertion
about nonperiodic coordinate rigidity is made.
Source: Bowen (1970b), Proposition 12, p. 914. -/
private theorem periodic_rank_coordinate_rigidity {N : ℕ}
    (S : Set (ℤ → Fin N)) (rs ru : ℤ → ℕ)
    (hrs : ∀ j, rs (j + 1) ≤ rs j) (hru : ∀ j, ru (j - 1) ≤ ru j)
    (m : ℕ) (hm : 0 < m)
    (hps : ∀ j, rs (j + m) = rs j) (hpu : ∀ j, ru (j - m) = ru j)
    (hforward : ∀ a ∈ S, ∀ b ∈ S, ∀ j,
      a j = b j → a (j + 1) ≠ b (j + 1) → rs (j + 1) < rs j)
    (hbackward : ∀ a ∈ S, ∀ b ∈ S, ∀ j,
      a j = b j → a (j - 1) ≠ b (j - 1) → ru (j - 1) < ru j) :
    ∀ a ∈ S, ∀ b ∈ S, (∃ j, a j = b j) → a = b := by
  have hs := periodic_antitone_rank_step_eq rs hrs m hm hps
  have hu : ∀ j, ru (j - 1) = ru j := by
    have he := periodic_antitone_rank_step_eq (fun j ↦ ru (-j))
      (fun j ↦ by simpa [neg_add, sub_eq_add_neg, add_comm] using hru (-j)) m hm
      (fun j ↦ by simpa [neg_add, sub_eq_add_neg, add_comm] using hpu (-j))
    intro j
    simpa [neg_add, sub_eq_add_neg, add_comm] using he (-j)
  intro a ha b hb ⟨j, hj⟩
  have hf : ∀ k, a k = b k → a (k + 1) = b (k + 1) := by
    intro k hk
    by_contra hn
    have h := hforward a ha b hb k hk hn
    rw [hs k] at h
    exact (lt_irrefl _ h)
  have hb' : ∀ k, a k = b k → a (k - 1) = b (k - 1) := by
    intro k hk
    by_contra hn
    have h := hbackward a ha b hb k hk hn
    rw [hu k] at h
    exact (lt_irrefl _ h)
  have hall : ∀ k : ℤ, a (j + k) = b (j + k) := by
    intro k
    induction k using Int.induction_on with
    | zero => simpa using hj
    | succ n ih => simpa [add_assoc] using hf (j + n) ih
    | pred n ih =>
      simpa [sub_eq_add_neg, add_assoc, neg_add, add_comm, add_left_comm]
        using hb' (j + -(n : ℤ)) ih
  funext k
  simpa using hall (k - j)


/-- Reindex the same legal code by any integer time. Legality is reindexing
of its adjacent transition condition, including negative times. -/
private def translateLegalCode {N : ℕ} (B : Fin N → Fin N → Prop)
    (j : ℤ) (a : CodeSpace B) : CodeSpace B :=
  ⟨fun n ↦ a.val (j + n), fun n ↦ by simpa [add_assoc] using a.property (j + n)⟩

/-- Singleton itineraries identify the point coded by every integer translate.
This uses the original homeomorphism group law, with no extra covariance input. -/
private theorem translateLegalCode_coding {X : Type*} [TopologicalSpace X] {N : ℕ}
    (F : X ≃ₜ X) (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X)
    (hit : ∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a})
    (j : ℤ) (a : CodeSpace B) :
    coding (translateLegalCode B j a) = (F ^ j) (coding a) := by
  have ha : ∀ n : ℤ, (F ^ n) (coding a) ∈ R (a.val n) := by
    have h : coding a ∈ ({coding a} : Set X) := mem_singleton _
    rw [← hit a] at h
    exact h
  have h : (F ^ j) (coding a) ∈ {x : X |
      ∀ n : ℤ, (F ^ n) x ∈ R ((translateLegalCode B j a).val n)} := by
    intro n
    have h := ha (n + j)
    rw [zpow_add, Homeomorph.mul_apply] at h
    simpa only [translateLegalCode, add_comm n j] using h
  rw [hit] at h
  exact h.symm

/-- The abstract rank mechanism applied to actual singleton-itinerary coding.
The only extra inputs are bounded ranks on physical points, monotonicity, and
strict decrease at an actual one-step code branch. Integer translation derives
all orbit branch rules, then the finite records bound the entire fibre and
periodicity gives coordinate rigidity.
Source: Bowen (1970b), Propositions 9–12, pp. 912–914. -/
private theorem coding_fibres_and_rigidity_of_physical_ranks
    {X : Type*} [TopologicalSpace X] {N K : ℕ}
    (F : X ≃ₜ X) (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X)
    (hit : ∀ a, {x : X | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a})
    (rs ru : X → ℕ) (hKs : ∀ x, rs x ≤ K) (hKu : ∀ x, ru x ≤ K)
    (hms : ∀ x, rs (F x) ≤ rs x) (hmu : ∀ x, ru (F.symm x) ≤ ru x)
    (hbs : ∀ x a b, coding a = x → coding b = x → a.val 0 = b.val 0 →
      a.val 1 ≠ b.val 1 → rs (F x) < rs x)
    (hbu : ∀ x a b, coding a = x → coding b = x → a.val 0 = b.val 0 →
      a.val (-1) ≠ b.val (-1) → ru (F.symm x) < ru x) :
    (∀ x, {a : CodeSpace B | coding a = x}.encard ≤
      (N * (N ^ (K + 1) * N ^ (K + 1)) : ℕ)) ∧
    (∀ x, (∃ m : ℕ, 0 < m ∧ (F ^ m) x = x) →
      ∀ a b : CodeSpace B, coding a = x → coding b = x →
        (∃ j : ℤ, a.val j = b.val j) → a = b) := by
  classical
  have hnext : ∀ (j : ℤ) x, (F ^ (j + 1)) x = F ((F ^ j) x) := by
    intro j x
    rw [add_comm j 1, zpow_add, zpow_one, Homeomorph.mul_apply]
  have hprev : ∀ (j : ℤ) x, (F ^ (j - 1)) x = F.symm ((F ^ j) x) := by
    intro j x
    rw [sub_eq_add_neg, add_comm j (-1), zpow_add, Homeomorph.mul_apply]
    simp
  have hforward : ∀ x a b, coding a = x → coding b = x → ∀ j : ℤ,
      a.val j = b.val j → a.val (j + 1) ≠ b.val (j + 1) →
        rs ((F ^ (j + 1)) x) < rs ((F ^ j) x) := by
    intro x a b ha hb j he hn
    rw [hnext]
    apply hbs _ (translateLegalCode B j a) (translateLegalCode B j b)
    · rw [translateLegalCode_coding F B R coding hit, ha]
    · rw [translateLegalCode_coding F B R coding hit, hb]
    · simpa [translateLegalCode] using he
    · exact hn
  have hbackward : ∀ x a b, coding a = x → coding b = x → ∀ j : ℤ,
      a.val j = b.val j → a.val (j - 1) ≠ b.val (j - 1) →
        ru ((F ^ (j - 1)) x) < ru ((F ^ j) x) := by
    intro x a b ha hb j he hn
    rw [hprev]
    apply hbu _ (translateLegalCode B j a) (translateLegalCode B j b)
    · rw [translateLegalCode_coding F B R coding hit, ha]
    · rw [translateLegalCode_coding F B R coding hit, hb]
    · simpa [translateLegalCode] using he
    · exact hn
  constructor
  · intro x
    let S : Set (ℤ → Fin N) := Subtype.val '' {a : CodeSpace B | coding a = x}
    have hsanti : Antitone (fun n : ℕ ↦ rs ((F ^ (n : ℤ)) x)) := by
      apply antitone_nat_of_succ_le
      intro n
      simpa only [Nat.cast_add, Nat.cast_one, hnext] using hms ((F ^ (n : ℤ)) x)
    have huanti : Antitone (fun n : ℕ ↦ ru ((F ^ (-(n : ℤ))) x)) := by
      apply antitone_nat_of_succ_le
      intro n
      simpa only [Nat.cast_add, Nat.cast_one, neg_add, ← sub_eq_add_neg, hprev]
        using hmu ((F ^ (-(n : ℤ))) x)
    have hcard := two_sided_codes_encard_of_branch_ranks (K := K) S
      (fun n ↦ rs ((F ^ (n : ℤ)) x)) (fun n ↦ ru ((F ^ (-(n : ℤ))) x))
      hsanti huanti (by simpa using hKs x) (by simpa using hKu x) (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ n he hn
        simpa using hforward x a b ha hb n he hn) (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ n he hn
        have h := hbackward x a b ha hb (-(n : ℤ)) he
          (by simpa [neg_add, sub_eq_add_neg, add_comm] using hn)
        simpa [neg_add, sub_eq_add_neg, add_comm] using h)
    rwa [Subtype.val_injective.encard_image] at hcard
  · intro x ⟨m, hm, hx⟩ a b ha hb he
    let S : Set (ℤ → Fin N) := Subtype.val '' {a : CodeSpace B | coding a = x}
    apply Subtype.ext
    apply periodic_rank_coordinate_rigidity S
      (fun j ↦ rs ((F ^ j) x)) (fun j ↦ ru ((F ^ j) x))
      (fun j ↦ by simpa only [hnext] using hms ((F ^ j) x))
      (fun j ↦ by simpa only [hprev] using hmu ((F ^ j) x)) m hm
    · intro j
      simp only [zpow_add, zpow_natCast, Homeomorph.mul_apply, hx]
    · intro j
      have hinv : (F ^ (-(m : ℤ))) x = x := by
        apply (F ^ (m : ℤ)).injective
        simp [zpow_neg, hx]
      simp only [sub_eq_add_neg, zpow_add, Homeomorph.mul_apply, hinv]
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ j hj hn
      exact hforward x c d hc hd j hj hn
    · rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩ j hj hn
      exact hbackward x c d hc hd j hj hn
    · exact ⟨a, ha, rfl⟩
    · exact ⟨b, hb, rfl⟩
    · exact he


end FiniteFibreRanks

section NativePatternRanks

open Function

/-- Lemma7's existence half uses the ACTUAL every-label code over Fx. The
negative-one coordinate is a predecessor of the requested receiving label;
the singleton itinerary and original inverse map force it to contain x.
No pre-existing finite fibre or unique-predecessor premise is used here. -/
private theorem actual_code_gives_predecessor
    {X : Type*} [TopologicalSpace X] {N : ℕ}
    (F : X ≃ₜ X) (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X)
    (hcode : ∀ a, {y : X | ∀ n : ℤ, (F ^ n) y ∈ R (a.val n)} = {coding a})
    (hlabel : ∀ i x, x ∈ R i → ∃ a : CodeSpace B, coding a = x ∧ a.val 0 = i)
    (x : X) (j : Fin N) (hj : F x ∈ R j) :
    ∃ i : Fin N, x ∈ R i ∧ B i j := by
  obtain ⟨a, ha, haj⟩ := hlabel j (F x) hj
  have hit : ∀ n : ℤ, (F ^ n) (F x) ∈ R (a.val n) := by
    have hm : coding a ∈ ({coding a} : Set X) := mem_singleton _
    rw [← hcode a] at hm
    simpa only [ha, Set.mem_ofPred_eq] using hm
  refine ⟨a.val (-1), ?_, ?_⟩
  · simpa using hit (-1)
  · simpa only [neg_add_cancel, haj] using a.property (-1)

/-- The every-label code over x supplies an actual successor. Together with
the preceding existence and geometrically proved predecessor uniqueness this
makes T_z onto, as in Bowen1970b Lemma7. -/
private theorem actual_code_gives_successor
    {X : Type*} [TopologicalSpace X] {N : ℕ}
    (F : X ≃ₜ X) (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X)
    (hcode : ∀ a, {y : X | ∀ n : ℤ, (F ^ n) y ∈ R (a.val n)} = {coding a})
    (hlabel : ∀ i x, x ∈ R i → ∃ a : CodeSpace B, coding a = x ∧ a.val 0 = i)
    (x : X) (i : Fin N) (hi : x ∈ R i) :
    ∃ j : Fin N, F x ∈ R j ∧ B i j := by
  obtain ⟨a, ha, hai⟩ := hlabel i x hi
  have hit : ∀ n : ℤ, (F ^ n) x ∈ R (a.val n) := by
    have hm : coding a ∈ ({coding a} : Set X) := mem_singleton _
    rw [← hcode a] at hm
    simpa only [ha, Set.mem_ofPred_eq] using hm
  refine ⟨a.val 1, ?_, ?_⟩
  · simpa using hit 1
  · simpa only [hai, zero_add] using a.property 0

/-- Lemma7's stable transport of actual membership patterns. This uses the
entire CLOSED stable-slice law at witnessed transitions, the actual every-label
coding conclusion and the SAME local stable relation. It does not assume
boundary avoidance to substitute for any of these geometric facts. -/
private theorem same_stable_pattern_same_forward_pattern
    {X : Type*} [MetricSpace X] {N : ℕ}
    (F : X ≃ₜ X) (γ : ℝ) (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X)
    (hcode : ∀ a, {y : X | ∀ n : ℤ, (F ^ n) y ∈ R (a.val n)} = {coding a})
    (hlabel : ∀ i x, x ∈ R i → ∃ a : CodeSpace B, coding a = x ∧ a.val 0 = i)
    (hclosed : ∀ i j, B i j → ∀ x, x ∈ R i → F x ∈ R j →
      F '' (R i ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆ R j)
    (x y : X) (hstable : y ∈ Dynamics.relativeClosedStablePlaque F γ x)
    (hpattern : {i : Fin N | x ∈ R i} = {i | y ∈ R i}) :
    {j : Fin N | F x ∈ R j} = {j | F y ∈ R j} := by
  have hreverse : x ∈ Dynamics.relativeClosedStablePlaque F γ y :=
    fun n ↦ by simpa only [dist_comm] using hstable n
  have hmem : ∀ i, x ∈ R i ↔ y ∈ R i := fun i ↦ Set.ext_iff.mp hpattern i
  ext j
  constructor
  · intro hj
    obtain ⟨i, hxi, hij⟩ := actual_code_gives_predecessor F B R coding hcode hlabel x j hj
    exact hclosed i j hij x hxi hj ⟨y, ⟨(hmem i).mp hxi, hstable⟩, rfl⟩
  · intro hj
    obtain ⟨i, hyi, hij⟩ := actual_code_gives_predecessor F B R coding hcode hlabel y j hj
    exact hclosed i j hij y hyi hj ⟨x, ⟨(hmem i).mpr hyi, hreverse⟩, rfl⟩

/-- The actual T_z of Lemma7 is a surjection between the two literal membership
sets. Its only uniqueness input is the geometrically obtained predecessor-label
subsingleton condition at z, which is strictly weaker than any coding-fibre
bound. Every-label codes construct both existence and surjectivity. -/
private theorem exists_surjective_actual_predecessor_map
    {X : Type*} [TopologicalSpace X] {N : ℕ}
    (F : X ≃ₜ X) (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X)
    (hcode : ∀ a, {y : X | ∀ n : ℤ, (F ^ n) y ∈ R (a.val n)} = {coding a})
    (hlabel : ∀ i x, x ∈ R i → ∃ a : CodeSpace B, coding a = x ∧ a.val 0 = i)
    (x : X)
    (hunique : ∀ j : Fin N, F x ∈ R j → {i : Fin N | x ∈ R i ∧ B i j}.Subsingleton) :
    ∃ t : {j : Fin N | F x ∈ R j} → {i : Fin N | x ∈ R i},
      Surjective t ∧ ∀ j, B (t j).val j.val := by
  classical
  have hex : ∀ j : {j : Fin N | F x ∈ R j},
      ∃ i : {i : Fin N | x ∈ R i}, B i.val j.val := by
    intro j
    obtain ⟨i, hi, hij⟩ :=
      actual_code_gives_predecessor F B R coding hcode hlabel x j.val j.property
    exact ⟨⟨i, hi⟩, hij⟩
  choose t ht using hex
  refine ⟨t, ?_, ht⟩
  intro i
  obtain ⟨j, hj, hij⟩ :=
    actual_code_gives_successor F B R coding hcode hlabel x i.val i.property
  refine ⟨⟨j, hj⟩, ?_⟩
  apply Subtype.ext
  exact hunique j hj ⟨(t ⟨j, hj⟩).property, ht ⟨j, hj⟩⟩ ⟨i.property, hij⟩


/-- An ACTUAL one-step symbolic branch produces the collision used in
Proposition9 at every point z of its closed stable slice. The two receiving
labels come from two codes over the SAME x, with equal zero labels and distinct
one labels; the entire closed stable laws keep BOTH labels at Fz. Geometric
predecessor uniqueness at z identifies them under the constructed onto map.
The resulting strict cardinality is a conclusion, not an input. -/
private theorem actual_branch_stable_slice_strict_label_cardinality
    {X : Type*} [MetricSpace X] {N : ℕ}
    (F : X ≃ₜ X) (γ : ℝ) (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X)
    (hcode : ∀ a, {y : X | ∀ n : ℤ, (F ^ n) y ∈ R (a.val n)} = {coding a})
    (hlabel : ∀ i x, x ∈ R i → ∃ a : CodeSpace B, coding a = x ∧ a.val 0 = i)
    (hclosed : ∀ i j, B i j → ∀ x, x ∈ R i → F x ∈ R j →
      F '' (R i ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆ R j)
    (x z : X) (a b : CodeSpace B) (ha : coding a = x) (hb : coding b = x)
    (hzero : a.val 0 = b.val 0) (hbranch : a.val 1 ≠ b.val 1)
    (hz : z ∈ R (a.val 0) ∩ Dynamics.relativeClosedStablePlaque F γ x)
    (hunique : ∀ j : Fin N, F z ∈ R j → {i : Fin N | z ∈ R i ∧ B i j}.Subsingleton) :
    Nat.card {i : Fin N | z ∈ R i} < Nat.card {j : Fin N | F z ∈ R j} := by
  classical
  have hita : ∀ n : ℤ, (F ^ n) x ∈ R (a.val n) := by
    have hm : coding a ∈ ({coding a} : Set X) := mem_singleton _
    rw [← hcode a] at hm
    simpa only [ha, Set.mem_ofPred_eq] using hm
  have hitb : ∀ n : ℤ, (F ^ n) x ∈ R (b.val n) := by
    have hm : coding b ∈ ({coding b} : Set X) := mem_singleton _
    rw [← hcode b] at hm
    simpa only [hb, Set.mem_ofPred_eq] using hm
  have hxia : x ∈ R (a.val 0) := by simpa using hita 0
  have hxib : x ∈ R (b.val 0) := by simpa using hitb 0
  have hfa : F x ∈ R (a.val 1) := by simpa using hita 1
  have hfb : F x ∈ R (b.val 1) := by simpa using hitb 1
  have hab : B (a.val 0) (a.val 1) := by simpa using a.property 0
  have hbb : B (b.val 0) (b.val 1) := by simpa using b.property 0
  have hzfa : F z ∈ R (a.val 1) := hclosed _ _ hab x hxia hfa ⟨z, hz, rfl⟩
  have hzfb : F z ∈ R (b.val 1) := hclosed _ _ hbb x hxib hfb
    ⟨z, ⟨by simpa only [← hzero] using hz.1, hz.2⟩, rfl⟩
  obtain ⟨t, ht, htB⟩ := exists_surjective_actual_predecessor_map
    F B R coding hcode hlabel z hunique
  let j : {j : Fin N | F z ∈ R j} := ⟨a.val 1, hzfa⟩
  let k : {j : Fin N | F z ∈ R j} := ⟨b.val 1, hzfb⟩
  have hj : (t j).val = a.val 0 :=
    hunique j.val j.property ⟨(t j).property, htB j⟩ ⟨hz.1, hab⟩
  have hk : (t k).val = a.val 0 := by
    have he := hunique k.val k.property ⟨(t k).property, htB k⟩
      ⟨by simpa only [← hzero] using hz.1, hbb⟩
    exact he.trans hzero.symm
  have hcollision : t j = t k := Subtype.ext (hj.trans hk.symm)
  have hnotinj : ¬ Injective t := by
    intro hi
    exact hbranch (congrArg Subtype.val (hi hcollision))
  simpa only [Nat.card_eq_fintype_card] using
    Fintype.card_lt_of_surjective_not_injective t ht hnotinj



/-- Total label count of an actual finite family of alphabet subsets. -/
private def patternWeight {N : ℕ} (J : Set (Set (Fin N))) : ℕ := by
  classical
  exact ∑ A : J, A.val.ncard

/-- Both the number of patterns and their total label count have bounds
independent of the point. There are at most 2^N alphabet subsets, each of
cardinality at most N. This also includes empty pattern families. -/
private theorem pattern_bounds {N : ℕ} (J : Set (Set (Fin N))) :
    J.ncard ≤ 2 ^ N ∧ patternWeight J ≤ N * 2 ^ N := by
  classical
  have hc : J.ncard ≤ 2 ^ N := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_set, Fintype.card_fin]
      using J.ncard_le_card
  refine ⟨hc, ?_⟩
  calc
    patternWeight J ≤ ∑ _ : J, N := Finset.sum_le_sum fun A _ ↦ by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using A.val.ncard_le_card
    _ = N * J.ncard := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, Set.fintypeCard_eq_ncard, mul_comm]
    _ ≤ N * 2 ^ N := Nat.mul_le_mul_left N hc

/-- A concrete refinement of Bowen's finite tuple order. The first digit is
the pattern count; the second reverses total label count. Its radix is larger
than every possible total count, so a lost pattern forces a strict drop. -/
private def patternRank {N : ℕ} (J : Set (Set (Fin N))) : ℕ :=
  (N * 2 ^ N + 1) * J.ncard + (N * 2 ^ N - patternWeight J)

private theorem patternRank_bounded {N : ℕ} (J : Set (Set (Fin N))) :
    patternRank J ≤ (N * 2 ^ N + 1) * 2 ^ N + N * 2 ^ N := by
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (pattern_bounds J).1)
    (Nat.sub_le _ _)

/-- Surjective pattern transport and nondecreasing cardinalities force rank
monotonicity. With equal pattern counts the map is bijective and the finite
sum inequality applies; with fewer patterns the leading digit dominates. -/
private theorem patternRank_le_of_surjection {N : ℕ}
    (J K : Set (Set (Fin N))) (r : J → K) (hr : Surjective r)
    (hsizes : ∀ A, A.val.ncard ≤ (r A).val.ncard) :
    patternRank K ≤ patternRank J := by
  classical
  have hc : K.ncard ≤ J.ncard := by
    simpa only [Set.fintypeCard_eq_ncard] using
      Fintype.card_le_of_surjective r hr
  by_cases he : J.ncard = K.ncard
  · have hinj : Injective r := by
      by_contra hn
      have hlt := Fintype.card_lt_of_surjective_not_injective r hr hn
      simp only [Set.fintypeCard_eq_ncard] at hlt
      omega
    have hw : patternWeight J ≤ patternWeight K := by
      calc
        patternWeight J ≤ ∑ A : J, (r A).val.ncard :=
          Finset.sum_le_sum fun A _ ↦ hsizes A
        _ = patternWeight K := Fintype.sum_bijective r ⟨hinj, hr⟩ _ _ (fun _ ↦ rfl)
    unfold patternRank
    rw [he]
    exact Nat.add_le_add_left (Nat.sub_le_sub_left hw _) _
  · have hc' : K.ncard + 1 ≤ J.ncard := by omega
    have hm := Nat.mul_le_mul_left (N * 2 ^ N + 1) hc'
    rw [Nat.mul_add, Nat.mul_one] at hm
    unfold patternRank
    have hb := (pattern_bounds K).2
    omega

/-- An actual strict increase of one corresponding label count forces a
strict rank drop. If the counts of pattern families agree, bijectivity carries
the strict finite-sum inequality to the whole target family. -/
private theorem patternRank_lt_of_surjection_collision {N : ℕ}
    (J K : Set (Set (Fin N))) (r : J → K) (hr : Surjective r)
    (hsizes : ∀ A, A.val.ncard ≤ (r A).val.ncard)
    (hstrict : ∃ A, A.val.ncard < (r A).val.ncard) :
    patternRank K < patternRank J := by
  classical
  have hc : K.ncard ≤ J.ncard := by
    simpa only [Set.fintypeCard_eq_ncard] using
      Fintype.card_le_of_surjective r hr
  by_cases he : J.ncard = K.ncard
  · have hinj : Injective r := by
      by_contra hn
      have hlt := Fintype.card_lt_of_surjective_not_injective r hr hn
      simp only [Set.fintypeCard_eq_ncard] at hlt
      omega
    have hw : patternWeight J < patternWeight K := by
      calc
        patternWeight J < ∑ A : J, (r A).val.ncard :=
          Finset.sum_lt_sum (fun A _ ↦ hsizes A)
            (by obtain ⟨A, hA⟩ := hstrict; exact ⟨A, Finset.mem_univ A, hA⟩)
        _ = patternWeight K := Fintype.sum_bijective r ⟨hinj, hr⟩ _ _ (fun _ ↦ rfl)
    have hb := (pattern_bounds K).2
    unfold patternRank
    rw [he]
    omega
  · have hc' : K.ncard + 1 ≤ J.ncard := by omega
    have hm := Nat.mul_le_mul_left (N * 2 ^ N + 1) hc'
    rw [Nat.mul_add, Nat.mul_one] at hm
    unfold patternRank
    omega



/-- Actual recurrent labels in the original closed stable plaque. Closure is
in X; because the plaque is closed and contains x, this is equivalent to its
native subtype closure at x. No symbolic family is substituted for this set. -/
private def stablePhysicalPatterns {X : Type*} [MetricSpace X] {N : ℕ}
    (F : X ≃ₜ X) (γ : ℝ) (R : Fin N → Set X) (Good : Set X) (x : X) :
    Set (Set (Fin N)) :=
  {A | x ∈ closure {z : X | z ∈ Dynamics.relativeClosedStablePlaque F γ x ∧
    z ∈ Good ∧ {i : Fin N | z ∈ R i} = A}}

/-- Recurrence supplies an actual boundary-avoiding representative at every
positive original metric scale. -/
private theorem stablePhysicalPatterns_rep {X : Type*} [MetricSpace X] {N : ℕ}
    (F : X ≃ₜ X) (γ : ℝ) (R : Fin N → Set X) (Good : Set X) (x : X)
    (A : stablePhysicalPatterns F γ R Good x) (δ : ℝ) (hδ : 0 < δ) :
    ∃ z : X, dist z x < δ ∧ z ∈ Dynamics.relativeClosedStablePlaque F γ x ∧
      z ∈ Good ∧ {i : Fin N | z ∈ R i} = A.val := by
  obtain ⟨z, hz, hd⟩ := Metric.mem_closure_iff.mp A.property δ hδ
  exact ⟨z, by simpa only [dist_comm] using hd, hz⟩

/-- Recurring physical stable patterns transport surjectively under the
original F. Representatives are chosen in one strict γ/3 germ; pair contraction
and the closed stable Markov law make their image labels independent of that
choice. Finite pattern stabilization and continuity of F inverse give onto.
The only good-set premise is its actual F invariance. -/
private theorem stablePhysicalPatterns_surjection
    {X : Type*} [MetricSpace X] [CompactSpace X] {N : ℕ}
    (F : X ≃ₜ X) (γ lam : ℝ) (hγpos : 0 < γ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hcontract : ∀ x y z : X,
      y ∈ Dynamics.relativeClosedStablePlaque F γ x →
      z ∈ Dynamics.relativeClosedStablePlaque F γ x → ∀ n : ℕ,
      dist ((F : X → X)^[n] y) ((F : X → X)^[n] z) ≤ lam ^ n * dist y z)
    (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X)
    (hit : ∀ a, {y : X | ∀ n : ℤ, (F ^ n) y ∈ R (a.val n)} = {coding a})
    (hlabel : ∀ i x, x ∈ R i → ∃ a : CodeSpace B, coding a = x ∧ a.val 0 = i)
    (hclosed : ∀ i j, B i j → ∀ x, x ∈ R i → F x ∈ R j →
      F '' (R i ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆ R j)
    (Good : Set X) (hgood : ∀ z, z ∈ Good ↔ F z ∈ Good) (x : X) :
    ∃ r : stablePhysicalPatterns F γ R Good x →
        stablePhysicalPatterns F γ R Good (F x), Surjective r ∧
      ∀ A, ∀ z, dist z x < γ / 3 →
        z ∈ Dynamics.relativeClosedStablePlaque F γ x → z ∈ Good →
        {i : Fin N | z ∈ R i} = A.val → {i : Fin N | F z ∈ R i} = (r A).val := by
  classical
  have hγ : 0 < γ / 3 := by linarith [hγpos]
  choose rep hrepdist hrepstable hrepgood hreplabel using
    fun A : stablePhysicalPatterns F γ R Good x ↦
      stablePhysicalPatterns_rep F γ R Good x A (γ / 3) hγ
  have hsame : ∀ A : stablePhysicalPatterns F γ R Good x, ∀ z,
      dist z x < γ / 3 → z ∈ Dynamics.relativeClosedStablePlaque F γ x →
      {i : Fin N | z ∈ R i} = A.val →
      {i : Fin N | F z ∈ R i} = {i : Fin N | F (rep A) ∈ R i} := by
    intro A z hz hs hL
    exact same_stable_pattern_same_forward_pattern F γ B R coding hit hlabel hclosed
      z (rep A) (by
        intro n
        have hc := hcontract x (rep A) z (hrepstable A) hs n
        have hp : lam ^ n ≤ 1 := pow_le_one₀ hlam hlam1
        have hd : dist (rep A) z < γ := by
          have ht := dist_triangle (rep A) x z
          have hh := hrepdist A
          rw [dist_comm x z] at ht
          linarith
        exact hc.trans ((mul_le_mul_of_nonneg_right hp dist_nonneg).trans
          (by simpa using hd.le)))
      (hL.trans (hreplabel A).symm)
  have htarget : ∀ A : stablePhysicalPatterns F γ R Good x,
      {i : Fin N | F (rep A) ∈ R i} ∈ stablePhysicalPatterns F γ R Good (F x) := by
    intro A
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hmap⟩ := Metric.continuousAt_iff.mp F.continuous.continuousAt ε hε
    obtain ⟨z, hz, hs, hg, hL⟩ := stablePhysicalPatterns_rep
      F γ R Good x A (min δ (γ / 3)) (lt_min hδ hγ)
    have hzs := hz.trans_le (min_le_right _ _)
    refine ⟨F z, ⟨?_, (hgood z).mp hg, hsame A z hzs hs hL⟩, ?_⟩
    · intro n
      simpa only [Function.iterate_succ_apply] using hs (n + 1)
    · simpa only [dist_comm] using hmap (hz.trans_le (min_le_left _ _))
  let r : stablePhysicalPatterns F γ R Good x → stablePhysicalPatterns F γ R Good (F x) :=
    fun A ↦ ⟨{i : Fin N | F (rep A) ∈ R i}, htarget A⟩
  refine ⟨r, ?_, fun A z hz hs _ hL ↦ hsame A z hz hs hL⟩
  obtain ⟨δ, hδ, hrec⟩ := membership_patterns_eventually_recurrent R
    (Dynamics.relativeClosedStablePlaque F γ x ∩ Good) x
  obtain ⟨η, hη, hinv⟩ := Metric.continuousAt_iff.mp F.symm.continuous.continuousAt
    (min δ (γ / 3)) (lt_min hδ hγ)
  intro C
  obtain ⟨w, hw, hs, hg, hL⟩ := stablePhysicalPatterns_rep F γ R Good (F x) C η hη
  have hz : dist (F.symm w) x < min δ (γ / 3) := by
    simpa only [F.symm_apply_apply] using hinv hw
  have hzstable : F.symm w ∈ Dynamics.relativeClosedStablePlaque F γ x := by
    intro n
    cases n with
    | zero => exact (hz.trans_le (min_le_right _ _)).le.trans (by linarith [hγpos])
    | succ n => simpa only [Function.iterate_succ_apply, F.apply_symm_apply] using hs n
  have hzgood : F.symm w ∈ Good := (hgood _).mpr (by simpa using hg)
  let A : stablePhysicalPatterns F γ R Good x :=
    ⟨{i : Fin N | F.symm w ∈ R i}, by
      simpa only [stablePhysicalPatterns, mem_ofPred_eq, mem_inter_iff, and_assoc] using
        hrec (F.symm w) (hz.trans_le (min_le_left _ _)) ⟨hzstable, hzgood⟩⟩
  refine ⟨A, Subtype.ext ?_⟩
  have he := hsame A (F.symm w) (hz.trans_le (min_le_right _ _)) hzstable rfl
  simp only [F.apply_symm_apply] at he
  exact he.symm.trans hL

/-- The rank is constructed from the actual recurring stable labels. Its
remaining geometric premises are explicit: good points have unique legal
predecessors, and they accumulate at every point of every closed stable slice.
Surjective pattern transport and the collision at a branch then prove both
ordinary monotonicity and strict decrease; no rank is postulated. -/
private theorem actual_stable_pattern_rank
    {X : Type*} [MetricSpace X] [CompactSpace X] {N : ℕ}
    (F : X ≃ₜ X) (γ lam : ℝ) (hγpos : 0 < γ) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hcontract : ∀ x y z : X,
      y ∈ Dynamics.relativeClosedStablePlaque F γ x →
      z ∈ Dynamics.relativeClosedStablePlaque F γ x → ∀ n : ℕ,
      dist ((F : X → X)^[n] y) ((F : X → X)^[n] z) ≤ lam ^ n * dist y z)
    (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X)
    (hit : ∀ a, {y : X | ∀ n : ℤ, (F ^ n) y ∈ R (a.val n)} = {coding a})
    (hlabel : ∀ i x, x ∈ R i → ∃ a : CodeSpace B, coding a = x ∧ a.val 0 = i)
    (hclosed : ∀ i j, B i j → ∀ x, x ∈ R i → F x ∈ R j →
      F '' (R i ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆ R j)
    (Good : Set X) (hgood : ∀ z, z ∈ Good ↔ F z ∈ Good)
    (hunique : ∀ z ∈ Good, ∀ j, F z ∈ R j →
      {i : Fin N | z ∈ R i ∧ B i j}.Subsingleton)
    (hdense : ∀ x i, x ∈ R i → x ∈ closure {z : X |
      z ∈ R i ∧ z ∈ Dynamics.relativeClosedStablePlaque F γ x ∧ z ∈ Good}) :
    let rank := fun x ↦ patternRank (stablePhysicalPatterns F γ R Good x)
    (∀ x, rank x ≤ (N * 2 ^ N + 1) * 2 ^ N + N * 2 ^ N) ∧
    (∀ x, rank (F x) ≤ rank x) ∧
    (∀ x a b, coding a = x → coding b = x → a.val 0 = b.val 0 →
      a.val 1 ≠ b.val 1 → rank (F x) < rank x) := by
  classical
  dsimp only
  refine ⟨fun x ↦ patternRank_bounded _, ?_, ?_⟩
  · intro x
    obtain ⟨r, hr, hrule⟩ := stablePhysicalPatterns_surjection
      F γ lam hγpos hlam hlam1 hcontract B R coding hit hlabel hclosed Good hgood x
    apply patternRank_le_of_surjection _ _ r hr
    intro A
    obtain ⟨z, hz, hs, hg, hL⟩ := stablePhysicalPatterns_rep
      F γ R Good x A (γ / 3) (by linarith [hγpos])
    obtain ⟨t, ht, _⟩ := exists_surjective_actual_predecessor_map
      F B R coding hit hlabel z (hunique z hg)
    have hc := Fintype.card_le_of_surjective t ht
    simp only [Set.fintypeCard_eq_ncard] at hc
    rwa [hL, hrule A z hz hs hg hL] at hc
  · intro x a b ha hb hzero hbranch
    obtain ⟨r, hr, hrule⟩ := stablePhysicalPatterns_surjection
      F γ lam hγpos hlam hlam1 hcontract B R coding hit hlabel hclosed Good hgood x
    apply patternRank_lt_of_surjection_collision _ _ r hr
    · intro A
      obtain ⟨z, hz, hs, hg, hL⟩ := stablePhysicalPatterns_rep
        F γ R Good x A (γ / 3) (by linarith [hγpos])
      obtain ⟨t, ht, _⟩ := exists_surjective_actual_predecessor_map
        F B R coding hit hlabel z (hunique z hg)
      have hc := Fintype.card_le_of_surjective t ht
      simp only [Set.fintypeCard_eq_ncard] at hc
      rwa [hL, hrule A z hz hs hg hL] at hc
    · have hxi : x ∈ R (a.val 0) := by
        have hm : coding a ∈ ({coding a} : Set X) := mem_singleton _
        rw [← hit a] at hm
        simpa only [ha, zpow_zero, Homeomorph.one_apply] using hm 0
      obtain ⟨δ, hδ, hrec⟩ := membership_patterns_eventually_recurrent R
        (Dynamics.relativeClosedStablePlaque F γ x ∩ Good) x
      obtain ⟨z, hz, hdist⟩ := Metric.mem_closure_iff.mp (hdense x (a.val 0) hxi)
        (min δ (γ / 3)) (lt_min hδ (by linarith [hγpos]))
      have hd : dist z x < min δ (γ / 3) := by simpa only [dist_comm] using hdist
      let A : stablePhysicalPatterns F γ R Good x :=
        ⟨{i : Fin N | z ∈ R i}, by
          simpa only [stablePhysicalPatterns, mem_ofPred_eq, mem_inter_iff, and_assoc] using
            hrec z (hd.trans_le (min_le_left _ _)) hz.2⟩
      have hc := actual_branch_stable_slice_strict_label_cardinality F γ B R coding
        hit hlabel hclosed x z a b ha hb hzero hbranch ⟨hz.1, hz.2.1⟩
        (hunique z hz.2.2)
      simp only [Nat.card_coe_set_eq] at hc
      refine ⟨A, ?_⟩
      have he := hrule A z (hd.trans_le (min_le_right _ _)) hz.2.1 hz.2.2 rfl
      change ({i : Fin N | z ∈ R i}).ncard < (r A).val.ncard
      rwa [he] at hc

/-- Reverse integer time and transpose the transition relation. Legality is
the original edge at −j−1; reversing twice restores the original code. -/
private def reverseLegalCode {N : ℕ} (B : Fin N → Fin N → Prop)
    (a : CodeSpace B) : CodeSpace (fun i j ↦ B j i) :=
  ⟨fun j ↦ a.val (-j), by
    intro j
    have h := a.property (-(j + 1))
    simpa only [show -(j + 1) + 1 = -j by omega] using h⟩

private theorem reverseLegalCode_twice {N : ℕ} (B : Fin N → Fin N → Prop)
    (a : CodeSpace B) :
    reverseLegalCode (fun i j ↦ B j i) (reverseLegalCode B a) = a := by
  apply Subtype.ext
  funext j
  simp only [reverseLegalCode, neg_neg]

/-- Apply the concrete physical-pattern construction in both time directions.
The inverse-time coding is defined by reversing the SAME legal sequences, so
the two ranks control branches of the very same original coding map. -/
private theorem actual_two_sided_pattern_ranks
    {X : Type*} [MetricSpace X] [CompactSpace X] {N : ℕ}
    (F : X ≃ₜ X) (γ lam : ℝ) (H : Dynamics.Bowen.CompactLocalProductData F γ lam)
    (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X)
    (hit : ∀ a, {y : X | ∀ n : ℤ, (F ^ n) y ∈ R (a.val n)} = {coding a})
    (hlabel : ∀ i x, x ∈ R i → ∃ a : CodeSpace B, coding a = x ∧ a.val 0 = i)
    (hclosed : ∀ i j, B i j → ∀ x, x ∈ R i → F x ∈ R j →
      (F '' (R i ∩ Dynamics.relativeClosedStablePlaque F γ x) ⊆ R j) ∧
      (R j ∩ Dynamics.relativeClosedUnstablePlaque F γ (F x) ⊆
        F '' (R i ∩ Dynamics.relativeClosedUnstablePlaque F γ x)))
    (Gs Gu : Set X)
    (hgs : ∀ z, z ∈ Gs ↔ F z ∈ Gs) (hgu : ∀ z, z ∈ Gu ↔ F.symm z ∈ Gu)
    (huniqS : ∀ z ∈ Gs, ∀ j, F z ∈ R j →
      {i : Fin N | z ∈ R i ∧ B i j}.Subsingleton)
    (huniqU : ∀ z ∈ Gu, ∀ j, F.symm z ∈ R j →
      {i : Fin N | z ∈ R i ∧ B j i}.Subsingleton)
    (hdenseS : ∀ x i, x ∈ R i → x ∈ closure {z : X |
      z ∈ R i ∧ z ∈ Dynamics.relativeClosedStablePlaque F γ x ∧ z ∈ Gs})
    (hdenseU : ∀ x i, x ∈ R i → x ∈ closure {z : X |
      z ∈ R i ∧ z ∈ Dynamics.relativeClosedUnstablePlaque F γ x ∧ z ∈ Gu}) :
    ∃ K : ℕ, ∃ rs ru : X → ℕ,
      (∀ x, rs x ≤ K) ∧ (∀ x, ru x ≤ K) ∧
      (∀ x, rs (F x) ≤ rs x) ∧ (∀ x, ru (F.symm x) ≤ ru x) ∧
      (∀ x a b, coding a = x → coding b = x → a.val 0 = b.val 0 →
        a.val 1 ≠ b.val 1 → rs (F x) < rs x) ∧
      (∀ x a b, coding a = x → coding b = x → a.val 0 = b.val 0 →
        a.val (-1) ≠ b.val (-1) → ru (F.symm x) < ru x) := by
  classical
  let Br := fun i j ↦ B j i
  let cr : CodeSpace Br → X := fun a ↦ coding (reverseLegalCode Br a)
  have hinvpow : ∀ (j : ℤ) (x : X), (F.symm ^ j) x = (F ^ (-j)) x := by
    intro j x
    change (F⁻¹ ^ j) x = (F ^ (-j)) x
    rw [inv_zpow']
  have hitr : ∀ a : CodeSpace Br,
      {y : X | ∀ n : ℤ, (F.symm ^ n) y ∈ R (a.val n)} = {cr a} := by
    intro a
    rw [show cr a = coding (reverseLegalCode Br a) from rfl, ← hit]
    ext y
    constructor <;> intro hy n
    · simpa only [hinvpow, reverseLegalCode, neg_neg] using hy (-n)
    · simpa only [hinvpow, reverseLegalCode, neg_neg] using hy (-n)
  have hlabelr : ∀ i x, x ∈ R i → ∃ a : CodeSpace Br, cr a = x ∧ a.val 0 = i := by
    intro i x hx
    obtain ⟨a, ha, hzero⟩ := hlabel i x hx
    refine ⟨reverseLegalCode B a, ?_, ?_⟩
    · simpa only [cr, Br, reverseLegalCode_twice] using ha
    · simpa only [reverseLegalCode, neg_zero] using hzero
  have hclosedr : ∀ i j, Br i j → ∀ x, x ∈ R i → F.symm x ∈ R j →
      F.symm '' (R i ∩ Dynamics.relativeClosedStablePlaque F.symm γ x) ⊆ R j := by
    intro i j hij x hxi hxj y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hc := (hclosed j i hij (F.symm x) hxj (by simpa using hxi)).2
    have hzs : z ∈ R i ∩ Dynamics.relativeClosedUnstablePlaque F γ (F (F.symm x)) := by
      rw [F.apply_symm_apply]
      exact hz
    obtain ⟨w, hw, hwz⟩ := hc hzs
    simpa only [← hwz, F.symm_apply_apply] using hw.1
  obtain ⟨hKs, hms, hbs⟩ := actual_stable_pattern_rank F γ lam H.gamma_pos
    H.lambda_pos.le H.lambda_lt_one.le H.stable_contraction B R coding hit hlabel
    (fun i j hij x hx hfx ↦ (hclosed i j hij x hx hfx).1) Gs hgs huniqS hdenseS
  obtain ⟨hKu, hmu, hbu⟩ := actual_stable_pattern_rank F.symm γ lam H.gamma_pos
    H.lambda_pos.le H.lambda_lt_one.le H.unstable_contraction Br R cr hitr hlabelr
    hclosedr Gu hgu huniqU hdenseU
  refine ⟨(N * 2 ^ N + 1) * 2 ^ N + N * 2 ^ N,
    fun x ↦ patternRank (stablePhysicalPatterns F γ R Gs x),
    fun x ↦ patternRank (stablePhysicalPatterns F.symm γ R Gu x),
    hKs, hKu, hms, hmu, hbs, ?_⟩
  intro x a b ha hb hzero hbranch
  apply hbu x (reverseLegalCode B a) (reverseLegalCode B b)
  · simpa only [cr, Br, reverseLegalCode_twice] using ha
  · simpa only [cr, Br, reverseLegalCode_twice] using hb
  · simpa only [reverseLegalCode, neg_zero] using hzero
  · exact hbranch


/-- All integer iterates of the same point satisfy the specified geometric
property. This set is invariant by reindexing n ↦ n+1, including negative n. -/
private def allTimeGood {X : Type*} [TopologicalSpace X]
    (F : X ≃ₜ X) (P : X → Prop) : Set X := {x | ∀ n : ℤ, P ((F ^ n) x)}

private theorem allTimeGood_invariant {X : Type*} [TopologicalSpace X]
    (F : X ≃ₜ X) (P : X → Prop) (x : X) :
    x ∈ allTimeGood F P ↔ F x ∈ allTimeGood F P := by
  constructor
  · intro hx n
    have he : (F ^ n) (F x) = (F ^ (n + 1)) x := by
      rw [zpow_add_one, Homeomorph.mul_apply]
    rw [he]
    exact hx (n + 1)
  · intro hx n
    have he : (F ^ (n - 1)) (F x) = (F ^ n) x := by
      have hp : F ^ (n - 1) * F = F ^ n := by
        rw [← zpow_add_one]
        simp
      change (F ^ (n - 1) * F) x = (F ^ n) x
      rw [hp]
    simpa only [he] using hx (n - 1)

/-- Bowen 1970b, Lemma 2, pp. 908–909: after the directional boundary argument
gives a dense open subset of each integer-time good trace in a compact closed slice,
the Baire theorem gives good points arbitrarily close to every point of that slice.
The premise concerns the actual subspace topology of the slice. -/
private theorem dense_allTimeGood_in_compact_slice
    {X : Type*} [MetricSpace X] (F : X ≃ₜ X) (S : Set X)
    (hS : IsCompact S) (P : X → Prop)
    (hgood : ∀ n : ℤ, ∃ U : Set S, IsOpen U ∧ Dense U ∧
      U ⊆ {z : S | P ((F ^ n) z.val)}) :
    S ⊆ closure {z : X | z ∈ S ∧ z ∈ allTimeGood F P} := by
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  choose U hUopen hUdense hUsub using hgood
  have htrace : Dense (⋂ n : ℤ, {z : S | P ((F ^ n) z.val)}) :=
    (dense_iInter_of_isOpen hUopen hUdense).mono
      (iInter_mono fun n ↦ hUsub n)
  intro x hx
  have hx' := (Subtype.dense_iff.mp htrace) hx
  apply (closure_mono ?_) hx'
  rintro y ⟨z, hz, rfl⟩
  exact ⟨z.property, fun n ↦ mem_iInter.mp hz n⟩

private theorem isClosed_relativeClosedStablePlaque
    {X : Type*} [MetricSpace X] (F : X ≃ₜ X) (γ : ℝ) (x : X) :
    IsClosed (Dynamics.relativeClosedStablePlaque F γ x) := by
  simp only [Dynamics.relativeClosedStablePlaque, ofPred_forall]
  exact isClosed_iInter fun n ↦ by
    have heq : ((F : X → X)^[n]) = ((F ^ n : X ≃ₜ X) : X → X) :=
      funext fun y ↦ (homeomorph_nat_pow_apply F n y).symm
    exact isClosed_le (by simpa only [heq] using
      (F ^ n).continuous.dist (continuous_const : Continuous fun _ : X ↦ (F ^ n) x))
      continuous_const



end NativePatternRanks

section FactOneAdapter

variable {X : Type*} [MetricSpace X] [CompactSpace X]



end FactOneAdapter

section Geometric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Continuity of a real tangent subbundle only over Λ. Source: the original
hyperbolic-set hypothesis recalled in Bowen Fact 1, pp. 726–727. Each local
trivialization uses the topology induced by the actual inclusion in TM and
the relative topology on Λ. No distribution outside Λ is constrained. -/
def IsContinuousDistributionOn (Λ : Set M)
    (V : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)) : Prop :=
  ∀ x : Λ, ∃ r : ℕ,
    letI : TopologicalSpace (Bundle.TotalSpace (Fin r → ℝ) (fun y : Λ => ↥(V y.val))) :=
      TopologicalSpace.induced
        (fun z => (⟨z.proj.val, z.snd.val⟩ : TangentBundle 𝓘(ℝ, E) M)) inferInstance
    ∃ e : Bundle.Trivialization (Fin r → ℝ)
        (Bundle.TotalSpace.proj (F := Fin r → ℝ) (E := fun y : Λ => ↥(V y.val))),
      x ∈ e.baseSet ∧ e.IsLinear ℝ

variable [FiniteDimensional ℝ E] [CompactSpace M]
  [Bundle.RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E
    (fun x : M => TangentSpace 𝓘(ℝ, E) x)]

/-- The original compatible Riemannian distance agrees with its tensor's
length distance within each connected component. On a disconnected compact
manifold the prescribed finite intercomponent distances remain unrestricted.
Source: the original Riemannian-distance input of Bowen Fact 1, pp. 726–727. -/
def HasOriginalRiemannianDistance : Prop :=
  ∀ x y : M, y ∈ connectedComponent x →
    edist x y = Manifold.riemannianEDist 𝓘(ℝ, E) x y


omit [FiniteDimensional ℝ E] [CompactSpace M] in
/-- The original smooth metric and the hyperbolic input genuinely build the Fact1 datum.
The local-maximality intersection uses all integer images; replacing j by −j proves the
orbit formulation. The tangent fibres and their induced topology are the given ones. -/
private theorem exists_original_factOne_datum
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (Λ : Set M) (hΛne : Λ.Nonempty) (hΛcompact : IsCompact Λ)
    (hΛinvariant : ∀ x : M, x ∈ Λ ↔ f x ∈ Λ)
    (stable unstable : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (hstableContinuous : IsContinuousDistributionOn Λ stable)
    (hunstableContinuous : IsContinuousDistributionOn Λ unstable)
    (hcompl : ∀ x ∈ Λ, IsCompl (stable x) (unstable x))
    (hstableInvariant : ∀ x ∈ Λ,
      (stable x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap = stable (f x))
    (hunstableInvariant : ∀ x ∈ Λ,
      (unstable x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap = unstable (f x))
    (C rate : ℝ) (hC : 1 ≤ C) (hratepos : 0 < rate) (hratelt : rate < 1)
    (hstableBound : ∀ (n : ℕ) (x : M), x ∈ Λ → ∀ v ∈ stable x,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f : M → M)^[n]) x v‖ ≤ C * rate ^ n * ‖v‖)
    (hunstableBound : ∀ (n : ℕ) (x : M), x ∈ Λ → ∀ v ∈ unstable x,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f.symm : M → M)^[n]) x v‖ ≤ C * rate ^ n * ‖v‖)
    (hlocalMaximal : ∃ U : Set M, IsOpen U ∧ Λ ⊆ U ∧
      Λ = ⋂ j : ℤ, ((f.toHomeomorph ^ j : M ≃ₜ M) : M → M) '' U) :
    ∃ H : HyperbolicSetFactOneDatum f Λ,
      (∀ x : Λ, H.stable.fibre x = stable x) ∧
      (∀ x : Λ, H.unstable.fibre x = unstable x) := by
  obtain ⟨U, hU, hΛU, hmax⟩ := hlocalMaximal
  let g := RiemannianBundle.g (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
  obtain ⟨g', hgsmooth, hg'⟩ :=
    IsContMDiffRiemannianBundle.exists_contMDiff (IB := 𝓘(ℝ, E)) (n := ∞)
      (F := E) (E := fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)
  have hg_eq : g' = g.inner := by
    funext x
    ext v w
    exact (hg' x v w).symm
  rw [hg_eq] at hgsmooth
  let originalMetric : Bundle.ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x) :=
    { inner := g.inner
      symm := g.symm
      pos := g.pos
      isVonNBounded := g.isVonNBounded
      contMDiff := hgsmooth }
  have hnorm : ∀ (x : M) (v : TangentSpace 𝓘(ℝ, E) x),
      hyperbolicRiemannianNorm originalMetric v = ‖v‖ := by
    intro x v
    exact (norm_eq_sqrt_real_inner v).symm
  have hf : MapsTo f Λ Λ := fun x hx ↦ (hΛinvariant x).mp hx
  have hfinv : MapsTo f.symm Λ Λ := by
    intro x hx
    apply (hΛinvariant (f.symm x)).mpr
    simpa using hx
  have hlocal : ∀ x : M,
      x ∈ Λ ↔ ∀ n : ℤ, hyperbolicIntegerOrbit f n x ∈ U := by
    intro x
    constructor
    · intro hx n
      have hx' : x ∈ ((f.toHomeomorph ^ (-n) : M ≃ₜ M) : M → M) '' U :=
        mem_iInter.mp (hmax ▸ hx) (-n)
      obtain ⟨y, hy, hyx⟩ := hx'
      subst x
      simpa [hyperbolicIntegerOrbit, zpow_neg] using hy
    · intro hx
      rw [hmax]
      apply mem_iInter.mpr
      intro j
      refine ⟨hyperbolicIntegerOrbit f (-j) x, hx (-j), ?_⟩
      simp [hyperbolicIntegerOrbit, zpow_neg]
  refine ⟨{
    nonempty := hΛne
    compact := hΛcompact
    forward_mem := hf
    backward_mem := hfinv
    originalMetric := originalMetric
    stable := ⟨fun x ↦ stable x, hstableContinuous⟩
    unstable := ⟨fun x ↦ unstable x, hunstableContinuous⟩
    complementary := fun x ↦ hcompl x x.property
    stable_invariant := fun x ↦ hstableInvariant x x.property
    unstable_invariant := fun x ↦ hunstableInvariant x x.property
    C := C
    one_le_C := hC
    rate := rate
    rate_pos := hratepos
    rate_lt_one := hratelt
    stable_estimate := ?_
    unstable_estimate := ?_
    isolatingNeighborhood := U
    isolating_open := hU
    subset_isolating := hΛU
    locally_maximal := hlocal }, ?_, ?_⟩
  · intro n x v hv
    simpa only [hnorm] using hstableBound n x x.property v hv
  · intro n x v hv
    simpa only [hnorm] using hunstableBound n x x.property v hv
  · intro x
    rfl
  · intro x
    rfl

/-- Bowen hyperbolic-basic-set coding, including finite fibres, periodic coordinate rigidity and splicing.

Sources: Bowen1970, Markov Partitions for Axiom A Diffeomorphisms, Fact1 pp726–727, Theorem12 pp731–732, Lemmas25–27 and Theorem28 pp740–742; Bowen1970, Markov Partitions and Minimal Sets for Axiom A Diffeomorphisms, Lemmas1–2/6–7 and Propositions3/8–12 pp908–914.

The ambient model is an arbitrary finite-dimensional real normed space and its identity model with corners, hence a boundaryless manifold; no positive dimension, connectedness, mixing, or full-manifold hyperbolicity is assumed. The two distributions are arbitrary off Λ and have genuine local linear trivializations only on Λ. The supplied metric and smooth tensor are linked by componentwise Riemannian length distance; the finite cross-component metric is not replaced. The adapted metric, local-plaque size and rectangles are existential outputs. The transition predicate is exactly the 0/1 adjacency matrix encoded as a relation; its finite alphabet and product topology are Mathlib’s native definitions.

Complete natural-language proof from the current source DAG:

1. The original smooth hypotheses supply exact compact Fact1 geometry
Apply dynamics.hirsch_pugh_hyperbolic_set_fact1_g9 to the stated original f and Λ, omitting the unused transitivity assumption. Its current SOURCE/split/complete conclusion supplies the adapted compatible metric d*, contraction κ, closed Wγ stable/unstable orbit plaques, and continuous unique bracket. This application uses the original hyperbolic-set hypotheses directly, not the whole-manifold Anosov plaque theorem or a native intrinsic atlas. On compact Λ the identity (Λ,d*)→(Λ,d) is continuous because both metrics induce the original subspace topology; mathlib.isCompact_uniformContinuousOn_of_continuous makes it uniformly continuous. For the prescribed ε>0 choose η0>0 such that d*(x,y)<η0 implies d(x,y)<ε/2, and set η=η0/2>0. Then d*(x,y)≤η implies d*(x,y)<η0 and hence d(x,y)<ε/2. Step3 retains μ<η, so every pair in a returned rectangle has original d-distance <ε/2. Taking the supremum gives diam_d(R_i)≤ε/2<ε; the strict final margin does not require a supremum of values <ε to remain <ε. All coding arguments below use the original closed Wγ orbit plaques with their Λ-subspace topology and the relatively open product germs proved in Step2. No identification with strong-graph radii, g9 native intrinsic or complex atlases, or equality of different metric germs is inferred or needed. All interiors and closures below are in Λ, never ambient M. Fact1 is complete at its own one-level source-proof boundary; its named lower foundations and formal/Lean/transitive verification remain separate from this consumer deduction.

2. Compact canonical products and guarded bracket covariance
The bracket has [x,x]=x. For each r≤γ, continuity uniformly on a compact smaller closed pair domain gives ε(r)>0 such that d*(x,y)≤ε(r) implies the bracket is within d*-distance r of both x and y; since it belongs to their γ plaques, pairwise contraction upgrades this to [x,y]∈W_r^s(x)∩W_r^u(y). Choose γ=α0>α1>⋯>α7>0 with α_(k+1)<min(α_k/3,ε(α_k/3))/3, and such that d*(x,y)≤α_(k+1) implies d*(fx,fy),d*(f⁻¹x,f⁻¹y)<α_k. These choices use compact uniform continuity of f and f⁻¹. The compact Fact1 product-chart theorem now identifies small relatively open unstable/stable factor products with open subsets of Λ, and supplies the inverse coordinates p↦([p,x],[x,p]). Absorption [[p,q],r]=[p,r] and [p,[q,r]]=[p,r] follow from uniqueness whenever all points and brackets lie in these strict common plaque collars. The one-step covariance used below is not asserted globally: if d*(p,q),d*(fp,fq)≤α2, then f[p,q]=[fp,fq]. Indeed f[p,q] has the required stable future inequalities by contraction; its unstable inequalities at negative times ≥1 shift the inequalities for [p,q], and the missing time-zero inequality is <γ by the one-step continuity guard. Uniqueness proves the identity. Iterating this argument proves finite-prefix covariance only when every intermediate pair satisfies the guard.

3. Bowen small proper rectangles, including the actual original-map construction
Use dynamics.bowen_compact_local_product_proper_partition on (Λ,d*,f|Λ) with mesh μ<min(η,α7). Its exact compact-metric hypotheses were supplied above. Its source construction starts with finitely many compact regular-closed stable/unstable factor products covering Λ by their interiors and a uniform positive saturation margin. It chooses m large enough that β=κ^m has a geometric tail smaller than that margin. Writing h=f^m, its unstable factors satisfy C_i^n=⋃_j h⁻¹[C_(T_ij)^(n−1),h(y_ij)] for finitely many branches chosen from the uniform seed saturation; C_i=closure ⋃_n C_i^n stays inside the prescribed collar because the nth increment is bounded by β^n times the seed radius. The reversed construction gives D_i, and A_i=[C_i,D_i] has stable/unstable slice-covering properties for h. Regularized complements of C_i,D_i give four local quadrant products; the finite regular-open Boolean profile atoms have compact proper closures, disjoint interiors, and cover Λ. Slice covering and the quadrant profiles give the h-Markov property. Finally the retained nonempty sets E=closure ⋂_(0≤k<m)f^(−k)(int P_k) refine these h-atoms to an f-partition. Guarded finite-prefix covariance makes them rectangles, and the endpoint h-covering proves the original f stable/unstable inclusions. This is the actual iterate-enlargement/quadrant/original-map join, not an assumption that a partition for f^m is a partition for f. Name the resulting finite nonempty family R_1,…,R_N. Compactness, properness, disjoint interiors and the stated interior-witness Markov inclusions are exactly the retained provider conclusion. Its initial-cover, Boolean-atom and iterate-atom lower proofs remain their own dependencies, without their proofs being certified anew by this coding deduction. No connectedness of rectangles, planar-null frontier or finite-neighbor assertion from ghys.markov_partition is used.

4. A witnessed transition controls every closed overlap: Lemma25(a)
Write E,F for two partition rectangles with B_EF=1 and choose w∈int E∩f⁻¹(int F). The partition gives both Markov inclusions at w. They extend to any x∈E∩f⁻¹F as follows. For t∈F∩Wγ^u(fx), let r=[t,fw]. Bracket closure of F gives r∈F∩Wγ^u(fw), so the witnessed unstable covering supplies q∈E∩Wγ^u(w) with fq=r. Both q,x lie in E and fq,fx lie in F; the small mesh provides precisely the time0/time1 covariance guards. Thus v=[q,x] belongs to E∩Wγ^u(x) and fv=[fq,fx]=[[t,fw],fx]=[t,fx]=t. This proves fW^u(x,E)⊇W^u(fx,F) without making any prior assumption about the unknown preimage f⁻¹t. Apply the same argument to f⁻¹, exchanging E,F and exchanging stable/unstable bracket coordinates: its unstable covering at fw is precisely the original stable inclusion at w. It gives f⁻¹W^s(fx,F)⊇W^s(x,E), equivalently fW^s(x,E)⊆W^s(fx,F). Here W^s/u(x,E)=E∩Wγ^s/u(x). All absorption formulas involve source points in E or target points in F, with strict common guards. This is the closed-overlap version needed by Lemma26, not merely the interior-witness definition.

5. Relative-Λ unstable subrectangles and the nonempty transition product: Lemma26
Call A a u-subrectangle of E when A is a nonempty compact proper bracket-closed rectangle contained in E and W^u(z,E)⊆A for every z∈A. Fix the witness w above and set C=W^u(w,E), D=W^s(w,E)∩A. For z∈A, [w,z] belongs to W^u(z,E), hence lies in A and D. Thus D is nonempty. Bracket absorption and u-saturation show A=[C,D]. The slice theorem gives compact regular-closed C in the full γ unstable plaque. To prove D regular closed even when w∉A, use the open product chart based at w: A corresponds to C×D and is regular closed in that open chart. Product interior and closure identities yield C×D=closure(int C)×closure(int D)=C×closure(int D); since C is nonempty this gives D=closure(int D). The compact small factor cores lie inside the open chart, so these are the full-plaque interior/closure identities, not interiors only in E. By the stable inclusion at w, fD⊆F∩Wγ^s(fw). For z∈D, the closed-overlap unstable law at z gives fWu(z,E)⊇Wu(fz,F)=[Wu(fw,F),fz]. Taking the union proves [Wu(fw,F),fD]⊆fA∩F. Conversely y∈A with fy∈F has z=[w,y]∈D. Since w,y∈E and fw,fy∈F, guarded covariance gives fz=[fw,fy], so fy∈Wu(fz,F)=[Wu(fw,F),fz]. Therefore fA∩F=[Wu(fw,F),fD].

6. The omitted relative-plaque openness in Lemma26
The last product is proper in Λ, with no manifold assumption on Λ. Define O=Wγ^s(w)∩{z:d*(z,w)<γ}. Pairwise contraction implies fO⊆Wγ^s(fw). Conversely, if t∈Wγ^s(fw)∩f({z:d*(z,w)<γ}), its inverse z has d*(z,w)<γ at time0 and, at every time n≥1, the stable inequalities for t at time n−1 imply d*(f^n z,f^n w)≤γ. Thus z∈O. Hence fO=Wγ^s(fw)∩f(B_γ(w)), which is relatively open in the full target plaque, and f:O→fO is a homeomorphism. Since D lies in a strict small ball about w, this homeomorphism transports its dense relative interior to fD. Compactness makes fD closed in the full target plaque, so fD is regular closed there. The same follows for Wu(fw,F) from the rectangle-slice theorem. Both factors are nonempty and contained in the α4 cores because they lie in F, whose mesh is <α7. The regular-closed-product theorem gives a nonempty compact proper rectangle [Wu(fw,F),fD]. Its product description makes it u-saturated in F, hence fA∩F is a u-subrectangle of F. This expands Bowen p741’s homeomorphic-into assertion explicitly for the possibly non-manifold compact relative plaque. Singleton and zero-dimensional factors are open in themselves, so the argument includes them.

7. Every finite legal word is realized
For a∈Σ_B and n≥0 let K_n=⋂_(−n≤j≤n)f^(−j)R_(a_j). Starting at time −n, set T_0=R_(a_(−n)) and T_(k+1)=f(T_k)∩R_(a_(−n+k+1)) for 0≤k<2n. A whole rectangle is a u-subrectangle of itself, and every transition has an interior witness by the definition of B. The previous two steps inductively make each T_k a nonempty proper u-subrectangle of its receiving rectangle. A direct induction on k gives T_k=⋂_(i=0)^k f^(k−i)R_(a_(−n+i)); in particular T_(2n)=f^n K_n. Thus K_n is nonempty. Each K_n is closed and compact in compact Λ because it is a finite intersection of homeomorphic preimages of compact closed rectangles. They decrease with n. The named nested-compact theorem therefore gives a point of ⋂_n K_n=⋂_(j∈Z)f^(−j)R_(a_j). This uses legal finite strips, not an invalid inference that all pairwise overlaps imply a whole word intersection.

8. Expansivity and the uniform finite-window bound
If d*(f^j x,f^j y)≤γ for all integers j, then x∈Wγ^s(y)∩Wγ^u(y), whose unique point is [y,y]=y. Thus γ is an expansive bound. Two points in the full itinerary intersection lie in a common rectangle at every integer time, so their orbit distances are <μ<γ and they are equal. Denote the unique point π(a). For each ζ>0 define C_N⊆Λ×Λ by d*(x,y)≥ζ and d*(f^j x,f^j y)≤γ for all |j|≤N. These are decreasing closed subsets of compact Λ×Λ. Their total intersection is empty by expansivity. If all were nonempty the nested-compact theorem would contradict this; hence some C_N is empty. Consequently agreement within γ for the finite window |j|≤N forces initial distance <ζ. This is Bowen Lemma4’s compactness argument, with strict conclusion and the exact expansive bound.

9. Compact code space and continuity of coding
Give {1,…,N} its finite discrete topology and the sequence space its product topology. It is compact by finite-space compactness and compactness of arbitrary products. For each j, the legal adjacent-coordinate condition is a clopen cylinder condition, being a finite union of specified-coordinate cylinders. Their intersection Σ_B is closed, hence compact. If two codes agree on the finite window from the previous step, their iterates of π lie in the same rectangles throughout that window, so their d*-distance at time0 is <ζ. Equality on finitely many coordinates describes an open cylinder neighborhood in Σ_B. This proves continuity into (Λ,d*), and uniform continuity of the identity proves continuity into (Λ,d). A legal bi-infinite sequence is not presumed to exist from a matrix-entry condition alone; existence will also follow from the dense interior itineraries in the next step.

10. Onto from boundary-avoiding orbits, not from periodic-point density
Let Y=⋃_i int_Λ R_i. It is open, and Λ=⋃_i R_i=⋃_i closure(int R_i)⊆closure(Y), so Y is dense. Every f^(−j)Y is open and dense because f|Λ is a homeomorphism. Compact metric Λ is locally compact and R1, hence Baire; the countable dense-open intersection X=⋂_(j∈Z)f^(−j)Y is dense by the named Baire theorem. Since Λ is nonempty, X is nonempty. For x∈X each f^j x lies in exactly one rectangle interior, by disjointness. Its labels form a legal sequence: f^j x itself witnesses the transition into the next interior. The full itinerary intersection contains x, so π sends this sequence to x. Thus the image of π contains the dense set X. The domain Σ_B is compact and π continuous, so its image is compact and closed in the metric Hausdorff Λ. It therefore equals Λ. This handles all boundary points by closedness of the image rather than choosing arbitrary legal labels for them. No spectral decomposition, nonwandering-set equality or dense periodic points is used.

11. Covariance and splice estimates in the original distance
For a∈Σ_B the shifted sequence σa has labels (σa)_j=a_(j+1), and fπ(a) belongs to every f^(−j)R_(a_(j+1)). Uniqueness gives π(σa)=fπ(a). If a0=b0, the proposed c has all negative transitions from a and all nonnegative transitions from b; the transitions at −1→0 and 0→1 are legal because the shared zero symbol agrees. For j≥0 both f^jπ(c) and f^jπ(b) lie in R_(b_j), whose original d-diameter is <ε. For j≤0 both f^jπ(c) and f^jπ(a) lie in R_(a_j). These are exactly the asserted strict bounds, including j=0. No global injectivity of π on boundary itineraries is used.

12. Scope and edge cases
The chosen point hypothesis is Λ≠∅, so the finite covering family is nonempty. A finite periodic Λ is permitted: relative rectangle interiors may be singletons, legal codes include its cyclic itineraries, and onto/uniqueness/continuity remain valid. Dimension0 or a zero-rank stable/unstable bundle uses singleton factors in the relative product topology; no positive-dimensional disk or connected rectangle assumption was introduced. Transitivity is part of the unchanged statement but is unnecessary for the coding assertions proved here; Bowen uses it later in Proposition30 to prove transitivity of the symbolic shift. No assertion of mixing, primitive transition matrix, smooth toral atlas or transverse differentiability has been added.

13. The constructed partition meets the finite-pattern source guards
Keep exactly the R_i, B and π already constructed; no new partition is selected in the fibre proof. In the adapted metric d* every R_i has diameter <μ<α7<α3, is compact regular closed and bracket closed, and has the witnessed interior Markov inclusions. Thus it meets Bowen1970a p.729 rectangle definition and p.731 Markov definition. The chosen descending α0,…,α7 and uniform-continuity guards supply the strict common collars for Lemmas8–9 pp.729–730 and Lemma11(a) pp.730–731. The preceding closed-overlap step has already proved Lemma25(a) for this partition. The rectangle-slice provider gives regular-closed factors in full γ-plaques, and the preceding relative-plaque openness step proves their transport on open germs. These are precisely the inputs used by Bowen1970b Lemmas1–2 and6 pp.908–911. Every later rebase is taken on a sufficiently small germ where both bracket expressions lie in these collars; the germ may be reduced separately at each point and integer iterate. There is no assertion that a large iterate preserves a fixed γ-plaque, no inference of α3-smallness from an arbitrary original-metric expansive bound, and no appeal to the open arbitrary-partition fibre node. The compact Fact1 and proper-partition foundations remain the same named independent dependencies.

14. Every rectangle label is realized by a code: Lemma1(a), p.908
For i∈{1,…,N}, let C_i={a∈Σ_B:a_0=i}. This is a closed coordinate cylinder in the already compact code space. Its continuous image π(C_i) is compact and therefore closed in Λ, and the itinerary definition gives π(C_i)⊆R_i. The dense boundary-avoiding set X constructed in the onto step meets every nonempty relative open subset of int_Λ R_i. For x∈X∩int_Λ R_i its unique interior itinerary has zero label i, so x∈π(C_i). Thus int_Λ R_i⊆closure π(C_i)=π(C_i); properness R_i=closure(int_Λ R_i) gives π(C_i)=R_i. For S(x)={i:x∈R_i}, this proves S(x)={a_0:π(a)=x}. The shift is a homeomorphism of Σ_B, and πσ=fπ holds for every integer power, so {i:f^j x∈R_i}={a_j:π(a)=x} for every j∈Z. This is the closed-cylinder argument of Bowen1970a Proposition31 pp.742–743 used in Bowen1970b Lemma1(a), with the very same chosen π.

15. Relative slice frontiers and boundary perturbations: Lemma2, pp908–909
Use [u,v]=Wˢ_loc(u)∩Wᵘ_loc(v). In the guarded product coordinates a rectangle E is C×D with compact regular-closed factors. Its unstable boundary ∂ᵘE is C×(D∖int D), and its stable boundary is (C∖int C)×D. Hence each unstable boundary has closed nowhere-dense trace on any sufficiently small stable crossing, by stable rebase; the stable boundary has the dual property on unstable crossings. Indeed a regular-closed factor has frontier with empty interior, since every neighborhood of a factor point meets its interior. Compactness of each factor and continuity of the bracket also make these boundary sets closed in Λ. Put B_u=⋃E∂ᵘE and B_s=⋃E∂ˢE; only this finite union is covered by the finite-union leaf. If z∉B_u, then O_z=(⋂_(E∈S(z))int_(Wγˢ(z))Wˢ(z,E))∖⋃_(E∉S(z))E is an open stable-germ neighborhood of z, has constant S(z′)=S(z), and avoids B_u. Fix a closed small stable core K about z, strictly inside a larger γ-stable germ. For each fixed integer n, f^(−n) restricted to a sufficiently small germ about each point of K is a homeomorphism onto an open stable germ. This uses the already proved one-step plaque openness in both time directions, iterated with collars reduced at every intermediate image; equivalently the finitely many orbit inequalities added or removed by this iterate are made strict using continuity, and the remaining inequalities follow from contraction in the larger plaque. Compactness of f^(−n)K gives a finite cover by these open γ-stable germs. In each germ the trace of B_u is closed nowhere dense. Transporting the cover by f^n shows that the trace of f^n(B_u) in the interior of K is closed nowhere dense: a nonempty open subset in that trace would pull back to a nonempty open subset of one of the finitely many covered germs, contradicting its local nowhere-density. This is Bowen p.909 finite-cover argument, separately for each n; no cover or collar is asserted uniform in n. The closed γ-plaque is compact as a closed subset of compact Λ. Its metric topology is R1 and weakly locally compact; the named conversion gives local compactness, inherited by the strict open germ and O_z through the named open-embedding theorem. Thus O_z is Baire. For a fixed nearby x, the stable rebase z′↦[x,z′] is a homeomorphism on small open stable germs: in the product chart its image is the intersection of an open product with the target plaque, and bracket absorption supplies the inverse rebase, exactly Bowen1970a Lemma8 p.729. Therefore the inverse image of B_u is also closed nowhere dense. Apply the countable dense-open-intersection theorem in this same O_z to the complements of all integer-iterate traces and this one rebase trace. Every prescribed nonempty open neighborhood of z in O_z contains a z′ with S(z′)=S(z), z′∉⋃_(n∈Z)f^n(B_u), and [x,z′]∉B_u. This is Bowen1970b Lemma2 pp.908–909. The conclusion is a dense complement, not the false assertion that a countable nowhere-dense union is itself nowhere dense. Apply the identical argument to f⁻¹, exchanging stable/unstable and B_u/B_s.

16. Pattern sets and their finite stabilization: p908 and Proposition3 pp909–910
Define J_s(x)={P⊆I: for every δ>0 some z∈Wˢ_δ(x)∖B_u has S(z)=P}; define J_u using unstable germs and B_s. These are families of nonempty subsets. They are nonempty: a rectangle containing x has a stable slice regular closed at x; each neighborhood of x contains a nonempty relatively open subset of this slice, which cannot be exhausted by finitely many stable slice frontiers. Choose points tending to x outside B_u and pass to a repeated membership pattern among the finitely many subsets of I. The same argument gives J_u≠∅, including singleton zero-dimensional plaques where the slice frontier is empty. For each P not in J_s(x) there is a positive radius with no such representative; take the minimum of these finitely many radii. Thus for sufficiently small δ_s(x), every boundary-avoiding stable representative near x already realizes a member of J_s(x). Make the dual choice too. Excluding rectangles not containing x gives a neighborhood on which S(y)⊆S(x); shrink it so [x,y] and [y,x] lie strictly in these small germs. Bracket closure yields S([p,q])⊇S(p)∩S(q). For y in this neighborhood and z stable-near y put z*=[x,z]. Then z=[y,z*] and S(z)⊆S(y)⊆S(x), so the two bracket inclusions give S(z)=S(y)∩S(z*). Lemma2 permits the needed boundary exclusions without changing S(z), and permits the reverse perturbation from z*. The two germ homeomorphisms preserve arbitrary closeness. Consequently J_s(y)={P∩S(y):P∈J_s([x,y])}; the inverse-time argument gives its unstable dual. This is Proposition3’s actual membership calculation; Corollaries4–5 are unnecessary for the fibre bound.

17. Closed-overlap Markov laws and the merge obstruction: Lemma6, p911
For a witnessed transition E→F the two plaque inclusions hold at every x∈E∩f⁻¹F, including its boundary. This is Bowen1970a Lemma25 pp739–740: transport a target unstable point to the witness with the bracket, pull it back by the witnessed unstable covering, and rebase to x; guarded bracket covariance proves that the resulting source point maps to the original target point. The inverse-time argument yields the stable inclusion. Suppose now E₁≠E₂, x∈E₁∩E₂∩f⁻¹F and both transitions E_i→F are witnessed. Then V=Wᵘ(x,E₁)∩Wᵘ(x,E₂) contains f⁻¹Wᵘ(fx,F). The latter is regular closed at x in an open unstable germ, so V contains nonempty open subsets arbitrarily close to x. Choose x′∈V∖B_s. Distinct proper partition elements have intersection contained in their frontiers: an interior point of E₁ belonging to E₂ would be approximated inside E₁ by int E₂, contradicting disjoint interiors. Thus x′∈∂E₁. Since x′ is not in its stable boundary, it belongs to ∂ᵘE₁. In product coordinates unstable rebase preserves the stable-factor boundary coordinate. Both x′ and x lie in the same E₁ unstable slice, so x∈∂ᵘE₁⊆B_u. This proves Lemma6(b). It is not a claim that every closed overlap is a legal transition: the witnessed transition hypotheses are retained.

18. Unique predecessor maps on boundary-avoiding patterns: Lemma7, pp911–912
For z∉B_u and each F∈S(fz), every-label coding gives a code over fz with its zero label F. Shift it back to obtain a predecessor E∈S(z) with E→F. Lemma6(b) makes this E unique; call it T_z(F). For each E∈S(z), choose a code over z with zero label E; its next label F has T_z(F)=E. Thus T_z:S(fz)→S(z) is surjective. If y is stable-near z, both avoid B_u, and S(y)=S(z), then for every F∈S(fz), E=T_z(F) contains both y and z in its same stable slice. The closed-overlap stable law gives fy∈F, hence S(fz)⊆S(fy). Applying the same argument from y to z gives equality. The map T is determined solely by these two label sets and the transition matrix, so T_y=T_z. Apply this exact argument to f⁻¹ to get the dual unique successor map when z∉B_s.

19. A surjection of stable pattern families: Proposition8, p912
For P∈J_s(x), choose boundary-avoiding representatives z→x with S(z)=P. Lemma2 allows representatives avoiding every iterate of B_u; in particular fz avoids B_u. Lemma7 makes S(fz) independent of the chosen sufficiently close representative. Define R_x(P)=S(fz). The representatives can be made arbitrarily close to x, so their images tend to fx on its stable germ and show R_x(P)∈J_s(fx). For Q∈J_s(fx), choose w arbitrarily close to fx in its stable germ with S(w)=Q; Lemma2 perturbs within that germ, preserving Q, so w avoids both B_u and f(B_u). Then z=f⁻¹w is outside B_u and tends to x; finite stabilization ensures S(z)∈J_s(x). Its image pattern is Q. Thus R_x:J_s(x)→J_s(fx) is surjective. For every P choose its representative z; Lemma7 also gives the surjection T_z:R_x(P)→P, hence |R_x(P)|≥|P|. Repeat for f⁻¹ with J_u.

20. Finite tuple order and monotonicity: pp910–912
Choose L≥max(N,2^N). Let K_L consist of descending tuples (a₁,…,a_n) with 1≤n≤L and 1≤a_i≤L. Define a≽b if length(a)>length(b), or lengths agree and b_i≥a_i for every i; equality is allowed and strict dominance excludes equality. This is a finite partial order. Sort the cardinalities of the members of J_s(x) to form A_s(x)∈K_L, and similarly A_u(x). To compare A_s(x)=(a₁,…,a_n) and A_s(fx)=(b₁,…,b_m), R_x induces a surjection g:{1,…,n}→{1,…,m}. If n>m the first tuple strictly dominates. If n=m, g is a bijection and b_(g(i))≥a_i by T_z. For each i, injectivity prevents g({1,…,i}) from being contained in {1,…,i−1}; choose j≤i with g(j)≥i. Descending order gives b_i≥b_(g(j))≥a_j≥a_i. Thus A_s(x)≽A_s(fx). Its dual is A_u(x)≽A_u(f⁻¹x). This proves Proposition8’s reversed-cardinality order, rather than substituting ordinary lexicographic order.

21. Strict pattern decrease at a branch: Proposition9, pp912–913
An s-branch point x has two codes over x with the same label E at time0 and distinct labels F₁,F₂ at time1. Both witnessed transitions E→F_i hold and fx∈F₁∩F₂. By regular-closedness of Wˢ(x,E), any small stable germ about x contains an open subset of that slice. Remove B_u there and choose z sufficiently close to x so S(z)∈J_s(x). The closed-overlap stable laws give fz∈F₁∩F₂. Lemma7 forces T_z(F₁)=T_z(F₂)=E, so this surjection is not injective. If A_s(x)=A_s(fx), the pattern surjection g from the preceding step is bijective and the two tuple sums are equal. The inequalities a_i≤b_(g(i)) then sum to equality, so all are equal. Every finite surjection T_z between corresponding label patterns would be a bijection, contradicting the displayed collision. Hence A_s(x)≻A_s(fx). The inverse-time argument gives strict decrease of A_u at u-branches. The source printed E=1 in this last collision merely labels the common predecessor; no distinguished rectangle1 is assumed.

22. Uniform fibre count: Proposition10, p913
Let e be the maximum number of strict inequalities in a chain of finite K_L. Any forward orbit has at most e s-branch times: monotonicity holds at every time and strictness holds at each branch, so e+1 branch times would produce an impossible strict chain. Let A_n(x) be the legal words (a₀,…,a_n) appearing in full codes over x. There are at most N initial labels. Every word extends because it already comes from a full code. At a nonbranch time n, two full codes with the same prefix, hence the same nth label, must have the same next label. Thus restriction A_(n+1)(x)→A_n(x) is bijective. At a branch it has at most N extensions per word. Therefore |A_n(x)|≤N^(e+1) for all n. If more than this many distinct forward half-codes existed, select a finite excess family; each pair differs at a finite coordinate, and the largest of these coordinates produces too many distinct words in one A_n. The reverse-time argument bounds backward half-codes by N^(e+1). A full code is determined by its two halves, yielding |π⁻¹{x}|≤D=N^(2(e+1)). N≥1 since the partition covers nonempty Λ, so D≥1. The source counts chain vertices instead of strict drops; this harmless enlarged bound avoids an off-by-one convention.

23. Periodicity and coordinate rigidity: Corollary11 p913, Proposition12 p914
If f^m x=x with m≥1, covariance makes σ^m a bijection of the finite nonempty fibre over x. Every element of a finite set permuted bijectively returns after finitely many applications, so every code is periodic, with a period dividing m times its cycle length. No equality with the least period of x is claimed. The tuples A_s(f^j x) are monotone around its finite physical orbit and return to the starting tuple; antisymmetry forces equality at every step. The same holds for A_u in reverse time. Strict branch decrease therefore forbids every s-branch and u-branch on this orbit. If codes a,b over x agree at coordinate j, apply the no-s-branch assertion at f^j x to σ^j a,σ^j b to obtain agreement at j+1, and the no-u-branch assertion to obtain agreement at j−1. Induction proves equality at all coordinates. Every-label coding gives surjectivity of the coordinate-j map onto S(f^j x), and this rigidity gives injectivity. Thus it is a bijection for periodic x. This is exactly Proposition12 applied to constant-rank periodic orbits; no such rigidity is asserted over arbitrary nonperiodic x.
-/
theorem hyperbolic_basic_set_markov_coding
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (_hmetric : HasOriginalRiemannianDistance (E := E) (M := M))
    (Λ : Set M) (hΛne : Λ.Nonempty) (hΛcompact : IsCompact Λ)
    (hΛinvariant : ∀ x : M, x ∈ Λ ↔ f x ∈ Λ)
    (stable unstable : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x))
    (hstableContinuous : IsContinuousDistributionOn Λ stable)
    (hunstableContinuous : IsContinuousDistributionOn Λ unstable)
    (hcompl : ∀ x ∈ Λ, IsCompl (stable x) (unstable x))
    (hstableInvariant : ∀ x ∈ Λ,
      (stable x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap = stable (f x))
    (hunstableInvariant : ∀ x ∈ Λ,
      (unstable x).map (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap = unstable (f x))
    (C rate : ℝ) (hC : 1 ≤ C) (hratepos : 0 < rate) (hratelt : rate < 1)
    (hstableBound : ∀ (n : ℕ) (x : M), x ∈ Λ → ∀ v ∈ stable x,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f : M → M)^[n]) x v‖ ≤ C * rate ^ n * ‖v‖)
    (hunstableBound : ∀ (n : ℕ) (x : M), x ∈ Λ → ∀ v ∈ unstable x,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((f.symm : M → M)^[n]) x v‖ ≤ C * rate ^ n * ‖v‖)
    (hlocalMaximal : ∃ U : Set M, IsOpen U ∧ Λ ⊆ U ∧
      Λ = ⋂ j : ℤ, ((f.toHomeomorph ^ j : M ≃ₜ M) : M → M) '' U)
    (_htransitive :
      let F := restrictedDynamics f.toHomeomorph Λ hΛinvariant
      ∀ U V : Set Λ, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
        ∃ n : ℕ, (((F ^ n : Λ ≃ₜ Λ) : Λ → Λ) '' U ∩ V).Nonempty) :
    ∀ ε : ℝ, 0 < ε →
      let F := restrictedDynamics f.toHomeomorph Λ hΛinvariant
      ∃ (N D : ℕ), 1 ≤ N ∧ 1 ≤ D ∧
      ∃ (δ : MetricSpace Λ), δ.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace Λ) ∧
      ∃ (γ : ℝ), 0 < γ ∧ ∃ R : Fin N → Set Λ,
        (∀ i, IsRectangle F δ.dist γ (R i) ∧ Metric.diam (R i) < ε) ∧
        (∀ i j, i ≠ j → Disjoint (interior (R i)) (interior (R j))) ∧
        (⋃ i, R i) = univ ∧ HasMarkovInclusions F δ.dist γ R ∧
        let B := transition F R
        ∃ coding : CodeSpace B → Λ,
          (∀ a, {x : Λ | ∀ j : ℤ, (F ^ j) x ∈ R (a.val j)} = {coding a}) ∧
          Continuous coding ∧ Function.Surjective coding ∧
          (∀ a, coding (codeShift B a) = F (coding a)) ∧
          (∀ x : Λ, {a : CodeSpace B | coding a = x}.encard ≤ (D : ℕ∞)) ∧
          (∀ (x : Λ) (j : ℤ) (i : Fin N), (F ^ j) x ∈ R i ↔
            ∃ a : CodeSpace B, coding a = x ∧ a.val j = i) ∧
          (∀ x : Λ, (∃ m : ℕ, 0 < m ∧ (F ^ m) x = x) →
            (∀ a : CodeSpace B, coding a = x →
              ∃ m : ℕ, 0 < m ∧ (codeShift B)^[m] a = a) ∧
            (∀ a b : CodeSpace B, coding a = x → coding b = x →
              (∃ j : ℤ, a.val j = b.val j) → a = b) ∧
            (∀ j : ℤ, Set.BijOn (fun a : CodeSpace B => a.val j)
              {a | coding a = x} {i | (F ^ j) x ∈ R i})) ∧
          (∀ a b : CodeSpace B, a.val 0 = b.val 0 →
            ∃ c : CodeSpace B,
              (∀ j : ℤ, j ≤ 0 → c.val j = a.val j) ∧
              (∀ j : ℤ, 0 ≤ j → c.val j = b.val j) ∧
              (∀ j : ℤ, 0 ≤ j → dist ((F ^ j) (coding c)) ((F ^ j) (coding b)) < ε) ∧
              (∀ j : ℤ, j ≤ 0 → dist ((F ^ j) (coding c)) ((F ^ j) (coding a)) < ε)) := by
  obtain ⟨H, hHstable, hHunstable⟩ := exists_original_factOne_datum f Λ hΛne hΛcompact
    hΛinvariant stable unstable hstableContinuous hunstableContinuous hcompl
    hstableInvariant hunstableInvariant C rate hC hratepos hratelt hstableBound
    hunstableBound hlocalMaximal
  classical
  intro ε hε
  let tM : TopologicalSpace M := inferInstance
  let originalMetric : MetricSpace Λ := inferInstance
  let d₀ : Λ → Λ → ℝ := originalMetric.dist
  have hd₀ : Continuous (fun p : Λ × Λ ↦ d₀ p.1 p.2) := continuous_dist
  have hd₀diag : ∀ x, d₀ x x = 0 := fun x ↦ dist_self x
  obtain ⟨d, ht, hproduct⟩ := original_factOne_gives_compact_product_data f Λ H hΛinvariant
  let : MetricSpace M := @MetricSpace.replaceTopology M tM d ht.symm
  let : MetricSpace Λ := @Subtype.metricSpace M (fun x ↦ x ∈ Λ) inferInstance
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp hΛcompact
  let : Nonempty Λ := hΛne.to_subtype
  have htopΛ : (inferInstance : MetricSpace Λ).toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced Subtype.val tM := by
    rfl
  have hclosure (A : Set Λ) :
      @closure Λ (inferInstance : MetricSpace Λ).toUniformSpace.toTopologicalSpace A =
        @closure Λ (TopologicalSpace.induced Subtype.val tM) A := by
    rw [htopΛ]
  obtain ⟨κ, γ, ⟨G⟩⟩ := hproduct
  let F := restrictedDynamics f.toHomeomorph Λ hΛinvariant
  -- Choose Bowen's adapted scales BEFORE choosing the coding partition.
  have hmodulus : ∀ δ : {δ : ℝ // 0 < δ}, ∃ η : ℝ, 0 < η ∧
      η ≤ G.closeRadius ∧ ∀ x y, dist x y ≤ η →
        G.bracket x y ∈ Dynamics.relativeClosedStablePlaque F δ.val x ∩
          Dynamics.relativeClosedUnstablePlaque F δ.val y := fun δ ↦
    factOne_narrow_bracket_modulus F γ κ G.closeRadius G.gamma_pos
      G.lambda_pos.le G.lambda_lt_one.le G.closeRadius_pos G.bracket
      G.bracket_mem G.bracket_unique G.bracket_continuous
      G.stable_contraction G.unstable_contraction δ.val δ.property
  choose η hη hηcore hηmem using hmodulus
  let εmod : ℝ → ℝ := fun δ ↦ if h : 0 < δ then η ⟨δ, h⟩ else G.closeRadius
  have hmodpos : ∀ δ, 0 < δ → 0 < εmod δ := by
    intro δ hδ
    simpa only [εmod, dite_eq_left hδ] using hη ⟨δ, hδ⟩
  obtain ⟨α, hα0, hαpos, hαdesc, hαmesh, hαscale, hαmap⟩ :=
    exists_factOne_refinement_scales F γ (min (γ / 2) G.closeRadius) G.gamma_pos
      (lt_min (half_pos G.gamma_pos) G.closeRadius_pos) εmod hmodpos
  obtain ⟨N, hN, R, hrect, hadaptedDiam, hbound, hdisj, hcover, hmarkov, hclosed,
    coding, hit, hcont, honto, hcov, hlabels, hsplice⟩ :=
    exists_canonical_coding_with_original_splice F γ κ G d₀ hd₀ hd₀diag ε hε
      (α 7) (hαpos 7)
  have hα7mesh : α 7 < min (γ / 2) G.closeRadius := hαmesh 6
  have hα73 : α 7 < α 3 :=
    (hαdesc 6).trans ((hαdesc 5).trans ((hαdesc 4).trans (hαdesc 3)))
  have hrectSmall : ∀ i, Metric.diam (R i) < α 3 := fun i ↦
    (hadaptedDiam i).trans hα73
  have hrectClose : ∀ i, Metric.diam (R i) ≤ G.closeRadius := fun i ↦
    ((hadaptedDiam i).trans hα7mesh).le.trans (min_le_right _ _)
  have hrectStrict : ∀ i, Metric.diam (R i) < γ / 2 := fun i ↦
    ((hadaptedDiam i).trans hα7mesh).trans_le (min_le_left _ _)
  have hrectBracket : ∀ i, ∀ p ∈ R i, ∀ q ∈ R i, G.bracket p q ∈ R i := by
    intro i p hp q hq
    obtain ⟨z, hz, huniq⟩ := (hrect i).2.2.2 p hp q hq
    have hclose : dist p q ≤ G.closeRadius :=
      (Metric.dist_le_diam_of_mem (hrect i).2.1.isBounded hp hq).trans (hrectClose i)
    have hm := G.bracket_mem p q hclose
    have heq : G.bracket p q = z := (huniq (G.bracket p q)).mp (by
      simpa only [localStable_eq_relative, localUnstable_eq_relative, Set.mem_inter_iff,
        F, restrictedDynamics] using hm)
    exact heq.symm ▸ hz
  -- Apply the published native-plaque slice theorem to this actual partition.
  let αN : ℕ → ℝ := fun n ↦ α ⟨n % 8, Nat.mod_lt n (by norm_num)⟩
  have hαN : ∀ n, n ≤ 3 → 0 < αN (n + 1) ∧ αN (n + 1) < αN n ∧
      αN (n + 1) < (1 / 3 : ℝ) * min (αN n / 3) (εmod (αN n / 3)) := by
    intro n hn
    simp only [αN, Nat.mod_eq_of_lt (show n < 8 by omega),
      Nat.mod_eq_of_lt (show n + 1 < 8 by omega)]
    exact ⟨hαpos ⟨n + 1, by omega⟩, hαdesc ⟨n, by omega⟩, hαscale ⟨n, by omega⟩⟩
  have hαNmap : ∀ n, n ≤ 3 → ∀ {x y : Λ}, dist x y ≤ αN (n + 1) →
      dist (F x) (F y) < αN n ∧ dist (F.symm x) (F.symm y) < αN n := by
    intro n hn x y hxy
    simp only [αN, Nat.mod_eq_of_lt (show n < 8 by omega),
      Nat.mod_eq_of_lt (show n + 1 < 8 by omega)] at hxy ⊢
    exact hαmap ⟨n, by omega⟩ x y hxy
  have hrectSlices (i : Fin N) := bowen_fact1_rectangle_slices_g6
    F κ γ G.closeRadius G.lambda_pos G.lambda_lt_one G.gamma_pos G.closeRadius_pos
    G.bracket
    (by
      intro x y z hy hz n
      simpa only [Bowen.RectangleSlicesPreparation.homeomorph_pow_apply, F, restrictedDynamics] using
        G.stable_contraction x y z
          (by simpa only [Bowen.RectangleSlicesPreparation.stablePlaque,
            Dynamics.relativeClosedStablePlaque, Set.mem_ofPred_eq,
            Bowen.RectangleSlicesPreparation.homeomorph_pow_apply, F, restrictedDynamics] using hy)
          (by simpa only [Bowen.RectangleSlicesPreparation.stablePlaque,
            Dynamics.relativeClosedStablePlaque, Set.mem_ofPred_eq,
            Bowen.RectangleSlicesPreparation.homeomorph_pow_apply, F, restrictedDynamics] using hz) n)
    (by
      intro x y z hy hz n
      simpa only [Bowen.RectangleSlicesPreparation.homeomorph_pow_apply, F, restrictedDynamics] using
        G.unstable_contraction x y z
          (by simpa only [Bowen.RectangleSlicesPreparation.unstablePlaque,
            Dynamics.relativeClosedUnstablePlaque, Set.mem_ofPred_eq,
            Bowen.RectangleSlicesPreparation.homeomorph_pow_apply, F, restrictedDynamics] using hy)
          (by simpa only [Bowen.RectangleSlicesPreparation.unstablePlaque,
            Dynamics.relativeClosedUnstablePlaque, Set.mem_ofPred_eq,
            Bowen.RectangleSlicesPreparation.homeomorph_pow_apply, F, restrictedDynamics] using hz) n)
    (by
      intro x y hxy
      simpa only [Bowen.RectangleSlicesPreparation.stablePlaque,
        Bowen.RectangleSlicesPreparation.unstablePlaque,
        Dynamics.relativeClosedStablePlaque, Dynamics.relativeClosedUnstablePlaque,
        Set.mem_inter_iff, Set.mem_ofPred_eq,
        Bowen.RectangleSlicesPreparation.homeomorph_pow_apply, F, restrictedDynamics] using G.bracket_mem x y hxy)
    (by
      intro x y z hxy hz
      exact G.bracket_unique x y z hxy (by
        simpa only [Bowen.RectangleSlicesPreparation.stablePlaque,
          Bowen.RectangleSlicesPreparation.unstablePlaque,
          Dynamics.relativeClosedStablePlaque, Dynamics.relativeClosedUnstablePlaque,
          Set.mem_inter_iff, Set.mem_ofPred_eq,
          Bowen.RectangleSlicesPreparation.homeomorph_pow_apply, F, restrictedDynamics] using hz))
    G.bracket_continuous εmod (fun δ hδ _ ↦ hmodpos δ hδ)
    (by
      intro x y δ hδ hδγ hxy
      have hh := hηmem ⟨δ, hδ⟩ x y (by simpa only [εmod, dite_eq_left hδ] using hxy)
      simpa only [Bowen.RectangleSlicesPreparation.stablePlaque,
        Bowen.RectangleSlicesPreparation.unstablePlaque,
        Dynamics.relativeClosedStablePlaque, Dynamics.relativeClosedUnstablePlaque,
        Set.mem_inter_iff, Set.mem_ofPred_eq,
        Bowen.RectangleSlicesPreparation.homeomorph_pow_apply, F, restrictedDynamics] using hh)
    αN hα0 hαN hαNmap (R i) (hrect i).1 (hrect i).2.1
    (fun hp hq ↦ hrectBracket i _ hp _ hq) (hrectSmall i).le (hrect i).2.2.1
    (fun q ↦ R i ∩ Bowen.RectangleSlicesPreparation.unstablePlaque F γ q)
    (fun q ↦ R i ∩ Bowen.RectangleSlicesPreparation.stablePlaque F γ q)
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
  have hnativeChart := Bowen.bowen_fact1_product_chart_g6
    F κ γ G.closeRadius G.lambda_pos G.lambda_lt_one G.gamma_pos G.closeRadius_pos
    (fun i : Fin 5 ↦ α ⟨i.val, by omega⟩) εmod (fun δ hδ _ ↦ hmodpos δ hδ)
    hα0 (fun i ↦ hαpos ⟨i.val, by omega⟩)
    (fun i ↦ hαscale ⟨i.val, by omega⟩)
    (fun i a b hab ↦ hαmap ⟨i.val, by omega⟩ a b hab) G.bracket
    (by
      intro x y z n hy hz
      simpa only [F, restrictedDynamics] using G.stable_contraction x y z hy hz n)
    (by
      intro x y z n hy hz
      simpa only [F, restrictedDynamics] using G.unstable_contraction x y z hy hz n)
    (by
      intro x y hxy
      refine ⟨G.bracket x y, ?_, ?_⟩
      · exact G.bracket_mem x y hxy
      · intro z hz
        exact G.bracket_unique x y z hxy hz)
    (by
      intro x y hxy
      exact G.bracket_mem x y hxy)
    G.bracket_continuous
    (by
      intro δ hδ hδγ x y hxy
      have hh := hηmem ⟨δ, hδ⟩ x y (by simpa only [εmod, dite_eq_left hδ] using hxy)
      exact hh)
  have hnativeRebase (x y : Λ) (hxy : dist x y ≤ α 3) :=
    Bowen.bowen_fact1_plaque_rebase_g6
      F κ γ G.closeRadius G.lambda_pos G.lambda_lt_one G.gamma_pos G.closeRadius_pos
      (fun i : Fin 5 ↦ α ⟨i.val, by omega⟩) εmod (fun δ hδ _ ↦ hmodpos δ hδ)
      hα0 (fun i ↦ hαpos ⟨i.val, by omega⟩)
      (fun i ↦ hαscale ⟨i.val, by omega⟩)
      (fun i a b hab ↦ hαmap ⟨i.val, by omega⟩ a b hab) G.bracket
      (by
        intro c a b n ha hb
        simpa only [F, restrictedDynamics] using G.stable_contraction c a b ha hb n)
      (by
        intro c a b n ha hb
        simpa only [F, restrictedDynamics] using G.unstable_contraction c a b ha hb n)
      (by
        intro a b hab
        refine ⟨G.bracket a b, G.bracket_mem a b hab, ?_⟩
        intro z hz
        exact G.bracket_unique a b z hab hz)
      (fun a b hab ↦ G.bracket_mem a b hab)
      G.bracket_continuous
      (by
        intro δ hδ hδγ a b hab
        exact hηmem ⟨δ, hδ⟩ a b (by simpa only [εmod, dite_eq_left hδ] using hab))
      x y hxy
  let chartRadius : ℝ := (α 3 + α 2) / 2
  have hchartRadiusLow : α 3 < chartRadius := by
    dsimp [chartRadius]
    have hd : α 3 < α 2 := hαdesc 2
    linarith
  have hchartRadiusHigh : chartRadius < α 2 := by
    dsimp [chartRadius]
    have hd : α 3 < α 2 := hαdesc 2
    linarith
  let chartU : Λ → Set Λ := fun q ↦ Metric.ball q chartRadius ∩
    Dynamics.relativeClosedUnstablePlaque F γ q
  let chartV : Λ → Set Λ := fun q ↦ Metric.ball q chartRadius ∩
    Dynamics.relativeClosedStablePlaque F γ q
  have hcommonChart (q : Λ) := hnativeChart.2 q (chartU q) (chartV q)
    (by
      intro z hz n
      have hh := G.unstable_contraction q z q hz.2
        (fun _ ↦ by simp [G.gamma_pos.le]) n
      exact hh.trans ((mul_le_mul_of_nonneg_right
        (pow_le_one₀ G.lambda_pos.le G.lambda_lt_one.le) dist_nonneg).trans
        (by
          change 1 * dist z q ≤ α 2
          simpa only [one_mul] using (Metric.mem_ball.mp hz.1).le.trans hchartRadiusHigh.le)))
    (by
      intro z hz n
      have hh := G.stable_contraction q z q hz.2
        (fun _ ↦ by simp [G.gamma_pos.le]) n
      exact hh.trans ((mul_le_mul_of_nonneg_right
        (pow_le_one₀ G.lambda_pos.le G.lambda_lt_one.le) dist_nonneg).trans
        (by
          change 1 * dist z q ≤ α 2
          simpa only [one_mul] using (Metric.mem_ball.mp hz.1).le.trans hchartRadiusHigh.le)))
    (by
      change IsOpen {u : Dynamics.relativeClosedUnstablePlaque F γ q | (u : Λ) ∈ chartU q}
      have heq : {u : Dynamics.relativeClosedUnstablePlaque F γ q | (u : Λ) ∈ chartU q} =
          (Subtype.val : Dynamics.relativeClosedUnstablePlaque F γ q → Λ) ⁻¹'
            Metric.ball q chartRadius := by
        ext u
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, u.property⟩⟩
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val)
    (by
      change IsOpen {v : Dynamics.relativeClosedStablePlaque F γ q | (v : Λ) ∈ chartV q}
      have heq : {v : Dynamics.relativeClosedStablePlaque F γ q | (v : Λ) ∈ chartV q} =
          (Subtype.val : Dynamics.relativeClosedStablePlaque F γ q → Λ) ⁻¹'
            Metric.ball q chartRadius := by
        ext v
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, v.property⟩⟩
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val)
  have hcommonFactorGuards (q : Λ) (i : Fin N) (hq : q ∈ R i) :
      R i ∩ Dynamics.relativeClosedUnstablePlaque F γ q ⊆ chartU q ∧
      R i ∩ Dynamics.relativeClosedStablePlaque F γ q ⊆ chartV q := by
    constructor <;> intro z hz
    · exact ⟨Metric.mem_ball.mpr
        (((Metric.dist_le_diam_of_mem (hrect i).2.1.isBounded hz.1 hq).trans_lt
          (hrectSmall i)).trans hchartRadiusLow), hz.2⟩
    · exact ⟨Metric.mem_ball.mpr
        (((Metric.dist_le_diam_of_mem (hrect i).2.1.isBounded hz.1 hq).trans_lt
          (hrectSmall i)).trans hchartRadiusLow), hz.2⟩
  have hnativeRectProduct (q : Λ) (i : Fin N) (hq : q ∈ R i) :
      R i = {z | ∃ u ∈ R i ∩ Dynamics.relativeClosedUnstablePlaque F γ q,
        ∃ v ∈ R i ∩ Dynamics.relativeClosedStablePlaque F γ q, G.bracket u v = z} := by
    obtain ⟨_, _, _, _, _, _, _, heq, _⟩ := hrectSlices i q hq
    simpa only [Bowen.RectangleSlicesPreparation.bracketImage,
      Bowen.RectangleSlicesPreparation.stablePlaque,
      Bowen.RectangleSlicesPreparation.unstablePlaque,
      Dynamics.relativeClosedStablePlaque, Dynamics.relativeClosedUnstablePlaque,
      Set.mem_ofPred_eq, Bowen.RectangleSlicesPreparation.homeomorph_pow_apply, Homeomorph.symm_symm] using heq
  have hcommonRectangleGuard (q : Λ) (i : Fin N) (hq : q ∈ R i) :
      R i ⊆ {z | ∃ u ∈ chartU q, ∃ v ∈ chartV q, G.bracket u v = z} := by
    intro z hz
    rw [hnativeRectProduct q i hq] at hz
    obtain ⟨u, hu, v, hv, heq⟩ := hz
    exact ⟨u, (hcommonFactorGuards q i hq).1 hu,
      v, (hcommonFactorGuards q i hq).2 hv, heq⟩
  have hcommonStableRegular (q : Λ) (i : Fin N) (hqi : q ∈ R i) :
      {v : {v : Dynamics.relativeClosedStablePlaque F γ q // (v : Λ) ∈ chartV q} |
        (v : Λ) ∈ R i} = closure (interior
          {v : {v : Dynamics.relativeClosedStablePlaque F γ q // (v : Λ) ∈ chartV q} |
            (v : Λ) ∈ R i}) := by
    let S := Dynamics.relativeClosedStablePlaque F γ q
    let V : Set S := {v | (v : Λ) ∈ chartV q}
    let D : Set S := {v | (v : Λ) ∈ R i}
    have hVopen : IsOpen V := by
      have heq : V = (Subtype.val : S → Λ) ⁻¹' Metric.ball q chartRadius := by
        ext v
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, v.property⟩⟩
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val
    have hD : D = closure (interior D) := by
      obtain ⟨_, _, _, _, _, _, hd, _, _⟩ := hrectSlices i q hqi
      have hs : Bowen.RectangleSlicesPreparation.stablePlaque F γ q = S := by
        ext z
        simp only [S, Bowen.RectangleSlicesPreparation.stablePlaque,
          Dynamics.relativeClosedStablePlaque, Set.mem_ofPred_eq,
          Bowen.RectangleSlicesPreparation.homeomorph_pow_apply]
      rw [hs] at hd
      simp only [Bowen.RectangleSlicesPreparation.plaqueSlice,
        Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ] at hd
      exact hd
    change (Subtype.val : V → S) ⁻¹' D = closure (interior ((Subtype.val : V → S) ⁻¹' D))
    calc
      (Subtype.val : V → S) ⁻¹' D = Subtype.val ⁻¹' closure (interior D) :=
        congrArg (fun T : Set S ↦ (Subtype.val : V → S) ⁻¹' T) hD
      _ = closure (interior ((Subtype.val : V → S) ⁻¹' D)) := by
        rw [hVopen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val,
          hVopen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage continuous_subtype_val]
  have hcommonPartialChart (q : Λ) :
      ∃ e : OpenPartialHomeomorph Λ
          ({u : Dynamics.relativeClosedUnstablePlaque F γ q // (u : Λ) ∈ chartU q} ×
           {v : Dynamics.relativeClosedStablePlaque F γ q // (v : Λ) ∈ chartV q}),
        e.source = {z | ∃ u ∈ chartU q, ∃ v ∈ chartV q, G.bracket u v = z} ∧
        e.target = Set.univ ∧
        (∀ p, e.symm p = G.bracket (p.1 : Λ) (p.2 : Λ)) ∧
        (∀ i : Fin N, q ∈ R i →
          e.symm ''
            ({u : {u : Dynamics.relativeClosedUnstablePlaque F γ q // (u : Λ) ∈ chartU q} | (u : Λ) ∈ R i} ×ˢ
             {v : {v : Dynamics.relativeClosedStablePlaque F γ q // (v : Λ) ∈ chartV q} | (v : Λ) ∈ R i}) ⊆ R i) := by
    obtain ⟨hWopen, h, hforward, hinverse⟩ := hcommonChart q
    let P := {u : Dynamics.relativeClosedUnstablePlaque F γ q // (u : Λ) ∈ chartU q} ×
      {v : Dynamics.relativeClosedStablePlaque F γ q // (v : Λ) ∈ chartV q}
    let W : Set Λ := {z | ∃ u ∈ chartU q, ∃ v ∈ chartV q, G.bracket u v = z}
    have hqU : q ∈ chartU q := ⟨by simpa using (hαpos 3).trans hchartRadiusLow,
      fun _ ↦ by simpa using G.gamma_pos.le⟩
    have hqV : q ∈ chartV q := ⟨by simpa using (hαpos 3).trans hchartRadiusLow,
      fun _ ↦ by simpa using G.gamma_pos.le⟩
    have : Nonempty P := ⟨⟨⟨⟨q, hqU.2⟩, hqU⟩, ⟨⟨q, hqV.2⟩, hqV⟩⟩⟩
    let g : P → Λ := fun p ↦ (h p : Λ)
    have hg : _root_.Topology.IsOpenEmbedding g :=
      hWopen.isOpenEmbedding_subtypeVal.comp h.isOpenEmbedding
    let e := (hg.toOpenPartialHomeomorph g).symm
    refine ⟨e, ?_, rfl, ?_, ?_⟩
    · change (hg.toOpenPartialHomeomorph g).target = W
      rw [_root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
      ext z
      constructor
      · rintro ⟨p, rfl⟩
        exact (h p).property
      · intro hz
        obtain ⟨p, hp⟩ := h.surjective ⟨z, hz⟩
        exact ⟨p, congrArg Subtype.val hp⟩
    · intro p
      exact hforward p
    · intro i hqi z hz
      obtain ⟨⟨u, v⟩, huv, rfl⟩ := hz
      change (h (u, v) : Λ) ∈ R i
      rw [hforward]
      exact hrectBracket i _ huv.1 _ huv.2
  have hinverseTargetChart (w : Λ) :
      ∃ O : Set (Dynamics.relativeClosedUnstablePlaque F γ (F w)),
        IsOpen O ∧ (⟨F w, fun _ ↦ by simpa using G.gamma_pos.le⟩ :
          Dynamics.relativeClosedUnstablePlaque F γ (F w)) ∈ O ∧
        ∃ g : O → Dynamics.relativeClosedUnstablePlaque F γ w,
          _root_.Topology.IsOpenEmbedding g ∧ ∀ t, (g t : Λ) = F.symm (t : Λ) := by
    obtain ⟨O, V, hO, hV, hwO, hwV, hOopen, hVopen, e, he⟩ :=
      Dynamics.Bowen.stablePlaqueIntegerChart F.symm γ G.gamma_pos (F w) (1 : ℤ)
    simp only [zpow_one, Homeomorph.symm_apply_apply] at hV hwV he
    rw [zpow_one, Homeomorph.symm_apply_apply] at hVopen
    change O ⊆ Dynamics.relativeClosedUnstablePlaque F γ (F w) at hO
    change V ⊆ Dynamics.relativeClosedUnstablePlaque F γ w at hV
    let Os : Set (Dynamics.relativeClosedUnstablePlaque F γ (F w)) := Subtype.val ⁻¹' O
    let Vs : Set (Dynamics.relativeClosedUnstablePlaque F γ w) := Subtype.val ⁻¹' V
    let a : Os ≃ₜ O := _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hO)
    let b : Vs ≃ₜ V := _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hV)
    let c : Os ≃ₜ Vs := (a.trans e).trans b.symm
    let g : Os → Dynamics.relativeClosedUnstablePlaque F γ w := fun t ↦ (c t).val
    have hVs : IsOpen Vs := hVopen
    have hg : _root_.Topology.IsOpenEmbedding g :=
      hVs.isOpenEmbedding_subtypeVal.comp c.isOpenEmbedding
    refine ⟨Os, hOopen, hwO, g, hg, ?_⟩
    intro t
    have hb : (b (c t) : Λ) = (e (a t) : Λ) := by
      exact congrArg Subtype.val (b.apply_symm_apply (e (a t)))
    calc
      (g t : Λ) = (b (c t) : Λ) := rfl
      _ = (e (a t) : Λ) := hb
      _ = F.symm (a t : Λ) := he (a t)
      _ = F.symm (t : Λ) := rfl
  have hinverseTargetImage (q w : Λ) (i j : Fin N)
      (hq : q ∈ R i) (hw : w ∈ R i) (hfw : F w ∈ R j)
      (hij : transition F R i j)
      (t : Λ) (ht : t ∈ R j ∩ Dynamics.relativeClosedUnstablePlaque F γ (F w)) :
      G.bracket (F.symm t) q ∈ R i := by
    obtain ⟨v, hv, hvf⟩ := (hclosed i j hij w hw hfw).2 ht
    have hvEq : v = F.symm t := by rw [← hvf, Homeomorph.symm_apply_apply]
    exact hrectBracket i _ (hvEq ▸ hv.1) q hq
  have hcommonInverseTargetChart (q w : Λ) (hwq : dist w q ≤ α 3)
      (hbq : G.bracket w q ∈ chartU q) :
      ∃ T : Set (Dynamics.relativeClosedUnstablePlaque F γ (F w)),
        IsOpen T ∧ (⟨F w, fun _ ↦ by simpa using G.gamma_pos.le⟩ :
          Dynamics.relativeClosedUnstablePlaque F γ (F w)) ∈ T ∧
        ∃ g : T → {u : Dynamics.relativeClosedUnstablePlaque F γ q // (u : Λ) ∈ chartU q},
          _root_.Topology.IsOpenEmbedding g ∧
          ∀ t, (g t : Λ) = G.bracket (F.symm (t : Λ)) q := by
    obtain ⟨O, hO, hwO, g, hg, hgf⟩ := hinverseTargetChart w
    let U : Set (Dynamics.relativeClosedUnstablePlaque F γ w) :=
      {u | (u : Λ) ∈ chartU w}
    have hU : IsOpen U := by
      have heq : U = (Subtype.val : Dynamics.relativeClosedUnstablePlaque F γ w → Λ) ⁻¹'
          Metric.ball w chartRadius := by
        ext u
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, u.property⟩⟩
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val
    have hUbound : chartU w ⊆ Dynamics.relativeClosedUnstablePlaque F (α 2) w := by
      intro z hz n
      have hh := G.unstable_contraction w z w hz.2
        (fun _ ↦ by simp [G.gamma_pos.le]) n
      exact hh.trans ((mul_le_mul_of_nonneg_right
        (pow_le_one₀ G.lambda_pos.le G.lambda_lt_one.le) dist_nonneg).trans
        (by simpa only [one_mul] using (Metric.mem_ball.mp hz.1).le.trans hchartRadiusHigh.le))
    obtain ⟨hB, hBopen, e, he, hei⟩ := (hnativeRebase w q hwq).1 (chartU w) hUbound hU
    let B : Set (Dynamics.relativeClosedUnstablePlaque F γ q) :=
      {u | (u : Λ) ∈ (fun z : Λ ↦ G.bracket z q) '' chartU w}
    have hB' : IsOpen B := hBopen
    let P : Set O := g ⁻¹' U
    have hP : IsOpen P := hU.preimage hg.continuous
    let gp : P → U := fun t ↦ ⟨g t.val, t.property⟩
    have hgp : _root_.Topology.IsOpenEmbedding gp :=
      _root_.Topology.IsOpenEmbedding.of_comp gp hU.isOpenEmbedding_subtypeVal
        (hg.comp hP.isOpenEmbedding_subtypeVal)
    let r : P → Dynamics.relativeClosedUnstablePlaque F γ q := fun t ↦ (e (gp t)).val
    have hr : _root_.Topology.IsOpenEmbedding r :=
      hB'.isOpenEmbedding_subtypeVal.comp (e.isOpenEmbedding.comp hgp)
    have hrf (t : P) : (r t : Λ) = G.bracket (F.symm (t : Λ)) q := by
      change (e (gp t) : Λ) = _
      exact (he (gp t)).trans (congrArg (fun z ↦ G.bracket z q) (hgf t.val))
    let Uq : Set (Dynamics.relativeClosedUnstablePlaque F γ q) :=
      {u | (u : Λ) ∈ chartU q}
    have hUq : IsOpen Uq := by
      have heq : Uq = (Subtype.val : Dynamics.relativeClosedUnstablePlaque F γ q → Λ) ⁻¹'
          Metric.ball q chartRadius := by
        ext u
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, u.property⟩⟩
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val
    let Q : Set P := r ⁻¹' Uq
    have hQ : IsOpen Q := hUq.preimage hr.continuous
    let rq : Q → Uq := fun t ↦ ⟨r t.val, t.property⟩
    have hrq : _root_.Topology.IsOpenEmbedding rq :=
      _root_.Topology.IsOpenEmbedding.of_comp rq hUq.isOpenEmbedding_subtypeVal
        (hr.comp hQ.isOpenEmbedding_subtypeVal)
    let ι : Q → Dynamics.relativeClosedUnstablePlaque F γ (F w) := fun t ↦ t.val.val.val
    have hι : _root_.Topology.IsOpenEmbedding ι :=
      hO.isOpenEmbedding_subtypeVal.comp
        (hP.isOpenEmbedding_subtypeVal.comp hQ.isOpenEmbedding_subtypeVal)
    let a : Q ≃ₜ Set.range ι := hι.isEmbedding.toHomeomorph
    let f : Set.range ι → Uq := rq ∘ a.symm
    have hf : _root_.Topology.IsOpenEmbedding f := hrq.comp a.symm.isOpenEmbedding
    let wO : O := ⟨⟨F w, fun _ ↦ by simpa using G.gamma_pos.le⟩, hwO⟩
    have hwP : wO ∈ P := by
      change (g wO : Λ) ∈ chartU w
      rw [hgf]
      simp only [wO, Homeomorph.symm_apply_apply]
      exact ⟨by simpa using (hαpos 3).trans hchartRadiusLow,
        fun _ ↦ by simpa using G.gamma_pos.le⟩
    let wP : P := ⟨wO, hwP⟩
    have hwQ : wP ∈ Q := by
      change (r wP : Λ) ∈ chartU q
      rw [hrf]
      simpa only [wP, wO, Homeomorph.symm_apply_apply] using hbq
    refine ⟨Set.range ι, hι.isOpen_range, ⟨⟨wP, hwQ⟩, rfl⟩, f, hf, ?_⟩
    intro t
    have ha : ι (a.symm t) = t.val := congrArg Subtype.val (a.apply_symm_apply t)
    change (r (a.symm t).val : Λ) = _
    rw [hrf]
    exact congrArg (fun z : Dynamics.relativeClosedUnstablePlaque F γ (F w) ↦
      G.bracket (F.symm (z : Λ)) q) ha
  have hcommonReceivingCore (q w : Λ) (j : Fin N) (hfw : F w ∈ R j)
      (hwq : dist w q ≤ α 3) (hbq : G.bracket w q ∈ chartU q) :
      ∃ T : Set (Dynamics.relativeClosedUnstablePlaque F γ (F w)),
        IsOpen T ∧
        ∃ g : T → {u : Dynamics.relativeClosedUnstablePlaque F γ q // (u : Λ) ∈ chartU q},
          _root_.Topology.IsOpenEmbedding g ∧
          {t : T | (t : Λ) ∈ R j} = closure (interior {t : T | (t : Λ) ∈ R j}) ∧
          {t : T | (t : Λ) ∈ R j}.Nonempty ∧
          ∀ i : Fin N, q ∈ R i → w ∈ R i → transition F R i j →
            g '' {t : T | (t : Λ) ∈ R j} ⊆ {u | (u : Λ) ∈ R i} := by
    obtain ⟨T, hT, hwT, g, hg, hgf⟩ := hcommonInverseTargetChart q w hwq hbq
    refine ⟨T, hT, g, hg, ?_, ?_, ?_⟩
    · let S := Dynamics.relativeClosedUnstablePlaque F γ (F w)
      let D : Set S := {t | (t : Λ) ∈ R j}
      have hD : D = closure (interior D) := by
        obtain ⟨_, _, _, _, _, hd, _, _, _⟩ := hrectSlices j (F w) hfw
        have hs : Bowen.RectangleSlicesPreparation.unstablePlaque F γ (F w) = S := by
          ext z
          simp only [S, Bowen.RectangleSlicesPreparation.unstablePlaque,
            Dynamics.relativeClosedUnstablePlaque, Set.mem_ofPred_eq,
            Bowen.RectangleSlicesPreparation.homeomorph_pow_apply]
        rw [hs] at hd
        simp only [Bowen.RectangleSlicesPreparation.plaqueSlice,
          Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ] at hd
        exact hd
      change (Subtype.val : T → S) ⁻¹' D = closure (interior ((Subtype.val : T → S) ⁻¹' D))
      calc
        (Subtype.val : T → S) ⁻¹' D = Subtype.val ⁻¹' closure (interior D) :=
          congrArg (fun A : Set S ↦ (Subtype.val : T → S) ⁻¹' A) hD
        _ = closure (interior ((Subtype.val : T → S) ⁻¹' D)) := by
          rw [hT.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val,
            hT.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage continuous_subtype_val]
    · exact ⟨⟨⟨F w, fun _ ↦ by simpa using G.gamma_pos.le⟩, hwT⟩, hfw⟩
    · intro i hqi hwi hij u hu
      obtain ⟨t, ht, rfl⟩ := hu
      change (g t : Λ) ∈ R i
      rw [hgf]
      exact hinverseTargetImage q w i j hqi hwi hfw hij t ⟨ht, t.val.property⟩
  have hcommonPredecessorCore (q w : Λ) (i j : Fin N)
      (hqi : q ∈ R i) (hwi : w ∈ R i) (hfw : F w ∈ R j) :
      ∃ T : Set (Dynamics.relativeClosedUnstablePlaque F γ (F w)),
        IsOpen T ∧
        ∃ g : T → {u : Dynamics.relativeClosedUnstablePlaque F γ q // (u : Λ) ∈ chartU q},
          _root_.Topology.IsOpenEmbedding g ∧
          {t : T | (t : Λ) ∈ R j} = closure (interior {t : T | (t : Λ) ∈ R j}) ∧
          {t : T | (t : Λ) ∈ R j}.Nonempty ∧
          ∀ k : Fin N, q ∈ R k → w ∈ R k → transition F R k j →
            g '' {t : T | (t : Λ) ∈ R j} ⊆ {u | (u : Λ) ∈ R k} := by
    have hwq : dist w q ≤ Metric.diam (R i) :=
      Metric.dist_le_diam_of_mem (hrect i).2.1.isBounded hwi hqi
    have hbq : G.bracket w q ∈ chartU q :=
      (hcommonFactorGuards q i hqi).1
        ⟨hrectBracket i w hwi q hqi, (G.bracket_mem w q (hwq.trans (hrectClose i))).2⟩
    exact hcommonReceivingCore q w j hfw (hwq.trans (hrectSmall i).le) hbq
  have hcommonCollision (q w : Λ) (i k j : Fin N) (hik : i ≠ k)
      (hqi : q ∈ R i) (hqk : q ∈ R k) (hwi : w ∈ R i) (hwk : w ∈ R k)
      (hfw : F w ∈ R j) (hij : transition F R i j) (hkj : transition F R k j) :
      {v : {v : Dynamics.relativeClosedStablePlaque F γ q // (v : Λ) ∈ chartV q} |
        (v : Λ) ∈ R i} ∩ {v | (v : Λ) ∈ R k} ⊆
        frontier {v : {v : Dynamics.relativeClosedStablePlaque F γ q // (v : Λ) ∈ chartV q} |
          (v : Λ) ∈ R i} := by
    obtain ⟨T, hT, g, hg, hC, hCne, hcover⟩ := hcommonPredecessorCore q w i j hqi hwi hfw
    let C : Set T := {t | (t : Λ) ∈ R j}
    let : Nonempty T := ⟨hCne.choose⟩
    let h := hg.toOpenPartialHomeomorph g
    obtain ⟨e, hesource, hetarget, heforward, herect⟩ := hcommonPartialChart q
    exact Dynamics.Bowen.localPredecessorCollisionFrontier e h C hC hCne
      (by simp only [h, _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
        Set.subset_univ])
      {u | (u : Λ) ∈ R i} {u | (u : Λ) ∈ R k}
      {v | (v : Λ) ∈ R i} {v | (v : Λ) ∈ R k} (R i) (R k)
      (hcover i hqi hwi hij) (hcover k hqk hwk hkj)
      (hcommonStableRegular q k hqk)
      (by rw [hetarget]; exact Set.subset_univ _)
      (by rw [hetarget]; exact Set.subset_univ _)
      (herect i hqi) (herect k hqk) (hdisj i k hik)
  have hselfCollisionBoundary (q : Λ) (i k j : Fin N) (hik : i ≠ k)
      (hqi : q ∈ R i) (hqk : q ∈ R k) (hFq : F q ∈ R j)
      (hij : transition F R i j) (hkj : transition F R k j) :
      q ∈ Bowen.RectangleSlicesPreparation.plaqueBoundary
        (Dynamics.relativeClosedStablePlaque F γ q) (R i) := by
    let S := Dynamics.relativeClosedStablePlaque F γ q
    let V : Set S := {v | (v : Λ) ∈ chartV q}
    let D : Set S := {v | (v : Λ) ∈ R i}
    have hV : IsOpen V := by
      have heq : V = (Subtype.val : S → Λ) ⁻¹' Metric.ball q chartRadius := by
        ext v
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, v.property⟩⟩
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val
    let qS : S := ⟨q, fun _ ↦ by simpa using G.gamma_pos.le⟩
    have hqV : qS ∈ V :=
      ⟨by simpa [qS] using (hαpos 3).trans hchartRadiusLow, qS.property⟩
    let qV : V := ⟨qS, hqV⟩
    have hfront := hcommonCollision q q i k j hik hqi hqk hqi hqk hFq hij hkj
      (show qV ∈ {v : V | (v : Λ) ∈ R i} ∩ {v | (v : Λ) ∈ R k} from ⟨hqi, hqk⟩)
    change qV ∈ frontier ((Subtype.val : V → S) ⁻¹' D) at hfront
    rw [← hV.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val D] at hfront
    exact ⟨qS, hfront, rfl⟩
  have hcollisionBoundaryCover (x : Λ) :
      ∃ C : Set (Dynamics.relativeClosedStablePlaque F γ x),
        IsClosed C ∧ IsNowhereDense C ∧
        ∀ z : Dynamics.relativeClosedStablePlaque F γ x, dist (z : Λ) x < γ →
          (∃ i k j : Fin N, i ≠ k ∧ transition F R i j ∧ transition F R k j ∧
            (z : Λ) ∈ R i ∧ (z : Λ) ∈ R k ∧ F z ∈ R j) → z ∈ frontier C := by
    let C : Set (Dynamics.relativeClosedStablePlaque F γ x) :=
      ⋃ i : Fin N, frontier {z : Dynamics.relativeClosedStablePlaque F γ x | (z : Λ) ∈ R i}
    have hC : IsClosed C := isClosed_iUnion_of_finite fun _ ↦ isClosed_frontier
    have hND : IsNowhereDense C := IsNowhereDense.iUnion fun i ↦ by
      apply isClosed_frontier.isNowhereDense_iff.mpr
      exact interior_frontier ((hrect i).2.1.isClosed.preimage continuous_subtype_val)
    refine ⟨C, hC, hND, ?_⟩
    intro z hz hbad
    obtain ⟨i, k, j, hik, hij, hkj, hzi, hzk, hFz⟩ := hbad
    have hb := hselfCollisionBoundary z i k j hik hzi hzk hFz hij hkj
    have heq := (Dynamics.Bowen.stableDirectionalBoundaryTrace F γ κ G.gamma_pos
      ⟨G.lambda_pos.le, G.lambda_lt_one.le⟩
      (by
        intro a y z hy hz n
        simpa only [F, restrictedDynamics] using G.stable_contraction a y z hy hz n)
      (R i) (hrect i).2.1.isClosed x).1
    have hzfront : z ∈ frontier {z : Dynamics.relativeClosedStablePlaque F γ x | (z : Λ) ∈ R i} := by
      have hh : z ∈ {z : Dynamics.relativeClosedStablePlaque F γ x |
          dist (z : Λ) x < γ ∧ (z : Λ) ∈ Bowen.RectangleSlicesPreparation.plaqueBoundary
            (Dynamics.relativeClosedStablePlaque F γ z.val) (R i)} := ⟨hz, hb⟩
      rw [heq] at hh
      exact hh.2
    rw [frontier, hC.closure_eq, hC.isNowhereDense_iff.mp hND, Set.sdiff_empty]
    exact Set.mem_iUnion.mpr ⟨i, hzfront⟩
  have hstableDensity (x : Λ) (i : Fin N) (hx : x ∈ R i) :
      x ∈ closure {z : Λ | z ∈ R i ∧ z ∈ Dynamics.relativeClosedStablePlaque F γ x ∧
        ∀ n : ℤ, ∀ j : Fin N, F ((F ^ n) z) ∈ R j →
          {k : Fin N | (F ^ n) z ∈ R k ∧ transition F R k j}.Subsingleton} := by
    let S := Dynamics.relativeClosedStablePlaque F γ x
    let P : Set S := {z | dist (z : Λ) x < γ / 2}
    have hP : IsOpen P := Metric.isOpen_ball.preimage continuous_subtype_val
    let : CompactSpace S := isCompact_iff_compactSpace.mp
      (isClosed_relativeClosedStablePlaque F γ x).isCompact
    let : BaireSpace P := hP.isOpenEmbedding_subtypeVal.baireSpace
    let a : P → Λ := fun z ↦ z.val.val
    have ha : Continuous a := continuous_subtype_val.comp continuous_subtype_val
    let K : Set P := {z | (z : Λ) ∈ R i}
    have hK : K = closure (interior K) := by
      let D : Set S := {z | (z : Λ) ∈ R i}
      have hD : D = closure (interior D) := by
        obtain ⟨_, _, _, _, _, _, hd, _, _⟩ := hrectSlices i x hx
        have hs : Bowen.RectangleSlicesPreparation.stablePlaque F γ x = S := by
          ext z
          simp only [S, Bowen.RectangleSlicesPreparation.stablePlaque,
            Dynamics.relativeClosedStablePlaque, Set.mem_ofPred_eq,
            Bowen.RectangleSlicesPreparation.homeomorph_pow_apply]
        rw [hs] at hd
        simp only [Bowen.RectangleSlicesPreparation.plaqueSlice,
          Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ] at hd
        exact hd
      change (Subtype.val : P → S) ⁻¹' D = closure (interior ((Subtype.val : P → S) ⁻¹' D))
      calc
        (Subtype.val : P → S) ⁻¹' D = Subtype.val ⁻¹' closure (interior D) :=
          congrArg (fun A : Set S ↦ (Subtype.val : P → S) ⁻¹' A) hD
        _ = closure (interior ((Subtype.val : P → S) ⁻¹' D)) := by
          rw [hP.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val,
            hP.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage continuous_subtype_val]
    have hdense := Dynamics.Bowen.predecessorTraceDensity F a ha R
      (fun k ↦ (hrect k).2.1.isClosed) (transition F R) K hK (by
        intro n z hbad
        obtain ⟨O, hO, hzO, g, hg, hgf⟩ := Dynamics.Bowen.stablePlaqueInteriorIntegerChart
          F γ κ G.gamma_pos ⟨G.lambda_pos.le, G.lambda_lt_one.le⟩
          (by
            intro c y z hy hz n
            simpa only [F, restrictedDynamics] using G.stable_contraction c y z hy hz n)
          x z.val (z.property.trans (by linarith [G.gamma_pos])) n
        let q : Λ := (F ^ n) (a z)
        let V : Set P := (Subtype.val : P → S) ⁻¹' O ∩
          (fun w : P ↦ (F ^ n) (a w)) ⁻¹' Metric.ball q γ
        have hV : IsOpen V :=
          (hO.preimage continuous_subtype_val).inter
            (Metric.isOpen_ball.preimage ((F ^ n).continuous.comp ha))
        have hzV : z ∈ V := ⟨hzO, by simpa [q] using G.gamma_pos⟩
        let j : V → O := fun w ↦ ⟨w.val.val, w.property.1⟩
        have hj : _root_.Topology.IsOpenEmbedding j :=
          _root_.Topology.IsOpenEmbedding.of_comp j hO.isOpenEmbedding_subtypeVal
            (hP.isOpenEmbedding_subtypeVal.comp hV.isOpenEmbedding_subtypeVal)
        let f : V → Dynamics.relativeClosedStablePlaque F γ q := g ∘ j
        have hf : _root_.Topology.IsOpenEmbedding f := hg.comp hj
        obtain ⟨C, hC, hND, hcover⟩ := hcollisionBoundaryCover q
        refine ⟨V, hV, hzV, Dynamics.relativeClosedStablePlaque F γ q,
          inferInstance, f, hf.continuous, hf.isOpenMap, C, hC, ?_⟩
        intro w hw
        have hfw : (f w : Λ) = (F ^ n) (a w.val) := hgf (j w)
        apply hcover (f w)
        · rw [hfw]
          exact Metric.mem_ball.mp w.property.2
        · simpa only [hfw] using hw)
    let xP : P := ⟨⟨x, fun _ ↦ by simpa using G.gamma_pos.le⟩,
      by simpa [P] using (half_pos G.gamma_pos)⟩
    have hxcl : xP ∈ closure {z : P | z ∈ interior K ∧ ∀ n : ℤ, ∀ j : Fin N,
        F ((F ^ n) (a z)) ∈ R j →
          {k : Fin N | (F ^ n) (a z) ∈ R k ∧ transition F R k j}.Subsingleton} :=
      hdense.symm ▸ hx
    have himage := mem_closure_image ha.continuousAt hxcl
    apply closure_mono ?_ himage
    rintro z ⟨w, hw, rfl⟩
    exact ⟨(show w ∈ K from interior_subset hw.1), w.val.property, hw.2⟩
  let revBracket : Λ → Λ → Λ := fun x y ↦ G.bracket y x
  let revTransition : Fin N → Fin N → Prop := fun i j ↦ transition F R j i
  have hrectBracketRev (i : Fin N) (p : Λ) (hp : p ∈ R i) (q : Λ) (hq : q ∈ R i) :
      revBracket p q ∈ R i := hrectBracket i q hq p hp
  have hcommonFactorGuardsRev (q : Λ) (i : Fin N) (hq : q ∈ R i) :=
    (hcommonFactorGuards q i hq).symm
  have hcommonStableRegularRev (q : Λ) (i : Fin N) (hqi : q ∈ R i) :
      {v : {v : Dynamics.relativeClosedStablePlaque F.symm γ q // (v : Λ) ∈ chartU q} |
        (v : Λ) ∈ R i} = closure (interior
          {v : {v : Dynamics.relativeClosedStablePlaque F.symm γ q // (v : Λ) ∈ chartU q} |
            (v : Λ) ∈ R i}) := by
    let S := Dynamics.relativeClosedStablePlaque F.symm γ q
    let V : Set S := {v | (v : Λ) ∈ chartU q}
    let D : Set S := {v | (v : Λ) ∈ R i}
    have hVopen : IsOpen V := by
      have heq : V = (Subtype.val : S → Λ) ⁻¹' Metric.ball q chartRadius := by
        ext v
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, v.property⟩⟩
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val
    have hD : D = closure (interior D) := by
      obtain ⟨_, _, _, _, _, hd, _, _, _⟩ := hrectSlices i q hqi
      have hs : Bowen.RectangleSlicesPreparation.unstablePlaque F γ q = S := by
        ext z
        simp only [S, Bowen.RectangleSlicesPreparation.unstablePlaque,
          Dynamics.relativeClosedStablePlaque, Set.mem_ofPred_eq,
          Bowen.RectangleSlicesPreparation.homeomorph_pow_apply]
      rw [hs] at hd
      simp only [Bowen.RectangleSlicesPreparation.plaqueSlice,
        Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ] at hd
      exact hd
    change (Subtype.val : V → S) ⁻¹' D = closure (interior ((Subtype.val : V → S) ⁻¹' D))
    calc
      (Subtype.val : V → S) ⁻¹' D = Subtype.val ⁻¹' closure (interior D) :=
        congrArg (fun T : Set S ↦ (Subtype.val : V → S) ⁻¹' T) hD
      _ = closure (interior ((Subtype.val : V → S) ⁻¹' D)) := by
        rw [hVopen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val,
          hVopen.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage continuous_subtype_val]
  have hcommonPartialChartRev (q : Λ) :
      ∃ e : OpenPartialHomeomorph Λ
          ({v : Dynamics.relativeClosedStablePlaque F γ q // (v : Λ) ∈ chartV q} ×
           {u : Dynamics.relativeClosedUnstablePlaque F γ q // (u : Λ) ∈ chartU q}),
        e.target = Set.univ ∧
        ∀ i : Fin N, q ∈ R i →
          e.symm ''
            ({v : {v : Dynamics.relativeClosedStablePlaque F γ q // (v : Λ) ∈ chartV q} | (v : Λ) ∈ R i} ×ˢ
             {u : {u : Dynamics.relativeClosedUnstablePlaque F γ q // (u : Λ) ∈ chartU q} | (u : Λ) ∈ R i}) ⊆ R i := by
    obtain ⟨hWopen, h, hforward, hinverse⟩ := hcommonChart q
    let P := {v : Dynamics.relativeClosedStablePlaque F γ q // (v : Λ) ∈ chartV q} ×
      {u : Dynamics.relativeClosedUnstablePlaque F γ q // (u : Λ) ∈ chartU q}
    have hqU : q ∈ chartU q := ⟨by simpa using (hαpos 3).trans hchartRadiusLow,
      fun _ ↦ by simpa using G.gamma_pos.le⟩
    have hqV : q ∈ chartV q := ⟨by simpa using (hαpos 3).trans hchartRadiusLow,
      fun _ ↦ by simpa using G.gamma_pos.le⟩
    let : Nonempty P := ⟨⟨⟨⟨q, hqV.2⟩, hqV⟩, ⟨⟨q, hqU.2⟩, hqU⟩⟩⟩
    let g : P → Λ := fun p ↦ (h (p.2, p.1) : Λ)
    have hg : _root_.Topology.IsOpenEmbedding g :=
      hWopen.isOpenEmbedding_subtypeVal.comp
        (h.isOpenEmbedding.comp (Homeomorph.prodComm _ _).isOpenEmbedding)
    let e := (hg.toOpenPartialHomeomorph g).symm
    refine ⟨e, rfl, ?_⟩
    intro i hqi z hz
    obtain ⟨⟨v, u⟩, hvu, rfl⟩ := hz
    change (h (u, v) : Λ) ∈ R i
    rw [hforward]
    exact hrectBracket i _ hvu.2 _ hvu.1
  have hinverseTargetChartRev (w : Λ) :
      ∃ O : Set (Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w)),
        IsOpen O ∧ (⟨F.symm w, fun _ ↦ by simpa using G.gamma_pos.le⟩ :
          Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w)) ∈ O ∧
        ∃ g : O → Dynamics.relativeClosedUnstablePlaque F.symm γ w,
          _root_.Topology.IsOpenEmbedding g ∧ ∀ t, (g t : Λ) = F.symm.symm (t : Λ) := by
    obtain ⟨O, V, hO, hV, hwO, hwV, hOopen, hVopen, e, he⟩ :=
      Dynamics.Bowen.stablePlaqueIntegerChart F.symm.symm γ G.gamma_pos (F.symm w) (1 : ℤ)
    simp only [zpow_one, Homeomorph.symm_apply_apply] at hV hwV he
    rw [zpow_one, Homeomorph.symm_apply_apply] at hVopen
    change O ⊆ Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w) at hO
    change V ⊆ Dynamics.relativeClosedUnstablePlaque F.symm γ w at hV
    let Os : Set (Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w)) := Subtype.val ⁻¹' O
    let Vs : Set (Dynamics.relativeClosedUnstablePlaque F.symm γ w) := Subtype.val ⁻¹' V
    let a : Os ≃ₜ O := _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hO)
    let b : Vs ≃ₜ V := _root_.Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hV)
    let c : Os ≃ₜ Vs := (a.trans e).trans b.symm
    let g : Os → Dynamics.relativeClosedUnstablePlaque F.symm γ w := fun t ↦ (c t).val
    have hVs : IsOpen Vs := hVopen
    have hg : _root_.Topology.IsOpenEmbedding g :=
      hVs.isOpenEmbedding_subtypeVal.comp c.isOpenEmbedding
    refine ⟨Os, hOopen, hwO, g, hg, ?_⟩
    intro t
    have hb : (b (c t) : Λ) = (e (a t) : Λ) := by
      exact congrArg Subtype.val (b.apply_symm_apply (e (a t)))
    calc
      (g t : Λ) = (b (c t) : Λ) := rfl
      _ = (e (a t) : Λ) := hb
      _ = F.symm.symm (a t : Λ) := he (a t)
      _ = F.symm.symm (t : Λ) := rfl
  have hinverseTargetImageRev (q w : Λ) (i j : Fin N)
      (hq : q ∈ R i) (hw : w ∈ R i) (hfw : F.symm w ∈ R j)
      (hij : revTransition i j)
      (t : Λ) (ht : t ∈ R j ∩ Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w)) :
      revBracket (F.symm.symm t) q ∈ R i := by
    have hFt : F t ∈ R i :=
      (hclosed j i hij (F.symm w) hfw (by simpa using hw)).1 ⟨t, ht, rfl⟩
    exact hrectBracket i q hq (F t) hFt
  have hcommonInverseTargetChartRev (q w : Λ) (hwq : dist w q ≤ α 3)
      (hbq : revBracket w q ∈ chartV q) :
      ∃ T : Set (Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w)),
        IsOpen T ∧ (⟨F.symm w, fun _ ↦ by simpa using G.gamma_pos.le⟩ :
          Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w)) ∈ T ∧
        ∃ g : T → {u : Dynamics.relativeClosedUnstablePlaque F.symm γ q // (u : Λ) ∈ chartV q},
          _root_.Topology.IsOpenEmbedding g ∧
          ∀ t, (g t : Λ) = revBracket (F.symm.symm (t : Λ)) q := by
    obtain ⟨O, hO, hwO, g, hg, hgf⟩ := hinverseTargetChartRev w
    let U : Set (Dynamics.relativeClosedUnstablePlaque F.symm γ w) :=
      {u | (u : Λ) ∈ chartV w}
    have hU : IsOpen U := by
      have heq : U = (Subtype.val : Dynamics.relativeClosedUnstablePlaque F.symm γ w → Λ) ⁻¹'
          Metric.ball w chartRadius := by
        ext u
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, u.property⟩⟩
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val
    have hUbound : chartV w ⊆ Dynamics.relativeClosedUnstablePlaque F.symm (α 2) w := by
      intro z hz n
      have hh := G.stable_contraction w z w hz.2
        (fun _ ↦ by simp [G.gamma_pos.le]) n
      exact hh.trans ((mul_le_mul_of_nonneg_right
        (pow_le_one₀ G.lambda_pos.le G.lambda_lt_one.le) dist_nonneg).trans
        (by simpa only [one_mul] using (Metric.mem_ball.mp hz.1).le.trans hchartRadiusHigh.le))
    obtain ⟨hB, hBopen, e, he, hei⟩ := (hnativeRebase w q hwq).2 (chartV w) hUbound hU
    let B : Set (Dynamics.relativeClosedUnstablePlaque F.symm γ q) :=
      {u | (u : Λ) ∈ (fun z : Λ ↦ revBracket z q) '' chartV w}
    have hB' : IsOpen B := hBopen
    let P : Set O := g ⁻¹' U
    have hP : IsOpen P := hU.preimage hg.continuous
    let gp : P → U := fun t ↦ ⟨g t.val, t.property⟩
    have hgp : _root_.Topology.IsOpenEmbedding gp :=
      _root_.Topology.IsOpenEmbedding.of_comp gp hU.isOpenEmbedding_subtypeVal
        (hg.comp hP.isOpenEmbedding_subtypeVal)
    let r : P → Dynamics.relativeClosedUnstablePlaque F.symm γ q := fun t ↦ (e (gp t)).val
    have hr : _root_.Topology.IsOpenEmbedding r :=
      hB'.isOpenEmbedding_subtypeVal.comp (e.isOpenEmbedding.comp hgp)
    have hrf (t : P) : (r t : Λ) = revBracket (F.symm.symm (t : Λ)) q := by
      change (e (gp t) : Λ) = _
      exact (he (gp t)).trans (congrArg (fun z ↦ revBracket z q) (hgf t.val))
    let Uq : Set (Dynamics.relativeClosedUnstablePlaque F.symm γ q) :=
      {u | (u : Λ) ∈ chartV q}
    have hUq : IsOpen Uq := by
      have heq : Uq = (Subtype.val : Dynamics.relativeClosedUnstablePlaque F.symm γ q → Λ) ⁻¹'
          Metric.ball q chartRadius := by
        ext u
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, u.property⟩⟩
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val
    let Q : Set P := r ⁻¹' Uq
    have hQ : IsOpen Q := hUq.preimage hr.continuous
    let rq : Q → Uq := fun t ↦ ⟨r t.val, t.property⟩
    have hrq : _root_.Topology.IsOpenEmbedding rq :=
      _root_.Topology.IsOpenEmbedding.of_comp rq hUq.isOpenEmbedding_subtypeVal
        (hr.comp hQ.isOpenEmbedding_subtypeVal)
    let ι : Q → Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w) := fun t ↦ t.val.val.val
    have hι : _root_.Topology.IsOpenEmbedding ι :=
      hO.isOpenEmbedding_subtypeVal.comp
        (hP.isOpenEmbedding_subtypeVal.comp hQ.isOpenEmbedding_subtypeVal)
    let a : Q ≃ₜ Set.range ι := hι.isEmbedding.toHomeomorph
    let f : Set.range ι → Uq := rq ∘ a.symm
    have hf : _root_.Topology.IsOpenEmbedding f := hrq.comp a.symm.isOpenEmbedding
    let wO : O := ⟨⟨F.symm w, fun _ ↦ by simpa using G.gamma_pos.le⟩, hwO⟩
    have hwP : wO ∈ P := by
      change (g wO : Λ) ∈ chartV w
      rw [hgf]
      simp only [wO, Homeomorph.symm_apply_apply]
      exact ⟨by simpa using (hαpos 3).trans hchartRadiusLow,
        fun _ ↦ by simpa using G.gamma_pos.le⟩
    let wP : P := ⟨wO, hwP⟩
    have hwQ : wP ∈ Q := by
      change (r wP : Λ) ∈ chartV q
      rw [hrf]
      simpa only [wP, wO, Homeomorph.symm_apply_apply] using hbq
    refine ⟨Set.range ι, hι.isOpen_range, ⟨⟨wP, hwQ⟩, rfl⟩, f, hf, ?_⟩
    intro t
    have ha : ι (a.symm t) = t.val := congrArg Subtype.val (a.apply_symm_apply t)
    change (r (a.symm t).val : Λ) = _
    rw [hrf]
    exact congrArg (fun z : Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w) ↦
      revBracket (F.symm.symm (z : Λ)) q) ha
  have hcommonReceivingCoreRev (q w : Λ) (j : Fin N) (hfw : F.symm w ∈ R j)
      (hwq : dist w q ≤ α 3) (hbq : revBracket w q ∈ chartV q) :
      ∃ T : Set (Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w)),
        IsOpen T ∧
        ∃ g : T → {u : Dynamics.relativeClosedUnstablePlaque F.symm γ q // (u : Λ) ∈ chartV q},
          _root_.Topology.IsOpenEmbedding g ∧
          {t : T | (t : Λ) ∈ R j} = closure (interior {t : T | (t : Λ) ∈ R j}) ∧
          {t : T | (t : Λ) ∈ R j}.Nonempty ∧
          ∀ i : Fin N, q ∈ R i → w ∈ R i → revTransition i j →
            g '' {t : T | (t : Λ) ∈ R j} ⊆ {u | (u : Λ) ∈ R i} := by
    obtain ⟨T, hT, hwT, g, hg, hgf⟩ := hcommonInverseTargetChartRev q w hwq hbq
    refine ⟨T, hT, g, hg, ?_, ?_, ?_⟩
    · let S := Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w)
      let D : Set S := {t | (t : Λ) ∈ R j}
      have hD : D = closure (interior D) := by
        obtain ⟨_, _, _, _, _, _, hd, _, _⟩ := hrectSlices j (F.symm w) hfw
        have hs : Bowen.RectangleSlicesPreparation.stablePlaque F γ (F.symm w) = S := by
          ext z
          simp only [S, Bowen.RectangleSlicesPreparation.stablePlaque,
            Dynamics.relativeClosedUnstablePlaque, Set.mem_ofPred_eq,
            Bowen.RectangleSlicesPreparation.homeomorph_pow_apply, Homeomorph.symm_symm]
        rw [hs] at hd
        simp only [Bowen.RectangleSlicesPreparation.plaqueSlice,
          Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ] at hd
        exact hd
      change (Subtype.val : T → S) ⁻¹' D = closure (interior ((Subtype.val : T → S) ⁻¹' D))
      calc
        (Subtype.val : T → S) ⁻¹' D = Subtype.val ⁻¹' closure (interior D) :=
          congrArg (fun A : Set S ↦ (Subtype.val : T → S) ⁻¹' A) hD
        _ = closure (interior ((Subtype.val : T → S) ⁻¹' D)) := by
          rw [hT.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val,
            hT.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage continuous_subtype_val]
    · exact ⟨⟨⟨F.symm w, fun _ ↦ by simpa using G.gamma_pos.le⟩, hwT⟩, hfw⟩
    · intro i hqi hwi hij u hu
      obtain ⟨t, ht, rfl⟩ := hu
      change (g t : Λ) ∈ R i
      rw [hgf]
      exact hinverseTargetImageRev q w i j hqi hwi hfw hij t ⟨ht, t.val.property⟩
  have hcommonPredecessorCoreRev (q w : Λ) (i j : Fin N)
      (hqi : q ∈ R i) (hwi : w ∈ R i) (hfw : F.symm w ∈ R j) :
      ∃ T : Set (Dynamics.relativeClosedUnstablePlaque F.symm γ (F.symm w)),
        IsOpen T ∧
        ∃ g : T → {u : Dynamics.relativeClosedUnstablePlaque F.symm γ q // (u : Λ) ∈ chartV q},
          _root_.Topology.IsOpenEmbedding g ∧
          {t : T | (t : Λ) ∈ R j} = closure (interior {t : T | (t : Λ) ∈ R j}) ∧
          {t : T | (t : Λ) ∈ R j}.Nonempty ∧
          ∀ k : Fin N, q ∈ R k → w ∈ R k → revTransition k j →
            g '' {t : T | (t : Λ) ∈ R j} ⊆ {u | (u : Λ) ∈ R k} := by
    have hwq : dist w q ≤ Metric.diam (R i) :=
      Metric.dist_le_diam_of_mem (hrect i).2.1.isBounded hwi hqi
    have hbq : revBracket w q ∈ chartV q :=
      (hcommonFactorGuardsRev q i hqi).1
        ⟨hrectBracketRev i w hwi q hqi, (G.bracket_mem q w (by simpa only [dist_comm] using hwq.trans (hrectClose i))).1⟩
    exact hcommonReceivingCoreRev q w j hfw (hwq.trans (hrectSmall i).le) hbq
  have hcommonCollisionRev (q w : Λ) (i k j : Fin N) (hik : i ≠ k)
      (hqi : q ∈ R i) (hqk : q ∈ R k) (hwi : w ∈ R i) (hwk : w ∈ R k)
      (hfw : F.symm w ∈ R j) (hij : revTransition i j) (hkj : revTransition k j) :
      {v : {v : Dynamics.relativeClosedStablePlaque F.symm γ q // (v : Λ) ∈ chartU q} |
        (v : Λ) ∈ R i} ∩ {v | (v : Λ) ∈ R k} ⊆
        frontier {v : {v : Dynamics.relativeClosedStablePlaque F.symm γ q // (v : Λ) ∈ chartU q} |
          (v : Λ) ∈ R i} := by
    obtain ⟨T, hT, g, hg, hC, hCne, hcover⟩ := hcommonPredecessorCoreRev q w i j hqi hwi hfw
    let C : Set T := {t | (t : Λ) ∈ R j}
    let : Nonempty T := ⟨hCne.choose⟩
    let h := hg.toOpenPartialHomeomorph g
    obtain ⟨e, hetarget, herect⟩ := hcommonPartialChartRev q
    exact Dynamics.Bowen.localPredecessorCollisionFrontier e h C hC hCne
      (by simp only [h, _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source,
        Set.subset_univ])
      {u | (u : Λ) ∈ R i} {u | (u : Λ) ∈ R k}
      {v | (v : Λ) ∈ R i} {v | (v : Λ) ∈ R k} (R i) (R k)
      (hcover i hqi hwi hij) (hcover k hqk hwk hkj)
      (hcommonStableRegularRev q k hqk)
      (by rw [hetarget]; exact Set.subset_univ _)
      (by rw [hetarget]; exact Set.subset_univ _)
      (herect i hqi) (herect k hqk) (hdisj i k hik)
  have hselfCollisionBoundaryRev (q : Λ) (i k j : Fin N) (hik : i ≠ k)
      (hqi : q ∈ R i) (hqk : q ∈ R k) (hFq : F.symm q ∈ R j)
      (hij : revTransition i j) (hkj : revTransition k j) :
      q ∈ Bowen.RectangleSlicesPreparation.plaqueBoundary
        (Dynamics.relativeClosedStablePlaque F.symm γ q) (R i) := by
    let S := Dynamics.relativeClosedStablePlaque F.symm γ q
    let V : Set S := {v | (v : Λ) ∈ chartU q}
    let D : Set S := {v | (v : Λ) ∈ R i}
    have hV : IsOpen V := by
      have heq : V = (Subtype.val : S → Λ) ⁻¹' Metric.ball q chartRadius := by
        ext v
        exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, v.property⟩⟩
      rw [heq]
      exact Metric.isOpen_ball.preimage continuous_subtype_val
    let qS : S := ⟨q, fun _ ↦ by simpa using G.gamma_pos.le⟩
    have hqV : qS ∈ V :=
      ⟨by simpa [qS] using (hαpos 3).trans hchartRadiusLow, qS.property⟩
    let qV : V := ⟨qS, hqV⟩
    have hfront := hcommonCollisionRev q q i k j hik hqi hqk hqi hqk hFq hij hkj
      (show qV ∈ {v : V | (v : Λ) ∈ R i} ∩ {v | (v : Λ) ∈ R k} from ⟨hqi, hqk⟩)
    change qV ∈ frontier ((Subtype.val : V → S) ⁻¹' D) at hfront
    rw [← hV.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      continuous_subtype_val D] at hfront
    exact ⟨qS, hfront, rfl⟩
  have hcollisionBoundaryCoverRev (x : Λ) :
      ∃ C : Set (Dynamics.relativeClosedStablePlaque F.symm γ x),
        IsClosed C ∧ IsNowhereDense C ∧
        ∀ z : Dynamics.relativeClosedStablePlaque F.symm γ x, dist (z : Λ) x < γ →
          (∃ i k j : Fin N, i ≠ k ∧ revTransition i j ∧ revTransition k j ∧
            (z : Λ) ∈ R i ∧ (z : Λ) ∈ R k ∧ F.symm z ∈ R j) → z ∈ frontier C := by
    let C : Set (Dynamics.relativeClosedStablePlaque F.symm γ x) :=
      ⋃ i : Fin N, frontier {z : Dynamics.relativeClosedStablePlaque F.symm γ x | (z : Λ) ∈ R i}
    have hC : IsClosed C := isClosed_iUnion_of_finite fun _ ↦ isClosed_frontier
    have hND : IsNowhereDense C := IsNowhereDense.iUnion fun i ↦ by
      apply isClosed_frontier.isNowhereDense_iff.mpr
      exact interior_frontier ((hrect i).2.1.isClosed.preimage continuous_subtype_val)
    refine ⟨C, hC, hND, ?_⟩
    intro z hz hbad
    obtain ⟨i, k, j, hik, hij, hkj, hzi, hzk, hFz⟩ := hbad
    have hb := hselfCollisionBoundaryRev z i k j hik hzi hzk hFz hij hkj
    have heq := (Dynamics.Bowen.stableDirectionalBoundaryTrace F.symm γ κ G.gamma_pos
      ⟨G.lambda_pos.le, G.lambda_lt_one.le⟩
      (by
        intro a y z hy hz n
        simpa only [F, restrictedDynamics] using G.unstable_contraction a y z hy hz n)
      (R i) (hrect i).2.1.isClosed x).1
    have hzfront : z ∈ frontier {z : Dynamics.relativeClosedStablePlaque F.symm γ x | (z : Λ) ∈ R i} := by
      have hh : z ∈ {z : Dynamics.relativeClosedStablePlaque F.symm γ x |
          dist (z : Λ) x < γ ∧ (z : Λ) ∈ Bowen.RectangleSlicesPreparation.plaqueBoundary
            (Dynamics.relativeClosedStablePlaque F.symm γ z.val) (R i)} := ⟨hz, hb⟩
      rw [heq] at hh
      exact hh.2
    rw [frontier, hC.closure_eq, hC.isNowhereDense_iff.mp hND, Set.sdiff_empty]
    exact Set.mem_iUnion.mpr ⟨i, hzfront⟩
  have hstableDensityRev (x : Λ) (i : Fin N) (hx : x ∈ R i) :
      x ∈ closure {z : Λ | z ∈ R i ∧ z ∈ Dynamics.relativeClosedStablePlaque F.symm γ x ∧
        ∀ n : ℤ, ∀ j : Fin N, F.symm ((F.symm ^ n) z) ∈ R j →
          {k : Fin N | (F.symm ^ n) z ∈ R k ∧ revTransition k j}.Subsingleton} := by
    let S := Dynamics.relativeClosedStablePlaque F.symm γ x
    let P : Set S := {z | dist (z : Λ) x < γ / 2}
    have hP : IsOpen P := Metric.isOpen_ball.preimage continuous_subtype_val
    let : CompactSpace S := isCompact_iff_compactSpace.mp
      (isClosed_relativeClosedStablePlaque F.symm γ x).isCompact
    let : BaireSpace P := hP.isOpenEmbedding_subtypeVal.baireSpace
    let a : P → Λ := fun z ↦ z.val.val
    have ha : Continuous a := continuous_subtype_val.comp continuous_subtype_val
    let K : Set P := {z | (z : Λ) ∈ R i}
    have hK : K = closure (interior K) := by
      let D : Set S := {z | (z : Λ) ∈ R i}
      have hD : D = closure (interior D) := by
        obtain ⟨_, _, _, _, _, hd, _, _, _⟩ := hrectSlices i x hx
        have hs : Bowen.RectangleSlicesPreparation.unstablePlaque F γ x = S := by
          ext z
          simp only [S, Bowen.RectangleSlicesPreparation.unstablePlaque,
            Dynamics.relativeClosedStablePlaque, Set.mem_ofPred_eq,
            Bowen.RectangleSlicesPreparation.homeomorph_pow_apply]
        rw [hs] at hd
        simp only [Bowen.RectangleSlicesPreparation.plaqueSlice,
          Set.preimage_inter, Subtype.coe_preimage_self, Set.inter_univ] at hd
        exact hd
      change (Subtype.val : P → S) ⁻¹' D = closure (interior ((Subtype.val : P → S) ⁻¹' D))
      calc
        (Subtype.val : P → S) ⁻¹' D = Subtype.val ⁻¹' closure (interior D) :=
          congrArg (fun A : Set S ↦ (Subtype.val : P → S) ⁻¹' A) hD
        _ = closure (interior ((Subtype.val : P → S) ⁻¹' D)) := by
          rw [hP.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage continuous_subtype_val,
            hP.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage continuous_subtype_val]
    have hdense := Dynamics.Bowen.predecessorTraceDensity F.symm a ha R
      (fun k ↦ (hrect k).2.1.isClosed) (revTransition) K hK (by
        intro n z hbad
        obtain ⟨O, hO, hzO, g, hg, hgf⟩ := Dynamics.Bowen.stablePlaqueInteriorIntegerChart
          F.symm γ κ G.gamma_pos ⟨G.lambda_pos.le, G.lambda_lt_one.le⟩
          (by
            intro c y z hy hz n
            simpa only [F, restrictedDynamics] using G.unstable_contraction c y z hy hz n)
          x z.val (z.property.trans (by linarith [G.gamma_pos])) n
        let q : Λ := (F.symm ^ n) (a z)
        let V : Set P := (Subtype.val : P → S) ⁻¹' O ∩
          (fun w : P ↦ (F.symm ^ n) (a w)) ⁻¹' Metric.ball q γ
        have hV : IsOpen V :=
          (hO.preimage continuous_subtype_val).inter
            (Metric.isOpen_ball.preimage ((F.symm ^ n).continuous.comp ha))
        have hzV : z ∈ V := ⟨hzO, by simpa [q] using G.gamma_pos⟩
        let j : V → O := fun w ↦ ⟨w.val.val, w.property.1⟩
        have hj : _root_.Topology.IsOpenEmbedding j :=
          _root_.Topology.IsOpenEmbedding.of_comp j hO.isOpenEmbedding_subtypeVal
            (hP.isOpenEmbedding_subtypeVal.comp hV.isOpenEmbedding_subtypeVal)
        let f : V → Dynamics.relativeClosedStablePlaque F.symm γ q := g ∘ j
        have hf : _root_.Topology.IsOpenEmbedding f := hg.comp hj
        obtain ⟨C, hC, hND, hcover⟩ := hcollisionBoundaryCoverRev q
        refine ⟨V, hV, hzV, Dynamics.relativeClosedStablePlaque F.symm γ q,
          inferInstance, f, hf.continuous, hf.isOpenMap, C, hC, ?_⟩
        intro w hw
        have hfw : (f w : Λ) = (F.symm ^ n) (a w.val) := hgf (j w)
        apply hcover (f w)
        · rw [hfw]
          exact Metric.mem_ball.mp w.property.2
        · simpa only [hfw] using hw)
    let xP : P := ⟨⟨x, fun _ ↦ by simpa using G.gamma_pos.le⟩,
      by simpa [P] using (half_pos G.gamma_pos)⟩
    have hxcl : xP ∈ closure {z : P | z ∈ interior K ∧ ∀ n : ℤ, ∀ j : Fin N,
        F.symm ((F.symm ^ n) (a z)) ∈ R j →
          {k : Fin N | (F.symm ^ n) (a z) ∈ R k ∧ revTransition k j}.Subsingleton} :=
      hdense.symm ▸ hx
    have himage := mem_closure_image ha.continuousAt hxcl
    apply closure_mono ?_ himage
    rintro z ⟨w, hw, rfl⟩
    exact ⟨(show w ∈ K from interior_subset hw.1), w.val.property, hw.2⟩
  have hdiam : ∀ i, @Metric.diam Λ originalMetric.toPseudoMetricSpace (R i) < ε := by
    intro i
    have hd : @Metric.diam Λ originalMetric.toPseudoMetricSpace (R i) ≤ ε / 2 :=
      @Metric.diam_le_of_forall_dist_le Λ (R i) originalMetric.toPseudoMetricSpace
        (ε / 2) (by linarith) (fun p hp q hq ↦ (hbound i p hp q hq).le)
    exact hd.trans_lt (by linarith)
  -- Only the finite-pattern branch argument remains: a uniform bound for this
  -- same coding, and coordinate rigidity over periodic physical points.
  suffices hfibre : ∃ D : ℕ, 1 ≤ D ∧
      (∀ x : Λ, {a : CodeSpace (transition F R) | coding a = x}.encard ≤ (D : ℕ∞)) ∧
      (∀ x : Λ, (∃ m : ℕ, 0 < m ∧ (F ^ m) x = x) →
        ∀ a b : CodeSpace (transition F R), coding a = x → coding b = x →
          (∃ j : ℤ, a.val j = b.val j) → a = b) by
    obtain ⟨D, hD, hfinite, hrigid⟩ := hfibre
    refine ⟨N, D, hN, hD, inferInstance, rfl, γ, G.gamma_pos, R,
      fun i ↦ ⟨hrect i, hdiam i⟩, hdisj, hcover, hmarkov,
      coding, hit, hcont, honto, hcov, hfinite, hlabels, ?_, hsplice⟩
    intro x hx
    exact ⟨periodic_code_of_bounded_fibre _ F coding hcov D hfinite x hx,
      hrigid x hx, coordinate_bijOn_of_code_rigidity F R coding hlabels x (hrigid x hx)⟩
  -- Bowen's native boundary-pattern construction is the remaining geometry.
  -- All counting and periodic deductions from its ranks are now proved above.
  suffices hranks : ∃ K : ℕ, ∃ rs ru : Λ → ℕ,
      (∀ x, rs x ≤ K) ∧ (∀ x, ru x ≤ K) ∧
      (∀ x, rs (F x) ≤ rs x) ∧ (∀ x, ru (F.symm x) ≤ ru x) ∧
      (∀ x a b, coding a = x → coding b = x → a.val 0 = b.val 0 →
        a.val 1 ≠ b.val 1 → rs (F x) < rs x) ∧
      (∀ x a b, coding a = x → coding b = x → a.val 0 = b.val 0 →
        a.val (-1) ≠ b.val (-1) → ru (F.symm x) < ru x) by
    obtain ⟨K, rs, ru, hKs, hKu, hms, hmu, hbs, hbu⟩ := hranks
    obtain ⟨hfinite, hrigid⟩ := coding_fibres_and_rigidity_of_physical_ranks
      F (transition F R) R coding hit rs ru hKs hKu hms hmu hbs hbu
    refine ⟨N * (N ^ (K + 1) * N ^ (K + 1)), ?_, hfinite, hrigid⟩
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  -- These sets use only actual rectangle membership and witnessed edges.
  -- Their invariance and zero-time uniqueness are immediate; the remaining
  -- geometry is density in every closed directional slice, including boundaries.
  let Ps : Λ → Prop := fun z ↦ ∀ j : Fin N, F z ∈ R j →
    {i : Fin N | z ∈ R i ∧ transition F R i j}.Subsingleton
  let Pu : Λ → Prop := fun z ↦ ∀ j : Fin N, F.symm z ∈ R j →
    {i : Fin N | z ∈ R i ∧ transition F R j i}.Subsingleton
  let Gs : Set Λ := allTimeGood F Ps
  let Gu : Set Λ := allTimeGood F.symm Pu
  suffices hdensity :
      (∀ x i, x ∈ R i → x ∈ closure {z : Λ |
        z ∈ R i ∧ z ∈ Dynamics.relativeClosedStablePlaque F γ x ∧ z ∈ Gs}) ∧
      (∀ x i, x ∈ R i → x ∈ closure {z : Λ |
        z ∈ R i ∧ z ∈ Dynamics.relativeClosedUnstablePlaque F γ x ∧ z ∈ Gu}) by
    apply actual_two_sided_pattern_ranks F γ κ G (transition F R) R coding hit
      (fun i x hx ↦ (hlabels x 0 i).mp (by simpa using hx)) hclosed Gs Gu
      (allTimeGood_invariant F _) (allTimeGood_invariant F.symm _)
    · intro z hz
      simpa only [zpow_zero, Homeomorph.one_apply] using hz 0
    · intro z hz
      simpa only [zpow_zero, Homeomorph.one_apply] using hz 0
    · exact hdensity.1
    · exact hdensity.2
  constructor
  · intro x i hx
    simpa only [Gs, allTimeGood, Ps, Set.mem_ofPred_eq] using hstableDensity x i hx
  · intro x i hx
    simpa only [Gu, allTimeGood, Pu, Set.mem_ofPred_eq, revTransition,
      Dynamics.relativeClosedStablePlaque, Dynamics.relativeClosedUnstablePlaque] using
      hstableDensityRev x i hx



end Geometric
end BowenBasicSetCoding
end HolomorphicAnosov
