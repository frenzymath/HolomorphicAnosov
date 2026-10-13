import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimeSucc
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimeNatCast
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.IntegerPeriodicTimePeriod
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.TraceEqCardCycles
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphZpowEquiv
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.HomeomorphPowCoe
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.RestrictedIterateVal
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.PeriodicZpowRemainder
import HolomorphicAnosov.Topology.Franks.IrreduciblePeriodicGrowth
import HolomorphicAnosov.Topology.Franks.TransitivePartitionIrreducible
import HolomorphicAnosov.Topology.Franks.RestrictedTangentSubbundle
import HolomorphicAnosov.Dynamics.SmaleSpectralCore
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.RestrictedZpowVal
import HolomorphicAnosov.Dynamics.ManningSignedTraceSupport.CompatibleMetricExpansivity
import Mathlib.Tactic

/-!
# Periodic point counts from finite Markov itineraries

Source: Bowen, *Markov Partitions and Minimal Sets for Axiom A Diffeomorphisms*
(1970), Proposition 10 and Corollary 11, pp. 913–914; the direct count sandwich is
an agent-written consequence of finite-to-one coding and expansivity. Perron
bounds use Seneta, *Non-negative Matrices and Markov Chains*, Chapter 1. The
application uses the original Smale spectral decomposition on the same smooth
Anosov diffeomorphism and the same Riemannian metric.

A physical point fixed by the m-th iterate determines an admissible finite path.
Equality of paths gives equality of all orbit coordinates modulo m, and then
expansivity. Conversely, repeating a cyclic word gives a full periodic code;
its image is physically periodic, and each fibre is bounded by the full coding
multiplicity. Finite matrix path/trace identities and Perron estimates give
exponential bounds. On the original manifold, periodic points lie in a finite
disjoint union of basic components; their exact counts add, and a component of
maximal Perron rate controls the lower bound along its positive iterate.

The exponent base is positive, with no assertion that it exceeds one. This
includes a one-point system. All finiteness/count claims have positive period;
empty coding alphabets are allowed in the elementary sandwich. A physical
periodic point need not have a code of the same period.
-/

open Set Filter
open scoped ContDiff Manifold Bundle
open scoped BigOperators

namespace HolomorphicAnosov
open BowenBasicSetCoding
open Dynamics.ManningOriginalBasicSetSignedTraceG7
open Dynamics.ManningOriginalBasicSetSignedTraceG7.CodingAdapter

/-- Physical period-m points inject into admissible length-m paths under any
onto coding by rectangles of expansive mesh. Equality of the finite itinerary
makes all integer iterates close, by reduction modulo m, so expansivity applies.
Choose a full code over each fixed point by surjectivity and restrict to times
zero through m. Equality of restrictions puts the two physical orbits in the same
rectangle at every residue class. The periodic remainder identity extends the
mesh estimate to every integer time, so expansivity proves injectivity. The
finite path type then proves finiteness and the cardinal bound.
Source: the direct itinerary argument from Bowen (1970), Proposition 10,
pp. 913–914. -/
theorem periodic_points_finite_and_card_le_admissible_paths
    {X : Type*} [MetricSpace X] (F : X ≃ₜ X) {N : ℕ}
    (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X) (honto : Function.Surjective coding)
    (hmem : ∀ a j, (F^j) (coding a) ∈ R (a.val j))
    (e : ℝ) (hmesh : ∀ i, ∀ x ∈ R i, ∀ y ∈ R i, dist x y ≤ e)
    (hexp : ∀ x y, (∀ j : ℤ, dist ((F^j) x) ((F^j) y) ≤ e) → x = y)
    (m : ℕ) (hm : 0 < m) :
    Finite {x : X // (F^m) x = x} ∧
    Nat.card {x : X // (F^m) x = x} ≤
      Nat.card {w : Fin (m+1) → Fin N // ∀ i : Fin m, B (w i.castSucc) (w i.succ)} := by
  classical
  have hpow (j : ℤ) (x : X) : (F^j) x = (F.toEquiv^j) x :=
    congrArg (fun g : Equiv.Perm X ↦ g x) (CarrierAdapter.homeomorph_zpow_equiv F j)
  let S := {x : X // (F^m) x = x}
  let W := {w : Fin (m+1) → Fin N // ∀ i : Fin m, B (w i.castSucc) (w i.succ)}
  let a : S → CodeSpace B := fun x ↦ (honto x.val).choose
  have ha (x : S) : coding (a x) = x.val := (honto x.val).choose_spec
  let w : S → W := fun x ↦ ⟨fun i ↦ (a x).val i.val, fun i ↦ by
    simpa using (a x).property (i.val : ℤ)⟩
  have hw : Function.Injective w := by
    intro x y hxy
    apply Subtype.ext
    apply hexp
    intro j
    let t := integerPeriodicTime hm j
    have hlabel : (a x).val (t.val : ℤ) = (a y).val (t.val : ℤ) := by
      exact congrArg (fun v : W ↦ v.val t.castSucc) hxy
    have hx := hmem (a x) (t.val : ℤ)
    have hy := hmem (a y) (t.val : ℤ)
    rw [ha] at hx hy
    rw [← hlabel] at hy
    have hb := hmesh _ _ hx _ hy
    have hxr : (F.toEquiv^j) x.val = (F.toEquiv^t.val) x.val := by
      simpa only [t, integerPeriodicTime, Equiv.Perm.coe_pow] using
        periodic_zpow_remainder F.toEquiv hm (x := x.val) (by
          change ((F : X → X)^[m]) x.val = x.val
          simpa only [CarrierAdapter.homeomorph_pow_coe] using x.property) j
    have hyr : (F.toEquiv^j) y.val = (F.toEquiv^t.val) y.val := by
      simpa only [t, integerPeriodicTime, Equiv.Perm.coe_pow] using
        periodic_zpow_remainder F.toEquiv hm (x := y.val) (by
          change ((F : X → X)^[m]) y.val = y.val
          simpa only [CarrierAdapter.homeomorph_pow_coe] using y.property) j
    rw [hpow, hpow, zpow_natCast] at hb
    rw [hpow, hpow, hxr, hyr]
    exact hb
  exact ⟨Finite.of_injective w hw, Nat.card_le_card_of_injective w hw⟩

/-- Symbolic cycles project to physical points of the same period with no larger
fibres than the full coding map. Summing these fibres gives the lower physical
count. Repeat a length-m cyclic word using integer remainders. Its closing edge
makes the full code legal, and the m-th shift fixes it. Coding covariance gives
a physical fixed point. Restriction to one period proves that repetition is
injective; consequently each projected fibre injects into a full coding fibre.
Summing these finite fibre bounds gives the inequality.
Source: the finite-to-one coding count from Bowen (1970), Proposition 10,
pp. 913–914, with an agent-written finite-fibre argument. -/
theorem cyclic_words_card_le_fibre_mul_periodic_points
    {X : Type*} [TopologicalSpace X] (F : X ≃ₜ X) {N : ℕ}
    (B : Fin N → Fin N → Prop) (coding : CodeSpace B → X)
    (hcov : Function.Semiconj coding (codeShift B) F)
    (D : ℕ) (hfibre : ∀ x, {a : CodeSpace B | coding a = x}.encard ≤ (D : ℕ∞))
    (m : ℕ) (hm : 0 < m) [Finite {x : X // (F^m) x = x}] :
    Nat.card {w : Fin m → Fin N // ∀ i, B (w i) (w (nextTime hm i))} ≤
      D * Nat.card {x : X // (F^m) x = x} := by
  classical
  let W := {w : Fin m → Fin N // ∀ i, B (w i) (w (nextTime hm i))}
  let S := {x : X // (F^m) x = x}
  let full : W → CodeSpace B := fun w ↦
    ⟨fun j ↦ w.val (integerPeriodicTime hm j), fun j ↦ by
      dsimp only
      rw [integerPeriodicTime_succ]; exact w.property _⟩
  have hfull : Function.Injective full := by
    intro w v hwv
    apply Subtype.ext
    funext i
    have hh := congrArg (fun a : CodeSpace B ↦ a.val (i.val : ℤ)) hwv
    simpa only [full, integerPeriodicTime_natCast] using hh
  have hshift (a : CodeSpace B) (k : ℕ) (j : ℤ) :
      ((codeShift B)^[k] a).val j = a.val (j+k) := by
    induction k generalizing j with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      change ((codeShift B)^[k] a).val (1+j) = _
      rw [ih]
      exact congrArg a.val (by omega)
  have hperiodic (w : W) : (codeShift B)^[m] (full w) = full w := by
    apply Subtype.ext
    funext j
    rw [hshift]
    exact congrArg w.val (integerPeriodicTime_period hm j)
  let project : W → S := fun w ↦ ⟨coding (full w), by
    rw [CarrierAdapter.homeomorph_pow_coe]
    exact ((hcov.iterate_right m) (full w)).symm.trans (congrArg coding (hperiodic w))⟩
  let : Fintype S := Fintype.ofFinite S
  have hfib (x : S) : Nat.card {w : W // project w = x} ≤ D := by
    have hfin : {a : CodeSpace B | coding a = x.val}.Finite :=
      Set.encard_lt_top_iff.mp ((hfibre x.val).trans_lt (by simp))
    let : Finite {a : CodeSpace B // coding a = x.val} := hfin.to_subtype
    let incl : {w : W // project w = x} → {a : CodeSpace B // coding a = x.val} :=
      fun w ↦ ⟨full w.val, congrArg Subtype.val w.property⟩
    have hincl : Function.Injective incl := by
      intro w v hwv
      apply Subtype.ext
      exact hfull (congrArg Subtype.val hwv)
    have hbound : Nat.card {a : CodeSpace B // coding a = x.val} ≤ D := by
      change {a : CodeSpace B | coding a = x.val}.ncard ≤ D
      exact_mod_cast (show ({a : CodeSpace B | coding a = x.val}.ncard : ℕ∞) ≤ D by
        rw [hfin.cast_ncard_eq]; exact hfibre x.val)
    exact (Nat.card_le_card_of_injective incl hincl).trans hbound
  have hh := Finset.card_le_mul_card_image_of_maps_to
    (s := (Finset.univ : Finset W)) (t := (Finset.univ : Finset S))
    (f := project) (fun _ _ ↦ Finset.mem_univ _) D (by
      intro x _
      simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype] using hfib x)
  simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hh

/-- The sum of entries of the m-th zero-one matrix power counts all admissible
paths with m edges. Expand the endpoint path formula and reindex by the full
finite vertex tuple using the cons and snoc equivalences. Each path-edge
predicate contributes one precisely for an admissible tuple, so the sum is the
cardinality of the finite path subtype.
Source: the finite matrix path expansion used in Bowen (1970), pp. 913–914;
this reindexing is agent-written. -/
theorem admissible_paths_card_eq_matrix_sum {N m : ℕ}
    (B : Fin N → Fin N → Prop) (hm : 0 < m) :
    (Nat.card {w : Fin (m+1) → Fin N // ∀ i : Fin m,
      B (w i.castSucc) (w i.succ)} : ℤ) =
      ∑ i, ∑ j, (MatrixCounting.edgeMatrix B ^ m) i j := by
  classical
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Finset.sum_filter]
  symm
  simp_rw [MatrixCounting.matrix_power_path_sum]
  let e : (Fin N × ((Fin n → Fin N) × Fin N)) ≃ (Fin (n+1+1) → Fin N) :=
    (Equiv.prodCongr (Equiv.refl (Fin N)) ((Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (n+1) ↦ Fin N)))).trans
      (Fin.consEquiv (fun _ : Fin (n+1+1) ↦ Fin N))
  calc
    _ = ∑ p : Fin N × ((Fin n → Fin N) × Fin N),
        if MatrixCounting.PathEdges B p.1 p.2.2 p.2.1 then (1 : ℤ) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = _ := by
      apply Fintype.sum_equiv e
      intro p
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      change (if MatrixCounting.PathEdges B p.1 p.2.2 p.2.1 then (1 : ℤ) else 0) =
        if ∀ i : Fin (n+1),
          B ((Fin.cons (α := fun _ ↦ Fin N) p.1 (Fin.snoc (α := fun _ ↦ Fin N) p.2.1 p.2.2)) i.castSucc)
            ((Fin.cons (α := fun _ ↦ Fin N) p.1 (Fin.snoc (α := fun _ ↦ Fin N) p.2.1 p.2.2)) i.succ) then 1 else 0
      simp only [Fin.cons_succ, Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc,
        MatrixCounting.PathEdges]
      congr 1

/-- The physical periodic-point count lies between the principal symbolic trace
with bounded multiplicity and the ordinary symbolic path count. All quantities
refer to the same coding and transition matrix. Apply the preceding path
injection and cycle projection inequalities. Rewrite the path count as the sum
of matrix-power entries and the cyclic-word count as the trace, then cast both
natural cardinal inequalities into integers.
Source: Bowen (1970), Proposition 10, pp. 913–914; direct count sandwich. -/
theorem periodic_count_matrix_bounds
    {X : Type*} [MetricSpace X] (F : X ≃ₜ X) {N : ℕ}
    (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X) (honto : Function.Surjective coding)
    (hcov : Function.Semiconj coding (codeShift B) F)
    (hmem : ∀ a j, (F^j) (coding a) ∈ R (a.val j))
    (e : ℝ) (hmesh : ∀ i, ∀ x ∈ R i, ∀ y ∈ R i, dist x y ≤ e)
    (hexp : ∀ x y, (∀ j : ℤ, dist ((F^j) x) ((F^j) y) ≤ e) → x = y)
    (D : ℕ) (hfibre : ∀ x, {a : CodeSpace B | coding a = x}.encard ≤ (D : ℕ∞))
    (m : ℕ) (hm : 0 < m) :
    Finite {x : X // (F^m) x = x} ∧
      Matrix.trace (MatrixCounting.edgeMatrix B ^ m) ≤
        D * (Nat.card {x : X // (F^m) x = x} : ℤ) ∧
      (Nat.card {x : X // (F^m) x = x} : ℤ) ≤
        ∑ i, ∑ j, (MatrixCounting.edgeMatrix B ^ m) i j := by
  obtain ⟨hfin,hupp⟩ := periodic_points_finite_and_card_le_admissible_paths
    F B R coding honto hmem e hmesh hexp m hm
  let : Finite {x : X // (F^m) x = x} := hfin
  have hlow := cyclic_words_card_le_fibre_mul_periodic_points F B coding hcov D hfibre m hm
  refine ⟨hfin,?_,?_⟩
  · rw [MatrixCounting.trace_eq_card_cycles B hm]
    exact_mod_cast hlow
  · rw [← admissible_paths_card_eq_matrix_sum B hm]
    exact_mod_cast hupp

/-- An irreducible finite-to-one coding with expansive mesh gives exponential
periodic-point upper bounds and a positive lower bound on a common iterate.
Map the zero-one integer matrix into the reals. Its entries are nonnegative;
apply irreducible Perron growth to the preceding count sandwich, using positivity
of the fibre bound to divide the lower trace estimate. Matrix powers and trace
commute with this scalar map, so all bounds use the same transition matrix.
Source: Bowen (1970), pp. 913–914, and Seneta, Chapter 1. -/
theorem periodic_count_exponential_bounds_of_coding
    {X : Type*} [MetricSpace X] (F : X ≃ₜ X) {N : ℕ} [Nonempty (Fin N)]
    (B : Fin N → Fin N → Prop) (R : Fin N → Set X)
    (coding : CodeSpace B → X) (honto : Function.Surjective coding)
    (hcov : Function.Semiconj coding (codeShift B) F)
    (hmem : ∀ a j, (F^j) (coding a) ∈ R (a.val j))
    (e : ℝ) (hmesh : ∀ i, ∀ x ∈ R i, ∀ y ∈ R i, dist x y ≤ e)
    (hexp : ∀ x y, (∀ j : ℤ, dist ((F^j) x) ((F^j) y) ≤ e) → x = y)
    (D : ℕ) (hD : 0 < D) (hfibre : ∀ x, {a : CodeSpace B | coding a = x}.encard ≤ (D : ℕ∞))
    (hirr : ((MatrixCounting.edgeMatrix B).map (Int.castRingHom ℝ)).IsIrreducible) :
    (∀ m : ℕ, 0 < m → Finite {x : X // (F^m) x = x}) ∧
    ∃ ρ a b : ℝ, ∃ q : ℕ, 0 < ρ ∧ 0 < a ∧ 0 < b ∧ 0 < q ∧
      (∀ m : ℕ, 0 < m → (Nat.card {x : X // (F^m) x = x} : ℝ) ≤ b*ρ^m) ∧
      ∀ᶠ m : ℕ in atTop, a*ρ^(q*m) ≤ (Nat.card {x : X // (F^(q*m)) x = x} : ℝ) := by
  let A : Matrix (Fin N) (Fin N) ℝ := (MatrixCounting.edgeMatrix B).map (Int.castRingHom ℝ)
  have hA : ∀ i j, 0 ≤ A i j := by
    classical
    intro i j
    simp only [A,Matrix.map_apply,MatrixCounting.edgeMatrix]
    split_ifs <;> norm_num
  refine ⟨fun m hm ↦ (periodic_count_matrix_bounds F B R coding honto hcov hmem e hmesh hexp D hfibre m hm).1, ?_⟩
  apply count_exponential_bounds_of_irreducible_matrix A hA hirr
    (fun m ↦ (Nat.card {x : X // (F^m) x = x} : ℝ)) (D:ℝ) (by exact_mod_cast hD)
  intro m hm
  obtain ⟨_,hlow,hupp⟩ := periodic_count_matrix_bounds F B R coding honto hcov hmem e hmesh hexp D hfibre m hm
  have hpow : (MatrixCounting.edgeMatrix B^m).map (Int.castRingHom ℝ) = A^m :=
    Matrix.map_pow _ _ _
  constructor
  · have hh : ((Matrix.trace (MatrixCounting.edgeMatrix B^m) : ℤ) : ℝ) ≤
        (D:ℝ)*(Nat.card {x : X // (F^m) x = x} : ℝ) := by exact_mod_cast hlow
    simpa only [← hpow, Matrix.trace,Matrix.diag,Matrix.map_apply,Int.cast_sum,
      Int.coe_castRingHom] using hh
  · have hh : (Nat.card {x : X // (F^m) x = x} : ℝ) ≤
        ((∑ i, ∑ j, (MatrixCounting.edgeMatrix B^m) i j : ℤ) : ℝ) := by exact_mod_cast hupp
    simpa only [← hpow,Matrix.map_apply,Int.cast_sum,Int.coe_castRingHom] using hh

/-- Arbitrarily fine proper finite-to-one codings of a transitive compact system
supply the required exponential periodic-point bounds. An initial coding gives
expansivity in a compatible metric; request the final coding only after
transferring an expansive radius to the original metric. For the initial coding,
the unique diagonal bracket in a rectangle containing x shows that an orbit
remaining within the plaque radius of x equals x. Compact metric compatibility
transfers this to the original metric. Request a final coding with mesh smaller
than that radius. Transitivity and properness make its matrix irreducible; then
the preceding theorem applies with its positive coding multiplicity.
Source: Bowen (1970), Proposition 10 and Corollary 11, pp. 913–914. -/
theorem periodic_count_growth_of_small_codings
    {X : Type*} [old : MetricSpace X] [CompactSpace X] (F : X ≃ₜ X)
    (htrans : ∀ U V : Set X, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
      ∃ n : ℕ, (((F^n : X ≃ₜ X) : X → X) '' U ∩ V).Nonempty)
    (hcode : ∀ ε : ℝ, 0 < ε → ∃ N D : ℕ, 1 ≤ N ∧ 1 ≤ D ∧
      ∃ δ : MetricSpace X, δ.toUniformSpace.toTopologicalSpace = old.toUniformSpace.toTopologicalSpace ∧
      letI : MetricSpace X := old
      ∃ γ : ℝ, 0 < γ ∧ ∃ R : Fin N → Set X,
      (∀ i, IsRectangle F δ.dist γ (R i) ∧ Metric.diam (R i) < ε) ∧
      (∀ i j, i ≠ j → Disjoint (interior (R i)) (interior (R j))) ∧
      (⋃ i, R i) = univ ∧
      ∃ coding : CodeSpace (BowenBasicSetCoding.transition F R) → X,
        Function.Surjective coding ∧
        Function.Semiconj coding (codeShift (BowenBasicSetCoding.transition F R)) F ∧
        (∀ a j, (F^j) (coding a) ∈ R (a.val j)) ∧
        (∀ x, {a | coding a = x}.encard ≤ (D:ℕ∞))) :
    (∀ m : ℕ, 0 < m → Finite {x : X // (F^m) x = x}) ∧
    ∃ ρ a b : ℝ, ∃ q : ℕ, 0 < ρ ∧ 0 < a ∧ 0 < b ∧ 0 < q ∧
      (∀ m : ℕ, 0 < m → (Nat.card {x : X // (F^m) x = x} : ℝ) ≤ b*ρ^m) ∧
      ∀ᶠ m : ℕ in atTop, a*ρ^(q*m) ≤ (Nat.card {x : X // (F^(q*m)) x = x} : ℝ) := by
  classical
  obtain ⟨N₀,D₀,_,_,δ,hδ,γ,hγ,R₀,hR₀,_,hcover₀,_⟩ := hcode 1 zero_lt_one
  let : MetricSpace X := old
  have hpow (j : ℤ) (x : X) : (F^j) x = (F.toEquiv^j) x :=
    congrArg (fun g : Equiv.Perm X ↦ g x) (CarrierAdapter.homeomorph_zpow_equiv F j)
  have hexpδ : ∀ x y : X, (∀ j : ℤ, δ.dist ((F.toEquiv^j) x) ((F.toEquiv^j) y) ≤ γ) → x=y := by
    intro x y hxy
    obtain ⟨i,hi⟩ := mem_iUnion.mp (show x ∈ ⋃ i, R₀ i by rw [hcover₀]; trivial)
    obtain ⟨z,_,hu⟩ := (hR₀ i).1.2.2.2 x hi x hi
    have hxz : x=z := (hu x).mp ⟨by intro k; simpa only [δ.dist_self] using hγ.le,
      by intro k; simpa only [δ.dist_self] using hγ.le⟩
    have hyz : y=z := (hu y).mp ⟨by
      intro k
      have hh := hxy (k:ℤ)
      rw [← hpow,← hpow] at hh
      simpa only [δ.dist_comm,zpow_natCast] using hh, by
      intro k
      simpa only [δ.dist_comm,← hpow] using hxy (-(k:ℤ))⟩
    exact hxz.trans hyz.symm
  obtain ⟨e,he,hexp⟩ := MetricAdapter.compatible_metric_expansivity δ hδ F.toEquiv hγ hexpδ
  obtain ⟨N,D,hN,hD,δ',hδ',γ',hγ',R,hR,hdisj,hcover,coding,honto,hcov,hmem,hfibre⟩ := hcode e he
  let : MetricSpace X := old
  have : Nonempty (Fin N) := ⟨⟨0,by omega⟩⟩
  have hirr : ((MatrixCounting.edgeMatrix (BowenBasicSetCoding.transition F R)).map (Int.castRingHom ℝ)).IsIrreducible := by
    have hh := transitive_partition_irreducible F R (fun i ↦ (hR i).1.1)
      (fun i ↦ (hR i).1.2.2.1) hcover hdisj htrans
    convert hh using 1
    ext i j
    simp only [Matrix.map_apply,MatrixCounting.edgeMatrix,Matrix.of_apply,Int.coe_castRingHom]
    split_ifs <;> norm_num
  apply periodic_count_exponential_bounds_of_coding F (BowenBasicSetCoding.transition F R) R coding
    honto hcov hmem e (fun i x hx y hy ↦
      (Metric.dist_le_diam_of_mem (hR i).1.2.1.isBounded hx hy).trans (hR i).2.le)
    (fun x y hxy ↦ hexp x y (by simpa only [← hpow] using hxy)) D (by omega) hfibre hirr

/-- Bowen coding and Perron growth give periodic-count bounds on the original
hyperbolic basic set. Give the compact subset its relative compact-space
instance. The basic-set Markov coding theorem provides arbitrarily fine proper
codings in compatible metrics. The singleton itinerary identity supplies orbit
membership in every coded rectangle; its surjectivity, covariance and finite
fibre bound are exactly the preceding theorem's hypotheses.
Source: Bowen (1970), Proposition 10 and Corollary 11, pp. 913–914. -/
theorem hyperbolic_basic_set_periodic_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {M : Type*} [MetricSpace M] [CompactSpace M]
    [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    (f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hmetric : HasOriginalRiemannianDistance (E := E) (M := M))
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
    (htransitive :
      let F := restrictedDynamics f.toHomeomorph Λ hΛinvariant
      ∀ U V : Set Λ, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
        ∃ n : ℕ, (((F ^ n : Λ ≃ₜ Λ) : Λ → Λ) '' U ∩ V).Nonempty) :
    let F := restrictedDynamics f.toHomeomorph Λ hΛinvariant
    (∀ m : ℕ, 0 < m → Finite {x : Λ // (F^m) x = x}) ∧
    ∃ ρ a b : ℝ, ∃ q : ℕ, 0 < ρ ∧ 0 < a ∧ 0 < b ∧ 0 < q ∧
      (∀ m : ℕ, 0 < m → (Nat.card {x : Λ // (F^m) x = x} : ℝ) ≤ b*ρ^m) ∧
      ∀ᶠ m : ℕ in atTop, a*ρ^(q*m) ≤ (Nat.card {x : Λ // (F^(q*m)) x = x} : ℝ) := by
  classical
  let F := restrictedDynamics f.toHomeomorph Λ hΛinvariant
  let : CompactSpace Λ := isCompact_iff_compactSpace.mp hΛcompact
  apply periodic_count_growth_of_small_codings F htransitive
  intro ε hε
  obtain ⟨N,D,hN,hD,δ,hδ,γ,hγ,R,hR,hdisj,hcover,hmarkov,coding,hit,hcont,honto,hcov,hfibre,hlabels,hperiod,hsplice⟩ :=
    hyperbolic_basic_set_markov_coding f hmetric Λ hΛne hΛcompact hΛinvariant
      stable unstable hstableContinuous hunstableContinuous hcompl hstableInvariant hunstableInvariant
      C rate hC hratepos hratelt hstableBound hunstableBound hlocalMaximal htransitive ε hε
  exact ⟨N,D,hN,hD,δ,hδ,γ,hγ,R,hR,hdisj,hcover,coding,honto,hcov,
    fun a j ↦ (show coding a ∈ {x : Λ | ∀ j : ℤ, (F^j) x ∈ R (a.val j)} by
      rw [hit a]; exact Set.mem_singleton _) j,hfibre⟩

/-- Finite disjoint invariant components exhaust all periodic points, so their
periodic counts sum to the whole count. The component of maximal exponential
rate supplies the lower bound and the sum of coefficients supplies the upper.
The disjoint union of component fixed-point types maps to the whole fixed-point
type by inclusion. Disjointness proves injectivity, and the periodic cover proves
surjectivity; hence the type is finite and its cardinality is the exact finite
sum. Apply the finite-sum exponential-bound theorem and rewrite by this equality
at positive multiples of the selected component's period.
Source: the finite-component reduction in Manning (1974), Theorem A,
pp. 425–426; this exact finite-cardinality proof is agent-written. -/
theorem periodic_count_growth_of_finite_components
    {X : Type*} [MetricSpace X] (F : X ≃ₜ X) {b : ℕ} [Nonempty (Fin b)]
    (L : Fin b → Set X) (hinv : ∀ i x, x ∈ L i ↔ F x ∈ L i)
    (hdisj : Pairwise (fun i j ↦ Disjoint (L i) (L j)))
    (hcover : ∀ m : ℕ, 0 < m → ∀ x, (F^m) x=x → ∃ i, x ∈ L i)
    (hgrowth : ∀ i,
      let G := F.subtype (hinv i)
      (∀ m : ℕ, 0 < m → Finite {x : L i // (G^m) x = x}) ∧
      ∃ ρ a b : ℝ, ∃ q : ℕ, 0 < ρ ∧ 0 < a ∧ 0 < b ∧ 0 < q ∧
        (∀ m : ℕ, 0 < m → (Nat.card {x : L i // (G^m) x = x} : ℝ) ≤ b*ρ^m) ∧
        ∀ᶠ m : ℕ in atTop, a*ρ^(q*m) ≤ (Nat.card {x : L i // (G^(q*m)) x = x} : ℝ)) :
    (∀ m : ℕ, 0 < m → Finite {x : X // (F^m) x = x}) ∧
    ∃ r a b : ℝ, ∃ q : ℕ, 0 < r ∧ 0 < a ∧ 0 < b ∧ 0 < q ∧
      ∀ᶠ m : ℕ in atTop, a*r^m ≤ (Nat.card {x : X // (F^(q*m)) x = x} : ℝ) ∧
        (Nat.card {x : X // (F^(q*m)) x = x} : ℝ) ≤ b*r^m := by
  classical
  let G (i : Fin b) := F.subtype (hinv i)
  have hcard (m : ℕ) (hm : 0 < m) : Finite {x : X // (F^m) x=x} ∧
      Nat.card {x : X // (F^m) x=x} = ∑ i, Nat.card {x : L i // (G i^m) x=x} := by
    let (i : Fin b) : Finite {x : L i // (G i^m) x=x} := (hgrowth i).1 m hm
    let g : (Σ i, {x : L i // (G i^m) x=x}) → {x : X // (F^m) x=x} := fun y ↦
      ⟨y.2.val.val, by
        have hh := congrArg Subtype.val y.2.property
        simpa only [G,CarrierAdapter.restricted_iterate_val] using hh⟩
    have hginj : Function.Injective g := by
      rintro ⟨i,x⟩ ⟨j,y⟩ he
      have hv : x.val.val=y.val.val := congrArg Subtype.val he
      have hij : i=j := by
        by_contra h
        exact Set.disjoint_left.mp (hdisj h) x.val.property (hv ▸ y.val.property)
      subst j
      have hxy : x=y := Subtype.ext (Subtype.ext hv)
      cases hxy
      rfl
    have hgsurj : Function.Surjective g := by
      intro x
      obtain ⟨i,hi⟩ := hcover m hm x.val x.property
      refine ⟨⟨i,⟨⟨x.val,hi⟩,?_⟩⟩,rfl⟩
      apply Subtype.ext
      exact (CarrierAdapter.restricted_iterate_val F (L i) (hinv i) ⟨x.val,hi⟩ m).trans x.property
    refine ⟨Finite.of_surjective g hgsurj,?_⟩
    rw [← Nat.card_congr (Equiv.ofBijective g ⟨hginj,hgsurj⟩),Nat.card_sigma]
  refine ⟨fun m hm ↦ (hcard m hm).1,?_⟩
  obtain ⟨r,a,B,q,hr,ha,hB,hq,hlim⟩ := finite_sum_count_exponential_bounds
    (fun i m ↦ (Nat.card {x : L i // (G i^m) x=x} : ℝ)) (by intros; positivity)
    (fun i ↦ (hgrowth i).2)
  refine ⟨r,a,B,q,hr,ha,hB,hq,?_⟩
  filter_upwards [hlim,eventually_ge_atTop 1] with m hm hmpos
  rw [(hcard (q*m) (Nat.mul_pos hq (by omega))).2,Nat.cast_sum]
  exact hm

/-- Manning's periodic-count growth input on the original smooth Anosov
manifold. Smale's finite basic components give irreducible Bowen codings; the
maximal Perron rate bounds the sum of their actual physical periodic counts.
Apply the original Smale spectral-core theorem. Every periodic point belongs to
the resulting finite disjoint invariant union because it lies in the closure of
periodic points. On each component, transfer its dense integer orbit and dense
periodic set through subtype inclusion to obtain forward transitivity. Restrict
the two original continuous tangent subbundles, keep the original smooth metric,
and increase C to max(1,C). The basic-set theorem gives the component growth
bounds, and the exact finite-component count theorem gives the conclusion.
Source: Smale's spectral decomposition and Manning (1974), Theorem A,
pp. 425–426; the count sandwich replaces the signed-trace asymptotic step. -/
theorem original_anosov_periodic_growth
    {n : ℕ} {M : Type*} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [Nonempty M] [SecondCountableTopology M]
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (Es Eu : ContinuousRealTangentSubbundle
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M)
    (metric : Bundle.ContMDiffRiemannianMetric
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M => TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x))
    (C lam : ℝ) :
    let I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨metric.toRiemannianMetric⟩
    IsRiemannianManifold I M →
    0 < C → 0 < lam → lam < 1 →
    (∀ x, IsCompl (Es.toDistribution x) (Eu.toDistribution x)) →
    (∀ x, (Es.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Es.toDistribution (f x)) →
    (∀ x, (Eu.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Eu.toDistribution (f x)) →
    (∀ x k (v : TangentSpace I x), v ∈ Es.toDistribution x →
      ‖mfderiv I I ((f : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    (∀ x k (v : TangentSpace I x), v ∈ Eu.toDistribution x →
      ‖mfderiv I I ((f.symm : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    (∀ m : ℕ, 0 < m → Finite {x : M // (f.toHomeomorph^m) x=x}) ∧
    ∃ r a b : ℝ, ∃ q : ℕ, 0 < r ∧ 0 < a ∧ 0 < b ∧ 0 < q ∧
      ∀ᶠ m : ℕ in atTop, a*r^m ≤ (Nat.card {x : M // (f.toHomeomorph^(q*m)) x=x} : ℝ) ∧
        (Nat.card {x : M // (f.toHomeomorph^(q*m)) x=x} : ℝ) ≤ b*r^m := by
  classical
  intro I hR hC hlam hlam1 hcompl hEs hEu hs hu
  let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨metric.toRiemannianMetric⟩
  let : IsRiemannianManifold I M := hR
  obtain ⟨hperiodic,b,L,hb,hL,hdisj,hΩ,horbit,hperiodicL,hisolated,hreturn⟩ :=
    smale_original_anosov_spectral_core f Es Eu metric C lam hR hC hlam hlam1 hcompl hEs hEu hs hu
  have : Nonempty (Fin b) := ⟨⟨0,by omega⟩⟩
  have hinv (i) (x : M) : x ∈ L i ↔ f.toHomeomorph x ∈ L i := by
    constructor
    · intro hx
      rw [← (hL i).2.2]
      exact mem_image_of_mem f hx
    · intro hx
      rw [← (hL i).2.2] at hx
      obtain ⟨y,hy,he⟩ := hx
      exact f.injective he ▸ hy
  let G (i : Fin b) := f.toHomeomorph.subtype (hinv i)
  have hval (i) (m : ℕ) (x : L i) : ((G i^m) x).val = ((f : M → M)^[m]) x.val := by
    simpa only [CarrierAdapter.homeomorph_pow_coe,Diffeomorph.coe_toHomeomorph] using
      CarrierAdapter.restricted_iterate_val f.toHomeomorph (L i) (hinv i) x m
  apply periodic_count_growth_of_finite_components f.toHomeomorph L hinv hdisj
  · intro m hm x hx
    have hper : x ∈ Function.periodicPts (f : M → M) := Function.mem_periodicPts.mpr
      ⟨m,hm,by
        change ((f : M → M)^[m]) x = x
        simpa only [CarrierAdapter.homeomorph_pow_coe,Diffeomorph.coe_toHomeomorph] using hx⟩
    have hxΩ := (show x ∈ closure (Function.periodicPts (f : M → M)) from subset_closure hper)
    rw [hperiodic,hΩ] at hxΩ
    exact mem_iUnion.mp hxΩ
  · intro i
    let : CompactSpace (L i) := isCompact_iff_compactSpace.mp (hL i).2.1
    obtain ⟨x,hx,horb⟩ := horbit i
    have himage : Subtype.val '' Set.range (fun j : ℤ ↦ (G i^j) (⟨x,hx⟩ : L i)) =
        Set.range (fun j : ℤ ↦ (f.toEquiv^j) x) := by
      rw [← Set.range_comp]
      congr 1
      funext j
      exact (CarrierAdapter.restricted_zpow_val f.toHomeomorph (L i) (hinv i) j ⟨x,hx⟩).trans
        (congrArg (fun g : Equiv.Perm M ↦ g x) (CarrierAdapter.homeomorph_zpow_equiv f.toHomeomorph j))
    have hdense : Dense (Set.range (fun j : ℤ ↦ (G i^j) (⟨x,hx⟩ : L i))) := by
      apply Subtype.dense_iff.mpr
      rw [himage,horb]
    have hperimage : Subtype.val '' Function.periodicPts (G i : L i → L i) =
        Function.periodicPts (f : M → M) ∩ L i := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩
        obtain ⟨m,hm,hzm⟩ := Function.mem_periodicPts.mp hz
        refine ⟨Function.mem_periodicPts.mpr ⟨m,hm,?_⟩,z.property⟩
        change ((f : M → M)^[m]) z.val = z.val
        rw [← hval]
        exact congrArg Subtype.val (show (G i^m) z=z by simpa only [CarrierAdapter.homeomorph_pow_coe] using hzm.eq)
      · rintro ⟨hy,hyL⟩
        obtain ⟨m,hm,hym⟩ := Function.mem_periodicPts.mp hy
        refine ⟨⟨y,hyL⟩,Function.mem_periodicPts.mpr ⟨m,hm,?_⟩,rfl⟩
        change ((G i : L i → L i)^[m]) ⟨y,hyL⟩ = ⟨y,hyL⟩
        rw [← CarrierAdapter.homeomorph_pow_coe]
        apply Subtype.ext
        exact (hval i m ⟨y,hyL⟩).trans hym
    have hpdense : Dense (Function.periodicPts (G i : L i → L i)) := by
      apply Subtype.dense_iff.mpr
      rw [hperimage,hperiodicL i]
    have htrans := forward_transitive_of_dense_integer_orbit_and_periodic (G i) ⟨x,hx⟩ hdense hpdense
    have hlocal : ∃ U : Set M, IsOpen U ∧ L i ⊆ U ∧
        L i = ⋂ j : ℤ, ((f.toHomeomorph^j : M ≃ₜ M) : M → M) '' U := by
      have he (j : ℤ) : (fun x : M ↦ (f.toEquiv^j) x) = ((f.toHomeomorph^j : M ≃ₜ M) : M → M) := by
        funext x
        exact (congrArg (fun g : Equiv.Perm M ↦ g x) (CarrierAdapter.homeomorph_zpow_equiv f.toHomeomorph j)).symm
      simpa only [he] using hisolated i
    have hscale (k : ℕ) (x : M) (v : TangentSpace I x) : C*lam^k*‖v‖ ≤ max 1 C*lam^k*‖v‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 C) (pow_nonneg hlam.le _)) (norm_nonneg _)
    apply hyperbolic_basic_set_periodic_growth f (fun x y _ ↦ hR.out x y)
      (L i) (hL i).1 (hL i).2.1 (hinv i) Es.toDistribution Eu.toDistribution
      (continuous_tangent_subbundle_restrict Es (L i)) (continuous_tangent_subbundle_restrict Eu (L i))
      (fun x _ ↦ hcompl x) (fun x _ ↦ hEs x) (fun x _ ↦ hEu x)
      (max 1 C) lam (le_max_left _ _) hlam hlam1
      (fun k x _ v hv ↦ (hs x k v hv).trans (hscale k x v))
      (fun k x _ v hv ↦ (hu x k v hv).trans (hscale k x v)) hlocal htrans

end HolomorphicAnosov








