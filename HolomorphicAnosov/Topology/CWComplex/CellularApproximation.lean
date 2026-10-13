import HolomorphicAnosov.Topology.CWComplex.SkeletalImprovement
import HolomorphicAnosov.Topology.CWComplex.HatcherDyadicCellularHomotopy

/-!
# Relative cellular approximation

Source: Hatcher, *Algebraic Topology*, Theorem 4.8, pp. 349–351.
This module states relative cellular approximation for arbitrary Hausdorff CW complexes.
It uses Mathlib's classical CW complexes, subcomplexes, finite skeleta and relative homotopies.
No finiteness or regularity of the cell structure is assumed.
-/

namespace HolomorphicAnosov.Topology.CWComplex

universe u v

open Set

/-- Every continuous map between Hausdorff CW complexes that is cellular on a subcomplex
is homotopic relative to that subcomplex to a cellular map.

Here `skeleton n` contains exactly the cells of dimensions at most `n`.
`HomotopyRel f c A` is a continuous map from the product of the closed unit interval and `X`
to `Y`, with time-zero map `f`, time-one map `c`, and value `f a` at every time for `a ∈ A`.
Both empty and entire subcomplexes are allowed, as are infinitely many cells and skeleta.

Source: Hatcher, *Algebraic Topology*, Theorem 4.8, p. 349 and proof pp. 349–351;
Lemma 4.10, pp. 350–351; Proposition 0.16, p. 15; Proposition A.1, p. 520;
quotient-product Proposition A.17, pp. 532–533. The DAG proof is as follows.

C1. Assume inductively that the current map f_n:X→Y is cellular on X^{n−1} and equals the original
f on A, starting at n=0 with X^{−1}=∅. For an n-cell e of X not in A, pull back through its
characteristic disk, or a homeomorphic characteristic cube I^n. The boundary already maps into
Y^{n−1}. Its whole characteristic image is compact. The compact-CW theorem gives a finite target
subcomplex L containing that image. This use is made separately for each source cell; there is no
uniform finite target subcomplex for all n-cells.

C2. If L has no cells above dimension n, this disk already maps into Y^n. Otherwise choose a
highest-dimensional cell E of L of dimension k>n. Because E has highest dimension, W=L\E is a
subcomplex and L is obtained by attaching this one k-cell to W. The source boundary maps into
Y^{n−1}⊆Y^n, so it avoids E and lies in W. Apply the local missed-point homotopy theorem to the
characteristic cube map I^n→L. It gives a homotopy fixed on the inverse image of W, in particular
on the source boundary, to a map missing p in E. The implemented local theorem adapts
Bredon IV.11.2, p.207, which assumes a disk boundary mapping into W. For the stronger
arbitrary-cube supplier, first extend the cube map to Euclidean space by coordinate clamping,
then use Bredon II.11.7, pp.96–97, to smooth the open-cell chart map off the closed complement
of a relatively compact chart region,
and choose a point outside its lower-dimensional smooth image. The homotopy is stationary
outside that region, so it extends continuously across the open-cell boundary. The arbitrary-cube
clamping adaptation remains agent-origin in its own supplier node. The homotopy stays within L and does not add target cells.

C3. Push the punctured top cell to its attaching boundary. In its characteristic disk let p̂∈int
D^k be the preimage of p. For z≠p̂ let v=z−p̂ and let λ(v)>0 be the positive root of ||p̂+λv||²=1,
namely λ(v)=(-⟨p̂,v⟩+sqrt(⟨p̂,v⟩²+(1−||p̂||²)||v||²))/||v||². For z in D^k\{p̂}, λ(v)≥1 and is
continuous. Set R_s(z)=(1−s)z+s(p̂+λ(v)v). Convexity keeps this in D^k; at s=0 it is z, at s=1 it
lies in ∂D^k, and on the boundary λ=1 so every boundary point is fixed. Attach this homotopy to
the constant homotopy on W. Since the characteristic boundary values agree with their attaching
identifications, it descends to a homotopy on L\{p}, relative W, ending in W. For continuity, the
restricted attaching quotient remains quotient after removing the closed point p (an open subset
restriction); interval-product descent applies. Compose this homotopy with the map already missing
p. It remains fixed on the source boundary and eliminates E entirely.

C4. Repeat C2–C3 for top-dimensional cells until only dimensions at most n remain. Each step
removes a cell from the finite subcomplex L and keeps the image in the remaining subcomplex,
including all lower boundary cells; the process terminates after at most the number of its cells
above n. Concatenate these finitely many relative disk homotopies. For an n-cell in A instead use
the constant homotopy, since the assumed cellularity of f on A puts that cell in Y^n. The
resulting n-cell homotopies agree on all attaching boundaries because they are stationary there,
and agree with the constant homotopy on X^{n−1}∪A. Attach them simultaneously over all n-cells.
The characteristic disks form a quotient cover of X^n, and the interval is locally compact, so the
named product-descent theorem gives a jointly continuous homotopy on I×(X^n∪A), relative
X^{n−1}∪A, ending cellular on X^n. The choices and finite concatenation lengths may vary between
cells; joint continuity uses the CW quotient topology, not a uniform bound.

C5. The union B_n=X^n∪A is a subcomplex of X. Its just-constructed homotopy begins at f_n
restricted to B_n. The relative CW-pair HEP extends it to a jointly continuous homotopy H_n:I×X→Y
beginning at f_n. Because its prescribed values on A are constant, the extension is stationary on
A; likewise X^{n−1} stays fixed. Put f_{n+1}=H_n(1,·). Then f_{n+1} is cellular on X^n and remains
equal to f on A. This establishes the induction for all n without assuming HEP as an extra theorem
hypothesis.

C6. Let t_n=1−2^{−n}, so t_0=0 and t_n tends to1. On [t_n,t_{n+1}], define
F(t,x)=H_n((t−t_n)/(t_{n+1}−t_n),x); endpoint matching makes these finite consecutive pieces
continuous. Each x lies in a finite-dimensional cell, say dimension d. After stage d, it lies in
X^d, and every later stage n>d fixes X^{n−1} pointwise, hence fixes x. Thus define
c(x)=f_{d+1}(x), independent of the chosen larger skeleton, and F(1,x)=c(x). On a characteristic
closed d-cell, all points lie in X^d and the entire pullback homotopy becomes constant after
t_{d+1}; it is therefore continuous at time1 as well as on the finitely many earlier intervals.
This is eventual uniform stationarity on each single characteristic disk, not on all of X.

C7. The disjoint union of characteristic disks maps quotiently onto X. Indeed a subset with closed
pullback in every disk has compact closed-cell intersection images, closed because X is Hausdorff,
and the CW closed-cell criterion makes it closed in X; conversely continuity gives closed
pullbacks. The pullback of F to I times this disjoint union is jointly continuous by C6 on each
characteristic prism. Apply interval-product quotient descent to conclude F:I×X→Y jointly
continuous, including t=1. Its time1 slice c is continuous, and after stage n every point of X^n
maps into Y^n; later stages fix that skeleton. Therefore c(X^n)⊆Y^n for every n, and F(t,a)=f(a)
throughout.

C8. The case A=∅ gives ordinary cellular approximation; A=X already has cellular f and allows the
constant homotopy. For X=∅ the unique map and homotopy suffice. If Y=∅ and a continuous f exists
then X is empty. Zero-dimensional source cells are points: C2 uses k>0, and the smooth
missed-point theorem covers the zero-dimensional source; the push moves it into the 0-skeleton. Arbitrarily many cells
in any degree, infinitely many skeleta and nonregular characteristic maps cause no additional
assumptions: stationarity on attaching boundaries and the characteristic quotient topology handle
them.
-/
theorem cellularApproximation
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y]
    [_root_.Topology.CWComplex (Set.univ : Set X)]
    [_root_.Topology.CWComplex (Set.univ : Set Y)]
    (A : _root_.Topology.RelCWComplex.Subcomplex (Set.univ : Set X)) (f : C(X, Y))
    (hf : ∀ n : ℕ, Set.MapsTo f
      ((A : Set X) ∩
        (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X))
      (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y)) :
    ∃ c : C(X, Y),
      (∀ n : ℕ, Set.MapsTo c
        (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)
        (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set Y) (n : ℕ∞) : Set Y)) ∧
      Nonempty (ContinuousMap.HomotopyRel f c (A : Set X)) := by
  classical
  let P (n : ℕ) := {q : C(X, Y) // Set.EqOn q f A ∧
    ∀ m : ℕ, m < n → Set.MapsTo q
      (Topology.CWComplex.skeleton (Set.univ : Set X) (m : ℕ∞) : Set X)
      (Topology.CWComplex.skeleton (Set.univ : Set Y) (m : ℕ∞) : Set Y)}
  let start : P 0 := ⟨f, (fun _ _ ↦ rfl), fun _ hm ↦ (Nat.not_lt_zero _ hm).elim⟩
  have hnext (n : ℕ) (q : P n) : ∃ r : P (n + 1),
      ∃ H : ContinuousMap.HomotopyRel q.val r.val A,
      ∀ (m : ℕ), m < n → ∀ (t : unitInterval) x,
        x ∈ (Topology.CWComplex.skeleton (Set.univ : Set X) (m : ℕ∞) : Set X) →
        H (t, x) = q.val x := by
    obtain ⟨r, H, hfix, hcell⟩ := cw_skeletal_improvement A n q.val
      (fun x hx ↦ by
        rw [q.property.1 hx.1]
        exact hf n hx) q.property.2
    have hrA : Set.EqOn r f A := fun x hx ↦ (H.fst_eq_snd hx).symm.trans (q.property.1 hx)
    have hrCell : ∀ m : ℕ, m < n + 1 → Set.MapsTo r
        (Topology.CWComplex.skeleton (Set.univ : Set X) (m : ℕ∞) : Set X)
        (Topology.CWComplex.skeleton (Set.univ : Set Y) (m : ℕ∞) : Set Y) := by
      intro m hm
      rcases (Nat.lt_succ_iff.mp hm).lt_or_eq with hmn | rfl
      · intro x hx
        have he : r x = q.val x := (H.map_one_left x).symm.trans (hfix m hmn 1 x hx)
        rw [he]
        exact q.property.2 m hmn hx
      · exact hcell
    exact ⟨⟨r, hrA, hrCell⟩, H, hfix⟩
  let seq : ∀ n, P n := Nat.rec start (fun n q ↦ (hnext n q).choose)
  let G : ∀ n, ContinuousMap.HomotopyRel (seq n).val (seq (n + 1)).val A :=
    fun n ↦ (hnext n (seq n)).choose_spec.choose
  exact hatcher_dyadic_cellular_homotopy A (fun n ↦ (seq n).val) G
    (fun n t x hx ↦ (hnext (n + 1) (seq (n + 1))).choose_spec.choose_spec
      n (Nat.lt_succ_self n) t x hx)
    (fun n ↦ (seq (n + 1)).property.2 n (Nat.lt_succ_self n))

end HolomorphicAnosov.Topology.CWComplex
