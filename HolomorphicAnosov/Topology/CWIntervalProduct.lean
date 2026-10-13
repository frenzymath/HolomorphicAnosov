import HolomorphicAnosov.Topology.CWComplex.IntervalProductClosedCriterion
import HolomorphicAnosov.Topology.CWComplex.ProductClosedCellImage
import HolomorphicAnosov.Topology.CWComplex.EndpointPrismOpenCover
import HolomorphicAnosov.Topology.CWComplex.PrismPartialEquivData
import HolomorphicAnosov.Topology.CWComplex.EndpointSliceSubcomplex
import HolomorphicAnosov.Topology.CWComplex.EndpointPartialEquivData

/-!
# The original CW structure times the unit interval

Source: Fritsch–Piccinini, *Cellular Structures in Topology* (1990), Theorem 2.2.2,
printed p. 58, and the product-topology warning pp. 59–60. The ordinary-topology
justification is Hatcher, *Algebraic Topology*, Appendix, Theorem A.6 p. 524
(discussion starts p. 523), Proposition A.1 p. 520, and Propositions A.14–A.15
pp. 530–531. The supplied originals are `literature/Fritsch-Piccinini-Cellular-Structures-1990.pdf`
and `literature/hatcher-at.pdf`.

The quantified structure is actual Mathlib `CWComplex` data for the whole space
`X × unitInterval`, using its existing ordinary product topology. A degreewise
equivalence labels all cells by original endpoint and prism cells. All cell
images and native characteristic-map formulas are part of the conclusion.
Endpoint copies and their union are native original-indexed subcomplexes.

Mathlib's native disks are the maximum-norm balls in `Fin n → ℝ`, not Euclidean
norm balls. Splitting off `Fin.last d` identifies the closed `(d+1)`-disk with
the closed `d`-disk times `[-1,1]`. The affine-time formula is asserted only on
this exact closed disk; a total forward map can use the interval clamp outside
it. Cellular inclusions are stated by continuity and preservation of every
finite-dimensional skeleton, since Mathlib has no separate classical cellular
map predicate in this interface.
-/

open Set _root_.Topology

namespace HolomorphicAnosov.Topology

/-- The ordinary product with the original unit interval has the endpoint/prism
CW structure, with its original-indexed endpoint subcomplexes and cellular inclusions.

Source: Fritsch–Piccinini, Theorem 2.2.2, p. 58 and pp. 59–60; Hatcher,
Theorem A.6, p. 524, Proposition A.1, p. 520, and A.14–A.15, pp. 530–531.

Natural-language proof: The interval has two zero-cells and one one-cell. Its
zero-disk maps are the constants at 0 and 1. The one-disk map has coordinate
`s ↦ (s+1)/2` on `[-1,1]`; extend it to all real coordinates by the continuous
projection onto `[0,1]`. Its interior inverse is `t ↦ 2t-1`, and its boundary
maps to the endpoints. This gives the interval its usual topology and its
finite CW structure. In particular the interval is compact Hausdorff and
locally compact.

For the product in degree `n`, use the disjoint sum of original `n`-cells paired
with a Boolean endpoint and original `d`-cells with a witness `d+1=n` for the
prisms. This gives the stated degreewise cell equivalences with no cardinality
or global-dimension restriction. Following the multiplication/addition proof
of Fritsch–Piccinini, the `n`-skeleton is the union of `Xⁿ × {0,1}` and
`Xⁿ⁻¹ × I`, with a negative skeleton interpreted as empty. The characteristic
maps are the endpoint copies of the original maps and the product of each
original map with the interval map.

In the native maximum norm, a vector `w : Fin (d+1) → ℝ` is in the closed
unit ball exactly when its head is in the original closed unit ball and its
last coordinate is in `[-1,1]`. The same splitting identifies the open balls
with the product of the open head ball and `(-1,1)`. Coordinate split/join are
continuous inverses, including an empty head for `d=0`. Thus the product map
on the native closed disk has first component `χ(head w)` and time coordinate
`(w(last)+1)/2`. On the whole coordinate space use the continuous interval
clamp for time; it agrees with this formula on the closed disk. The original
characteristic inverse and the time coordinate `2t-1`, joined together, give
the total inverse function for the prism PartialEquiv. On the open source and
its stated target the original inverse identities and the affine identity
prove both PartialEquiv inverse laws. Endpoint PartialEquivs use the original
inverse and the fixed endpoint. Forward continuity on closed disks and inverse
continuity on the targets follow componentwise. No open cell is assumed open
in the ambient complex.

The open and closed images are exactly the sets asserted below, by split/join
and the original characteristic-image definitions. A prism boundary vector has
last coordinate `±1` or head on its sphere. The endpoint case lies in the two
endpoint closed copies of the original cell, of dimension `d`; the head case
lies in prisms over the finite lower-dimensional closed-cell family supplied
by the original frontier field. Endpoint boundaries use that same original
finite family at their fixed endpoint. These are finite families in strictly
lower product dimensions and give the unrestricted CW frontier field.
Original open-cell disjointness, the disjoint endpoint/interior time sets, and
the original covering property prove disjointness and coverage for all product
cells. At `d=0` the head sphere is empty and only the two prism endpoints occur.

For the weak topology one must keep the ordinary product topology. The
original CW weak topology and compact closed cells make `X` compactly generated.
Hatcher A.14 proves that currying a map on `X × I` is continuous by testing
compact time sets with the tube argument, and that uncurrying is continuous
because evaluation is continuous for locally compact `I`. A.15 applies these
facts to show that the ordinary product of compactly generated Hausdorff `X`
with locally compact `I` is compactly generated. Every compact subset of this
product projects to a compact subset of `X`, which A.1 places in a finite
subcomplex. Hence it is contained in finitely many of the actual product closed
cells. Testing closedness on these finitely many compact closed pieces proves
closedness on each compact subset, and compact generation then proves
closedness in the ordinary product. This is the written A.6 proof specialized
to the compact interval factor. Characteristic closed-disk surjections onto
closed-cell images are quotient maps because their sources are compact and
their targets Hausdorff; their products with the interval are likewise compact
Hausdorff surjections. Thus the same argument verifies the native weak-topology
field even when characteristic boundaries are noninjective. No regularity is
assumed and no disk is identified homeomorphically with its closed-cell image.

Package the resulting PartialEquivs and the source, continuity, disjointness,
frontier, weak-topology, and coverage fields into the actual `CWComplex` class
on the original product. Each endpoint family has carrier `X × {a}` and its
selected closed cells stay in that carrier. The union of both families has
carrier `X × {0,1}` and has the same closure property. The native subcomplex
constructor supplies the three subcomplexes with precisely these selected
original indices. Its inherited characteristic maps are the selected product
maps, so the displayed endpoint formulas are exactly the original maps with
the endpoint appended. Endpoint inclusions are continuous in the product
topology and take every original `n`-skeleton into the product `n`-skeleton,
as each original cell goes to its equal-dimensional endpoint cell. This is
cellularity. Empty `X` gives empty index types and the empty product structure;
unbounded dimension, arbitrary cardinality, and nonlocally finite complexes
require no changes to the construction or topology argument.
-/
theorem cw_interval_product
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [CWComplex (univ : Set X)] :
    ∃ K : CWComplex (univ : Set (X × unitInterval)),
      let : CWComplex (univ : Set (X × unitInterval)) := K
      ∃ labels : ∀ n : ℕ,
        ((Bool × RelCWComplex.cell (univ : Set X) n) ⊕
          (Σ d : ℕ, {_i : RelCWComplex.cell (univ : Set X) d // d + 1 = n})) ≃
            RelCWComplex.cell (univ : Set (X × unitInterval)) n,
      let endpoint := fun n a i ↦ labels n (Sum.inl (a, i))
      let prism := fun d i ↦ labels (d + 1) (Sum.inr ⟨d, ⟨i, rfl⟩⟩)
      (∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d) (a : Bool),
        CWComplex.openCell (C := univ) d (endpoint d a i) =
          (CWComplex.openCell (C := univ) d i).prod {if a then 1 else 0} ∧
        CWComplex.closedCell (C := univ) d (endpoint d a i) =
          (CWComplex.closedCell (C := univ) d i).prod {if a then 1 else 0} ∧
        ∀ z ∈ Metric.closedBall (0 : Fin d → ℝ) 1,
          Topology.RelCWComplex.map (C := univ) d (endpoint d a i) z =
            (Topology.RelCWComplex.map (C := univ) d i z, if a then 1 else 0)) ∧
      (∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d),
        CWComplex.openCell (C := univ) (d + 1) (prism d i) =
          (CWComplex.openCell (C := univ) d i).prod (Ioo (0 : unitInterval) 1) ∧
        CWComplex.closedCell (C := univ) (d + 1) (prism d i) =
          (CWComplex.closedCell (C := univ) d i).prod univ ∧
        ∀ w ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) 1,
          (Topology.RelCWComplex.map (C := univ) (d + 1) (prism d i) w).1 =
            Topology.RelCWComplex.map (C := univ) d i (fun j ↦ w j.castSucc) ∧
          ((Topology.RelCWComplex.map (C := univ) (d + 1) (prism d i) w).2 : ℝ) =
            (w (Fin.last d) + 1) / 2) ∧
      (∀ a : Bool, ∃ A : CWComplex.Subcomplex (univ : Set (X × unitInterval)),
        (A : Set (X × unitInterval)) = univ.prod {if a then 1 else 0} ∧
        (∀ n : ℕ, A.I n = range (endpoint n a)) ∧
        (∀ (n : ℕ) (i : RelCWComplex.cell (univ : Set X) n),
          ∃ j : RelCWComplex.cell (A : Set (X × unitInterval)) n,
            (j.1 : RelCWComplex.cell (univ : Set (X × unitInterval)) n) = endpoint n a i ∧
            ∀ z ∈ Metric.closedBall (0 : Fin n → ℝ) 1,
              Topology.RelCWComplex.map (C := (A : Set (X × unitInterval))) n j z =
                (Topology.RelCWComplex.map (C := univ) n i z, if a then 1 else 0))) ∧
      (∃ A : CWComplex.Subcomplex (univ : Set (X × unitInterval)),
        (A : Set (X × unitInterval)) = univ.prod {(0 : unitInterval), 1} ∧
        ∀ n : ℕ, A.I n = range (endpoint n false) ∪ range (endpoint n true)) ∧
      (∀ a : Bool, Continuous (fun x : X ↦ (x, if a then (1 : unitInterval) else 0)) ∧
        ∀ n : ℕ, MapsTo (fun x : X ↦ (x, if a then (1 : unitInterval) else 0))
          (CWComplex.skeleton (univ : Set X) n : Set X)
          (CWComplex.skeleton (univ : Set (X × unitInterval)) n : Set (X × unitInterval))) := by
  classical
  suffices hdata :
    ∃ K : CWComplex (univ : Set (X × unitInterval)),
      let : CWComplex (univ : Set (X × unitInterval)) := K
      ∃ labels : ∀ n : ℕ,
        ((Bool × RelCWComplex.cell (univ : Set X) n) ⊕
          (Σ d : ℕ, {i : RelCWComplex.cell (univ : Set X) d // d + 1 = n})) ≃
            RelCWComplex.cell (univ : Set (X × unitInterval)) n,
      let endpoint := fun n a i ↦ labels n (Sum.inl (a, i))
      let prism := fun d i ↦ labels (d + 1) (Sum.inr ⟨d, ⟨i, rfl⟩⟩)
      (∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d) (a : Bool),
        CWComplex.openCell (C := univ) d (endpoint d a i) =
          (CWComplex.openCell (C := univ) d i).prod {if a then 1 else 0} ∧
        CWComplex.closedCell (C := univ) d (endpoint d a i) =
          (CWComplex.closedCell (C := univ) d i).prod {if a then 1 else 0} ∧
        ∀ z ∈ Metric.closedBall (0 : Fin d → ℝ) 1,
          Topology.RelCWComplex.map (C := univ) d (endpoint d a i) z =
            (Topology.RelCWComplex.map (C := univ) d i z, if a then 1 else 0)) ∧
      (∀ (d : ℕ) (i : RelCWComplex.cell (univ : Set X) d),
        CWComplex.openCell (C := univ) (d + 1) (prism d i) =
          (CWComplex.openCell (C := univ) d i).prod (Ioo (0 : unitInterval) 1) ∧
        CWComplex.closedCell (C := univ) (d + 1) (prism d i) =
          (CWComplex.closedCell (C := univ) d i).prod univ ∧
        ∀ w ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) 1,
          (Topology.RelCWComplex.map (C := univ) (d + 1) (prism d i) w).1 =
            Topology.RelCWComplex.map (C := univ) d i (fun j ↦ w j.castSucc) ∧
          ((Topology.RelCWComplex.map (C := univ) (d + 1) (prism d i) w).2 : ℝ) =
            (w (Fin.last d) + 1) / 2) by
    obtain ⟨K, hK⟩ := hdata
    let : CWComplex (univ : Set (X × unitInterval)) := K
    obtain ⟨labels, hep, hpr⟩ := hK
    let endpoint := fun n a i ↦ labels n (Sum.inl (a, i))
    refine ⟨K, labels, hep, hpr, ?_, ?_, ?_⟩
    · intro a
      obtain ⟨A, hA, hI⟩ := endpoint_slice_subcomplex
        (if a then 1 else 0) (fun n ↦ endpoint n a) (fun n i z hz ↦ (hep n i a).2.2 z hz)
      refine ⟨A, hA, hI, ?_⟩
      intro n i
      have hi : endpoint n a i ∈ A.I n := by
        rw [hI]
        exact mem_range_self i
      refine ⟨⟨endpoint n a i, hi⟩, rfl, ?_⟩
      exact (hep n i a).2.2
    · obtain ⟨A, hA, hI⟩ := endpoint_range_subcomplex
        (fun n ↦ Bool × RelCWComplex.cell (univ : Set X) n)
        (fun n i ↦ endpoint n i.1 i.2)
        (univ.prod {(0 : unitInterval), 1}) (by
          intro n i y hy
          rw [(hep n i.2 i.1).2.1] at hy
          refine ⟨mem_univ _, ?_⟩
          rcases i with ⟨a, i⟩
          cases a
          · exact Or.inl hy.2
          · exact Or.inr hy.2) (by
          ext y
          constructor
          · intro hy
            rcases mem_iUnion.mp hy with ⟨n, hy⟩
            rcases mem_iUnion.mp hy with ⟨⟨a, i⟩, hy⟩
            rw [(hep n i a).1] at hy
            refine ⟨mem_univ _, ?_⟩
            cases a
            · exact Or.inl hy.2
            · exact Or.inr hy.2
          · intro hy
            have hx : y.1 ∈ ⋃ n, ⋃ i : RelCWComplex.cell (univ : Set X) n,
                CWComplex.openCell (C := univ) n i := by
              rw [CWComplex.iUnion_openCell_eq_complex]
              exact mem_univ _
            rcases mem_iUnion.mp hx with ⟨n, hx⟩
            rcases mem_iUnion.mp hx with ⟨i, hi⟩
            rcases hy.2 with h0 | h1
            · refine mem_iUnion_of_mem n (mem_iUnion_of_mem (false, i) ?_)
              rw [(hep n i false).1]
              exact ⟨hi, h0⟩
            · refine mem_iUnion_of_mem n (mem_iUnion_of_mem (true, i) ?_)
              rw [(hep n i true).1]
              exact ⟨hi, h1⟩)
      refine ⟨A, hA, ?_⟩
      intro n
      rw [hI]
      ext i
      constructor
      · rintro ⟨⟨a, j⟩, rfl⟩
        cases a
        · exact Or.inl ⟨j, rfl⟩
        · exact Or.inr ⟨j, rfl⟩
      · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
        · exact ⟨(false, j), rfl⟩
        · exact ⟨(true, j), rfl⟩
    · intro a
      refine ⟨continuous_id.prodMk continuous_const, ?_⟩
      intro n x hx
      rw [← CWComplex.iUnion_openCell_eq_skeleton] at hx ⊢
      rcases mem_iUnion.mp hx with ⟨d, hx⟩
      rcases mem_iUnion.mp hx with ⟨hd, hx⟩
      rcases mem_iUnion.mp hx with ⟨i, hi⟩
      refine mem_iUnion_of_mem d (mem_iUnion_of_mem hd
        (mem_iUnion_of_mem (endpoint d a i) ?_))
      rw [(hep d i a).1]
      exact ⟨hi, mem_singleton _⟩
  choose E hEs hEt hEf hEc hEi using (fun d i a ↦ endpoint_partial_equiv_data (X := X) d i a)
  choose P hPs hPt hPf hPc hPi using (fun d i ↦ prism_partial_equiv_data (X := X) d i)
  let C := fun n ↦ (Bool × RelCWComplex.cell (univ : Set X) n) ⊕
    (Σ d : ℕ, {i : RelCWComplex.cell (univ : Set X) d // d + 1 = n})
  let M : ∀ n, C n → PartialEquiv (Fin n → ℝ) (X × unitInterval) := fun n c ↦
    match c with
    | .inl (a, i) => E n i a
    | .inr ⟨d, ⟨i, h⟩⟩ => h ▸ P d i
  have me (n) (a) (i) : M n (.inl (a, i)) = E n i a := rfl
  have mp (d) (i) : M (d + 1) (.inr ⟨d, ⟨i, rfl⟩⟩) = P d i := rfl
  have ms (n) (c : C n) : (M n c).source = Metric.ball 0 1 := by
    rcases c with ⟨a, i⟩ | ⟨d, i, rfl⟩
    · exact hEs n i a
    · exact hPs d i
  have eo (n) (a) (i) : M n (.inl (a, i)) '' Metric.ball 0 1 =
      (CWComplex.openCell (C := (univ : Set X)) n i).prod {if a then 1 else 0} := by
    rw [← ms n (.inl (a, i)), PartialEquiv.image_source_eq_target]
    exact hEt n i a
  have po (d) (i) : M (d + 1) (.inr ⟨d, ⟨i, rfl⟩⟩) '' Metric.ball 0 1 =
      (CWComplex.openCell (C := (univ : Set X)) d i).prod (Ioo (0 : unitInterval) 1) := by
    rw [← ms (d + 1) (.inr ⟨d, ⟨i, rfl⟩⟩), PartialEquiv.image_source_eq_target]
    exact hPt d i
  have ec (n) (a) (i) : M n (.inl (a, i)) '' Metric.closedBall 0 1 =
      (CWComplex.closedCell (C := (univ : Set X)) n i).prod {if a then 1 else 0} :=
    endpoint_closed_image n i _ _ (fun z _ ↦ hEf n i a z)
  have pc (d) (i) : M (d + 1) (.inr ⟨d, ⟨i, rfl⟩⟩) '' Metric.closedBall 0 1 =
      (CWComplex.closedCell (C := (univ : Set X)) d i).prod univ :=
    prism_closed_image d i _ (hPf d i)
  have same (n m) (i : RelCWComplex.cell (univ : Set X) n)
      (j : RelCWComplex.cell (univ : Set X) m) (x : X)
      (hi : x ∈ CWComplex.openCell (C := univ) n i)
      (hj : x ∈ CWComplex.openCell (C := univ) m j) :
      (⟨n, i⟩ : Σ n, RelCWComplex.cell (univ : Set X) n) = ⟨m, j⟩ := by
    by_contra h
    exact Set.disjoint_left.mp (CWComplex.disjoint_openCell_of_ne h) hi hj
  have hd : (univ : Set (Σ n, C n)).PairwiseDisjoint
      (fun ni ↦ M ni.1 ni.2 '' Metric.ball 0 1) := by
    intro ⟨n, c⟩ _ ⟨m, c'⟩ _ hne
    apply Set.disjoint_left.mpr
    intro y hy hy'
    change y ∈ M n c '' Metric.ball 0 1 at hy
    change y ∈ M m c' '' Metric.ball 0 1 at hy'
    apply hne
    rcases c with ⟨a, i⟩ | ⟨d, i, rfl⟩ <;>
      rcases c' with ⟨b, j⟩ | ⟨e, j, rfl⟩
    · rw [eo] at hy hy'
      have hij := same n m i j y.1 hy.1 hy'.1
      cases hij
      have hab : a = b := by
        have ht : (if a then (1 : unitInterval) else 0) = (if b then 1 else 0) :=
          hy.2.symm.trans hy'.2
        cases a <;> cases b
        · rfl
        · exact (zero_ne_one ht).elim
        · exact (one_ne_zero ht).elim
        · rfl
      subst b
      rfl
    · rw [eo] at hy
      rw [po e j] at hy'
      cases a
      · exact (ne_of_gt hy'.2.1 hy.2).elim
      · exact (ne_of_lt hy'.2.2 hy.2).elim
    · rw [po d i] at hy
      rw [eo] at hy'
      cases b
      · exact (ne_of_gt hy.2.1 hy'.2).elim
      · exact (ne_of_lt hy.2.2 hy'.2).elim
    · rw [po d i] at hy
      rw [po e j] at hy'
      have hij := same d e i j y.1 hy.1 hy'.1
      cases hij
      rfl
  have hf : ∀ n (c : C n), ∃ J : ∀ m, Finset (C m),
      MapsTo (M n c) (Metric.sphere 0 1)
        (⋃ (m < n) (j ∈ J m), M m j '' Metric.closedBall 0 1) := by
    intro n c
    suffices ∃ L : Finset (Σ m, C m),
        ∀ w ∈ Metric.sphere (0 : Fin n → ℝ) 1,
          ∃ q ∈ L, q.1 < n ∧ M n c w ∈ M q.1 q.2 '' Metric.closedBall 0 1 by
      obtain ⟨L, hL⟩ := this
      refine ⟨fun m ↦ L.preimage (Sigma.mk m) (by
        intro x _ y _ h; exact eq_of_heq (Sigma.mk.inj h).2), ?_⟩
      intro w hw
      obtain ⟨⟨m, j⟩, hj, hm, hy⟩ := hL w hw
      exact mem_iUnion_of_mem m (mem_iUnion_of_mem hm
        (mem_iUnion_of_mem j (mem_iUnion_of_mem (Finset.mem_preimage.mpr hj) hy)))
    rcases c with ⟨a, i⟩ | ⟨d, i, rfl⟩
    · obtain ⟨F, hF⟩ := CWComplex.mapsTo (C := (univ : Set X)) n i
      let f : (Σ m, RelCWComplex.cell (univ : Set X) m) → (Σ m, C m) :=
        fun q ↦ ⟨q.1, .inl (a, q.2)⟩
      refine ⟨((Finset.range n).sigma F).image f, ?_⟩
      intro w hw
      obtain ⟨m, hm, j, hj, hy⟩ := by
        simpa only [mem_iUnion, exists_prop] using hF hw
      refine ⟨⟨m, .inl (a, j)⟩, Finset.mem_image.mpr
        ⟨⟨m, j⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hm, hj⟩, rfl⟩, hm, ?_⟩
      rw [ec, me, hEf]
      exact ⟨hy, mem_singleton _⟩
    · obtain ⟨F, hF⟩ := CWComplex.mapsTo (C := (univ : Set X)) d i
      let f : (Σ m, RelCWComplex.cell (univ : Set X) m) → (Σ m, C m) :=
        fun q ↦ ⟨q.1 + 1, .inr ⟨q.1, ⟨q.2, rfl⟩⟩⟩
      let L : Finset (Σ m, C m) :=
        {⟨d, .inl (false, i)⟩, ⟨d, .inl (true, i)⟩} ∪
          ((Finset.range d).sigma F).image f
      refine ⟨L, ?_⟩
      intro w hw
      have hwc : w ∈ Metric.closedBall (0 : Fin (d + 1) → ℝ) 1 :=
        Metric.sphere_subset_closedBall hw
      have hwle : ‖w‖ ≤ 1 := by simpa using hwc
      have hh : (fun j : Fin d ↦ w j.castSucc) ∈ Metric.closedBall 0 1 := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
          (fun j ↦ (norm_le_pi_norm w j.castSucc).trans hwle)
      have hxy := hPf d i w hwc
      have hx : (P d i w).1 ∈ CWComplex.closedCell (C := (univ : Set X)) d i :=
        ⟨(fun j ↦ w j.castSucc), hh, hxy.1.symm⟩
      by_cases h0 : (P d i w).2 = 0
      · refine ⟨⟨d, .inl (false, i)⟩, ?_, Nat.lt_succ_self d, ?_⟩
        · simp [L]
        · rw [ec, mp d i]
          exact ⟨hx, h0⟩
      by_cases h1 : (P d i w).2 = 1
      · refine ⟨⟨d, .inl (true, i)⟩, ?_, Nat.lt_succ_self d, ?_⟩
        · simp [L]
        · rw [ec, mp d i]
          exact ⟨hx, h1⟩
      have hhs : (fun j : Fin d ↦ w j.castSucc) ∈ Metric.sphere 0 1 := by
        have ht0 : (0 : ℝ) < (P d i w).2 := by
          exact lt_of_le_of_ne (P d i w).2.property.1 (by
            intro h; apply h0; apply Subtype.ext; exact h.symm)
        have ht1 : ((P d i w).2 : ℝ) < 1 := by
          exact lt_of_le_of_ne (P d i w).2.property.2 (by
            intro h; apply h1; apply Subtype.ext; exact h)
        rw [hxy.2] at ht0 ht1
        have hlast : ‖w (Fin.last d)‖ < 1 := by
          rw [Real.norm_eq_abs, abs_lt]
          constructor <;> linarith
        have hnorm : ‖(fun j : Fin d ↦ w j.castSucc)‖ = 1 := by
          apply le_antisymm (by simpa using hh)
          by_contra! hlt
          have hall : ∀ j, ‖w j‖ < 1 := by
            intro j
            refine Fin.lastCases hlast (fun k ↦ ?_) j
            exact (norm_le_pi_norm (fun j : Fin d ↦ w j.castSucc) k).trans_lt hlt
          have hwlt : ‖w‖ < 1 := (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr hall
          have hweq : ‖w‖ = 1 := by simpa using hw
          linarith
        simpa using hnorm
      obtain ⟨m, hm, j, hj, hy⟩ := by
        simpa only [mem_iUnion, exists_prop] using hF hhs
      refine ⟨⟨m + 1, .inr ⟨m, ⟨j, rfl⟩⟩⟩, ?_, Nat.add_lt_add_right hm 1, ?_⟩
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
          ⟨⟨m, j⟩, Finset.mem_sigma.mpr ⟨Finset.mem_range.mpr hm, hj⟩, rfl⟩))
      · rw [pc m j, mp d i]
        exact ⟨hxy.1.symm ▸ hy, mem_univ _⟩
  let K : CWComplex (univ : Set (X × unitInterval)) := {
    cell := C
    map := M
    source_eq := ms
    continuousOn := by
      intro n c
      rcases c with ⟨a, i⟩ | ⟨d, i, rfl⟩
      · exact hEc n i a
      · exact hPc d i
    continuousOn_symm := by
      intro n c
      rcases c with ⟨a, i⟩ | ⟨d, i, rfl⟩
      · exact hEi n i a
      · exact hPi d i
    pairwiseDisjoint' := hd
    mapsTo' := hf
    closed' := by
      intro A _ hA
      apply cw_interval_product_closed_of_closed_cells
      intro d i
      rw [← pc d i]
      exact hA (d + 1) (.inr ⟨d, ⟨i, rfl⟩⟩)
    union' := by
      apply Set.eq_univ_of_forall
      intro y
      have hy : y ∈ (univ : Set X).prod (univ : Set unitInterval) := ⟨trivial, trivial⟩
      rw [← endpoint_prism_open_cover] at hy
      rcases hy with hy | hy
      · obtain ⟨n, i, a, hy⟩ := by simpa only [mem_iUnion] using hy
        refine mem_iUnion_of_mem n (mem_iUnion_of_mem (.inl (a, i)) ?_)
        apply Set.image_mono Metric.ball_subset_closedBall
        rwa [eo]
      · obtain ⟨d, i, hy⟩ := by simpa only [mem_iUnion] using hy
        refine mem_iUnion_of_mem (d + 1) (mem_iUnion_of_mem (.inr ⟨d, ⟨i, rfl⟩⟩) ?_)
        apply Set.image_mono Metric.ball_subset_closedBall
        rwa [po d i] }
  refine ⟨K, fun n ↦ Equiv.refl (C n), ?_, ?_⟩
  · intro d i a
    exact ⟨eo d a i, ec d a i, fun z _ ↦ hEf d i a z⟩
  · intro d i
    exact ⟨po d i, pc d i, hPf d i⟩

end HolomorphicAnosov.Topology

