import HolomorphicAnosov.Topology.ConvexBodyCharacteristicMap
import HolomorphicAnosov.Topology.StandardCoordinateSimplexBody
import HolomorphicAnosov.Topology.GeometricFaceSupportG1

namespace HolomorphicAnosov
open Set Topology _root_.Topology

/-- Characteristic partial equivalences for every face of a geometric simplicial complex,
with the original maximum-norm parameter balls, their intrinsic open-cell images,
and their exact proper-subface sphere images.

Source: Hatcher, Algebraic Topology, §2.1, pp.103–104,107 and Proposition A.2, p.521.

For a face of cardinality d+1, use its barycentric homeomorphism β from the standard
coordinate simplex Δ to its convex hull K. Its strict-coordinate locus I maps exactly
to the intrinsic interior of K. Apply the convex-body characteristic construction to Δ:
the resulting continuous map c takes all of the parameter space into Δ, its closed
ball onto Δ, its open ball onto I, and its sphere onto Δ minus I. Its partial inverse
is continuous and obeys the inverse laws on I and the open ball.

The forward face map is β composed with c, followed by the inclusion of K into the
complex carrier. The inverse at a carrier point in K is c.symm composed with β.symm;
outside K set it to zero. Restricting this inverse to the intrinsic open-cell subtype
makes it a composition of continuous functions, proving exactly the required inverse
continuity. The partial-equivalence laws follow from the two constituent inverse laws.
Surjectivity on the closed ball follows by pulling a point of K back through β; the
open image is the partial-equivalence target. The sphere image is K minus its intrinsic
interior, hence the union of nonempty proper subface hulls by geometric_face_boundary_iff.

Finally choose these maps for all degree-and-face indices. Distinct faces have disjoint
intrinsic interiors by geometric_face_interiors_disjoint; equal vertex finsets have equal
cardinalities and hence equal dependent indices. The construction is vacuous for an empty
complex, while a singleton face uses the zero-dimensional ball and empty sphere. -/
theorem simplicial_face_characteristic_maps (N : ℕ)
    (P : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin N))) :
    let E := EuclideanSpace ℝ (Fin N)
    let X := {x : E // x ∈ P.space}
    let cells := fun d : ℕ ↦ {s : Finset (EuclideanSpace ℝ (Fin N)) // s ∈ P.faces ∧ s.card = d + 1}
    ∃ χ : ∀ d, cells d → PartialEquiv (Fin d → ℝ) X,
      (∀ d s, (χ d s).source = Metric.ball 0 1) ∧
      (∀ d s, ContinuousOn (χ d s) (Metric.closedBall 0 1)) ∧
      (∀ d s, ContinuousOn (χ d s).symm (χ d s).target) ∧
      (univ : Set (Σ d, cells d)).PairwiseDisjoint
        (fun ds ↦ χ ds.1 ds.2 '' Metric.ball 0 1) ∧
      (∀ d s,
        χ d s '' Metric.closedBall 0 1 =
          {x : X | x.val ∈ convexHull ℝ (s.val : Set E)} ∧
        χ d s '' Metric.ball 0 1 =
          {x : X | x.val ∈ intrinsicInterior ℝ
            (convexHull ℝ (s.val : Set E))} ∧
        χ d s '' Metric.sphere 0 1 =
          {x : X | ∃ t : Finset E, t.Nonempty ∧ t ⊂ s.val ∧
            x.val ∈ convexHull ℝ (t : Set E)}) := by
  classical
  let E := EuclideanSpace ℝ (Fin N)
  let X := {x : E // x ∈ P.space}
  let cells := fun d : ℕ ↦ {s : Finset E // s ∈ P.faces ∧ s.card = d + 1}
  have hone (d : ℕ) (s : cells d) : ∃ χ : PartialEquiv (Fin d → ℝ) X,
      χ.source = Metric.ball 0 1 ∧
      ContinuousOn χ (Metric.closedBall 0 1) ∧
      ContinuousOn χ.symm χ.target ∧
      χ '' Metric.closedBall 0 1 = {x : X | x.val ∈ convexHull ℝ (s.val : Set E)} ∧
      χ '' Metric.ball 0 1 =
        {x : X | x.val ∈ intrinsicInterior ℝ (convexHull ℝ (s.val : Set E))} ∧
      χ '' Metric.sphere 0 1 =
        {x : X | ∃ t : Finset E, t.Nonempty ∧ t ⊂ s.val ∧
          x.val ∈ convexHull ℝ (t : Set E)} := by
    let V := Fin d → ℝ
    let Δ : Set V := {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ 1}
    let I : Set V := {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}
    let K := convexHull ℝ (s.val : Set E)
    let O : Set X := {x | x.val ∈ intrinsicInterior ℝ K}
    obtain ⟨hc, hclosed, hb, hn, hi, hf⟩ := standard_coordinate_simplex_body d
    obtain ⟨c, hcs, hct, hcc, hci, hcm, hcd, hco, hcf⟩ :=
      convex_body_characteristic_map hc hn hb hclosed
    rw [hi] at hct hco
    obtain ⟨β, hβ⟩ := geometric_face_barycentric_homeomorph N d P s.val s.property.1 s.property.2
    have hβmem (u : Δ) : (β u).val ∈ intrinsicInterior ℝ K ↔ u.val ∈ I := by
      change β u ∈ {x | x.val ∈ intrinsicInterior ℝ K} ↔ _
      rw [← hβ]
      exact β.injective.mem_set_image
    let f : V → X := fun u ↦
      ⟨(β ⟨c u, hcm u⟩).val, P.convexHull_subset_space s.property.1 (β ⟨c u, hcm u⟩).property⟩
    let g : X → V := fun x ↦ if hx : x.val ∈ K then c.symm (β.symm ⟨x.val, hx⟩).val else 0
    have hgin (x : X) (hx : x.val ∈ K) : g x = c.symm (β.symm ⟨x.val, hx⟩).val := by
      simp [g, hx]
    have hfgmem (x : X) (hx : x ∈ O) : (β.symm ⟨x.val, intrinsicInterior_subset hx⟩).val ∈ c.target := by
      rw [hct]
      apply (hβmem _).mp
      simpa only [O, Set.mem_ofPred_eq, Homeomorph.apply_symm_apply] using hx
    let e : PartialEquiv V X :=
      { toFun := f
        invFun := g
        source := Metric.ball 0 1
        target := O
        map_source' := by
          intro u hu
          apply (hβmem _).mpr
          have := c.map_source (hcs.symm ▸ hu)
          rwa [hct] at this
        map_target' := by
          intro x hx
          rw [hgin x (intrinsicInterior_subset hx), ← hcs]
          exact c.map_target (hfgmem x hx)
        left_inv' := by
          intro u hu
          rw [hgin (f u) (β ⟨c u, hcm u⟩).property]
          change c.symm (β.symm (β ⟨c u, hcm u⟩)).val = u
          simpa using c.left_inv (hcs.symm ▸ hu)
        right_inv' := by
          intro x hx
          rw [hgin x (intrinsicInterior_subset hx)]
          apply Subtype.ext
          exact congrArg (fun z : K ↦ z.val) ((congrArg β (show
            (⟨c (c.symm (β.symm ⟨x.val, intrinsicInterior_subset hx⟩).val), hcm _⟩ : Δ) =
              β.symm ⟨x.val, intrinsicInterior_subset hx⟩ from
                Subtype.ext (c.right_inv (hfgmem x hx)))).trans (β.apply_symm_apply _)) }
    have hcont : Continuous f := by
      apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (β.continuous.comp (hcc.subtype_mk hcm))
    have hinv : ContinuousOn e.symm e.target := by
      apply continuousOn_iff_continuous_domRestrict.mpr
      let j : O → K := fun x ↦ ⟨x.val.val, intrinsicInterior_subset x.property⟩
      have hj : Continuous j := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      have hg : Continuous (fun x : O ↦ c.symm (β.symm (j x)).val) :=
        hci.comp (continuous_subtype_val.comp (β.symm.continuous.comp hj))
      exact hg.congr (fun x ↦ (hgin x.val (intrinsicInterior_subset x.property)).symm)
    have hd : e '' Metric.closedBall 0 1 = {x : X | x.val ∈ K} := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact (β ⟨c u, hcm u⟩).property
      · intro hx
        have hy : (β.symm ⟨x.val, hx⟩).val ∈ Δ := (β.symm ⟨x.val, hx⟩).property
        have hy' : (β.symm ⟨x.val, hx⟩).val ∈ c '' Metric.closedBall 0 1 := by
          simpa only [hcd] using hy
        obtain ⟨u, hu, he⟩ := hy'
        refine ⟨u, hu, Subtype.ext ?_⟩
        change (β ⟨c u, hcm u⟩).val = x.val
        have he' : (⟨c u, hcm u⟩ : Δ) = β.symm ⟨x.val, hx⟩ := Subtype.ext he
        rw [he', β.apply_symm_apply]
    have ho : e '' Metric.ball 0 1 = O := e.image_source_eq_target
    have hsphere : e '' Metric.sphere 0 1 = {x : X | x.val ∈ K ∧ x ∉ O} := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        have hcu : c u ∈ frontier Δ := hcf ▸ Set.mem_image_of_mem c hu
        rw [hf] at hcu
        refine ⟨(β ⟨c u, hcm u⟩).property, ?_⟩
        intro hx
        exact hcu.2 ((hβmem _).mp hx)
      · rintro ⟨hx, hxo⟩
        have hy : (β.symm ⟨x.val, hx⟩).val ∈ frontier Δ := by
          rw [hf]
          refine ⟨(β.symm ⟨x.val, hx⟩).property, ?_⟩
          intro hy
          apply hxo
          have := (hβmem _).mpr hy
          simpa only [O, Set.mem_ofPred_eq, Homeomorph.apply_symm_apply] using this
        rw [← hcf] at hy
        obtain ⟨u, hu, he⟩ := hy
        refine ⟨u, hu, Subtype.ext ?_⟩
        change (β ⟨c u, hcm u⟩).val = x.val
        have he' : (⟨c u, hcm u⟩ : Δ) = β.symm ⟨x.val, hx⟩ := Subtype.ext he
        rw [he', β.apply_symm_apply]
    refine ⟨e, rfl, hcont.continuousOn, hinv, hd, ho, ?_⟩
    rw [hsphere]
    ext x
    constructor
    · rintro ⟨hx, hxo⟩
      exact (geometric_face_boundary_iff N P s.val s.property.1 x.val hx).mp hxo
    · rintro ⟨t, ht, hts, hxt⟩
      have hx : x.val ∈ K := convexHull_mono (show (t : Set E) ⊆ s.val from hts.le) hxt
      exact ⟨hx, (geometric_face_boundary_iff N P s.val s.property.1 x.val hx).mpr
        ⟨t, ht, hts, hxt⟩⟩
  choose χ hsource hcont hinv hclosed hopen hsphere using hone
  refine ⟨χ, hsource, hcont, hinv, ?_, fun d s ↦ ⟨hclosed d s, hopen d s, hsphere d s⟩⟩
  intro a _ b _ hab
  change Disjoint (χ a.1 a.2 '' Metric.ball 0 1) (χ b.1 b.2 '' Metric.ball 0 1)
  rw [hopen, hopen]
  apply Set.disjoint_left.mpr
  intro x hxa hxb
  have hne : a.2.val ≠ b.2.val := by
    intro he
    have hd : a.1 = b.1 := by have ha := a.2.property.2; have hb := b.2.property.2; have hh := congrArg Finset.card he; omega
    apply hab
    cases a with | mk d s =>
      cases b with | mk d' t =>
        dsimp at hd he
        subst d'
        congr
        exact Subtype.ext he
  exact Set.disjoint_left.mp
    (geometric_face_interiors_disjoint N P a.2.val b.2.val a.2.property.1 b.2.property.1 hne)
    hxa hxb

end HolomorphicAnosov
