import HolomorphicAnosov.Topology.AccumulatingChordMetricSkeletonCompact
import HolomorphicAnosov.Topology.AccumulatingChordTargetNoncrossing
import HolomorphicAnosov.Topology.AccumulatingChordSkeletonCompact
import HolomorphicAnosov.Topology.AccumulatingChordEndpoint
import HolomorphicAnosov.Topology.AccumulatingChordArcClassification
import HolomorphicAnosov.Topology.AccumulatingChordBoundaryImage
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Affine homeomorphism of an embedded circle and its attached chords

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
§3(E)--§4(A), printed pp.863--864, `literature/cairns-jordan-schoenflies-1951.pdf`.
The general countable-chord statement is the agent-written omission expansion
recorded in DAG node `topo.cairns_accumulating_chord_continuity_g10`.
The continuity estimate also uses the attached-skeleton paragraph of de Carvalho,
*Pruning fronts and the formation of horseshoes*, arXiv:math/9701217v1,
Definition 4.3 and Lemma 4.4, printed/PDF pp.29--30,
`literature/deCarvalho-Pruning-Fronts-arxiv1997.pdf`.

All the objects in this statement are Mathlib objects. A proper nonempty open
circle arc is expressed as an open connected proper subset of `Circle` whose
frontier consists of the specified two distinct endpoints. Both major arcs and
arcs crossing an angular cut are included. The source and target skeletons have
their actual subspace topologies in the complex plane.
-/

namespace HolomorphicAnosov

open Set

/--
The prescribed boundary homeomorphism extends affinely over every attached chord
to a homeomorphism of the entire source and target skeletons.

Source and origin: the agent-written countable-chord omission expansion of
Cairns (1951), §3(E)--§4(A), printed pp.863--864, in
`topo.cairns_accumulating_chord_continuity_g10`. De Carvalho,
arXiv:math/9701217v1, Definition 4.3 and the skeleton-continuity paragraph of
Lemma 4.4, printed/PDF pp.29--30, supplies only the null-family endpoint estimate.
Its later disk-extension argument is not used. Munkres, *Topology*, 2nd ed.,
Theorem 21.3, printed p.130, supplies the metric sequential-continuity criterion.

Natural-language proof: lift each proper open circle arc to a bounded open angular
interval of length strictly between zero and one. Its closure has precisely the
given endpoints, including for major arcs and arcs crossing a fixed angular cut.
Disjointness and normalized circle measure bound the total length of every finite
subfamily by one. Thus only finitely many arcs have length at least any fixed
positive number. Uniform continuity of the embedding and of its composition with
the given boundary homeomorphism makes both families of closed image arcs null.
The corresponding source and target straight chords are null as well, because
their diameters are the distances between their endpoints.

The source open chords avoid the embedded circle and are pairwise disjoint, so
their affine maps agree with the boundary map at all shared endpoints. The images
of the parameter arcs under the circle homeomorphism remain disjoint circle arcs.
Consequently their endpoint pairs do not alternate cyclically. Straight chords of
the unit circle therefore have disjoint interiors, lie off the circle except at
their endpoints, and can meet only at shared endpoints. Distinct source chords
cannot share both endpoints under the given open-chord disjointness hypothesis.
Each affine map is a bijection of its chord onto the corresponding target chord.
Together with the given boundary homeomorphism these pieces define a bijection
of the stated skeletons, with exactly the two displayed restriction laws.

Each skeleton is compact. Indeed it is bounded, each individual chord and the
base circle image are closed, and a convergent sequence on distinct chords lies
at distances tending to zero from their endpoints on the base. Closedness of the
base puts its limit in the base. Any remaining sequence has a subsequence on the
base or on one recurring closed chord, whose limit stays in that closed piece.

For continuity, on the base use the given boundary map and on each fixed chord
use the affine map. For a sequence x_j converging on distinct source chords,
choose a source endpoint e_j of each chord. Source nullness gives e_j tending to
the same limit x on the base. Boundary continuity gives h(e_j) tending to h(x).
The distance between the image of x_j and h(e_j) is bounded by the diameter of
the corresponding target chord, which tends to zero. Thus the images tend to
h(x). To obtain convergence of every sequence, any allegedly bad image
subsequence has a further subsequence on the base, on a fixed chord, or on
distinct chords; each case contradicts the appropriate preceding estimate.
This includes finite alternations, omitted in the printed sketch. Sequential
continuity is continuity on these metric subspaces. The continuous bijection
from the compact source skeleton to the Hausdorff target skeleton has continuous
inverse and is the required homeomorphism.

The empty and finite index types are included. The hypotheses allow shared
endpoints and arbitrarily accumulating chords, and place no orientation
restriction on the boundary homeomorphism.

Formalized proof boundary: the affine map, its agreement at all endpoints, both
restriction laws, and its surjectivity are proved below. The remaining obligation
is compactness of the source, continuity of this fixed map, and its injectivity;
the null-family and target noncrossing arguments above justify those three parts.
-/
theorem accumulatingChordContinuity
    {ι : Type*} [Countable ι]
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (h : (Set.range σ) ≃ₜ Circle)
    (arcs : ι → Set Circle) (u v : ι → Circle)
    (hOpen : ∀ i, IsOpen (arcs i))
    (hConnected : ∀ i, IsConnected (arcs i))
    (hProper : ∀ i, arcs i ≠ Set.univ)
    (hEndpoints : ∀ i, frontier (arcs i) = {u i, v i})
    (hDistinct : ∀ i, u i ≠ v i)
    (hArcsDisjoint : Pairwise fun i j ↦ Disjoint (arcs i) (arcs j))
    (hAvoid : ∀ i, Disjoint (openSegment ℝ (σ (u i)) (σ (v i))) (Set.range σ))
    (hChordsDisjoint : Pairwise fun i j ↦
      Disjoint (openSegment ℝ (σ (u i)) (σ (v i)))
        (openSegment ℝ (σ (u j)) (σ (v j)))) :
    let a : ι → ℂ := fun i ↦ (h ⟨σ (u i), ⟨u i, rfl⟩⟩ : ℂ)
    let b : ι → ℂ := fun i ↦ (h ⟨σ (v i), ⟨v i, rfl⟩⟩ : ℂ)
    let X : Set ℂ := Set.range σ ∪ ⋃ i, segment ℝ (σ (u i)) (σ (v i))
    let Y : Set ℂ := Set.range (fun p : Circle ↦ (p : ℂ)) ∪ ⋃ i, segment ℝ (a i) (b i)
    ∃ H : X ≃ₜ Y,
      (∀ (x : X) (hx : x.1 ∈ Set.range σ), (H x).1 = (h ⟨x.1, hx⟩ : ℂ)) ∧
      ∀ (i : ι) (t : ℝ) (x : X), t ∈ Set.Icc 0 1 →
        x.1 = (1 - t) • σ (u i) + t • σ (v i) →
        (H x).1 = (1 - t) • a i + t • b i := by
  classical
  by_cases hempty : IsEmpty ι
  · dsimp only
    have hX : Set.range σ ∪ ⋃ i, segment ℝ (σ (u i)) (σ (v i)) = Set.range σ := by
      apply union_eq_left.mpr
      intro x hx
      obtain ⟨i, _⟩ := mem_iUnion.mp hx
      exact (hempty.false i).elim
    have hY : Set.range (fun p : Circle ↦ (p : ℂ)) ∪
        ⋃ i, segment ℝ (h ⟨σ (u i), ⟨u i, rfl⟩⟩ : ℂ)
          (h ⟨σ (v i), ⟨v i, rfl⟩⟩ : ℂ) =
        Set.range (fun p : Circle ↦ (p : ℂ)) := by
      apply union_eq_left.mpr
      intro x hx
      obtain ⟨i, _⟩ := mem_iUnion.mp hx
      exact (hempty.false i).elim
    refine ⟨(Homeomorph.setCongr hX).trans
      ((h.trans Topology.IsEmbedding.subtypeVal.toHomeomorph).trans
        (Homeomorph.setCongr hY).symm), ?_, ?_⟩
    · intro x hx
      rfl
    · intro i
      exact (hempty.false i).elim
  · dsimp only
    let a : ι → ℂ := fun i ↦ (h ⟨σ (u i), ⟨u i, rfl⟩⟩ : ℂ)
    let b : ι → ℂ := fun i ↦ (h ⟨σ (v i), ⟨v i, rfl⟩⟩ : ℂ)
    let X : Set ℂ := Set.range σ ∪ ⋃ i, segment ℝ (σ (u i)) (σ (v i))
    let Y : Set ℂ := Set.range (fun p : Circle ↦ (p : ℂ)) ∪
      ⋃ i, segment ℝ (a i) (b i)
    let s : ι → ℝ → ℂ := fun i ↦ AffineMap.lineMap (σ (u i)) (σ (v i))
    let q : ι → ℝ → ℂ := fun i ↦ AffineMap.lineMap (a i) (b i)
    have hs_injective (i : ι) : Function.Injective (s i) :=
      AffineMap.lineMap_injective ℝ (hσ.injective.ne (hDistinct i))
    -- Off the base, a point of a closed chord lies in its open chord.
    have hopen (i : ι) {x : ℂ} (hx : x ∉ Set.range σ)
        (hxi : x ∈ segment ℝ (σ (u i)) (σ (v i))) :
        x ∈ openSegment ℝ (σ (u i)) (σ (v i)) := by
      apply mem_openSegment_of_ne_left_right _ _ hxi
      · intro heq
        exact hx ⟨u i, heq⟩
      · intro heq
        exact hx ⟨v i, heq⟩
    have hparameter (x : X) (hx : x.1 ∉ Set.range σ) :
        ∃ p : ι × Set.Icc (0 : ℝ) 1, s p.1 p.2 = x.1 := by
      obtain ⟨i, hi⟩ := mem_iUnion.mp (x.2.resolve_left hx)
      rw [segment_eq_image_lineMap] at hi
      obtain ⟨t, ht, heq⟩ := hi
      exact ⟨⟨i, ⟨t, ht⟩⟩, heq⟩
    -- Disjoint open chords and injectivity of each affine parameter give
    -- uniqueness of the chord and parameter away from the base.
    have hparameter_unique {x : ℂ} (hx : x ∉ Set.range σ)
        {i j : ι} {t r : ℝ} (ht : t ∈ Set.Icc 0 1) (hr : r ∈ Set.Icc 0 1)
        (hi : s i t = x) (hj : s j r = x) : i = j ∧ t = r := by
      have hxi : x ∈ openSegment ℝ (σ (u i)) (σ (v i)) :=
        hopen i hx (hi ▸ lineMap_mem_segment ℝ _ _ ht)
      have hxj : x ∈ openSegment ℝ (σ (u j)) (σ (v j)) :=
        hopen j hx (hj ▸ lineMap_mem_segment ℝ _ _ hr)
      have hij : i = j := by
        by_contra hne
        exact Set.disjoint_left.mp (hChordsDisjoint hne) hxi hxj
      subst j
      exact ⟨rfl, hs_injective i (hi.trans hj.symm)⟩
    -- A point of a chord on the base is necessarily one of its endpoints,
    -- so the affine prescription agrees with the prescribed boundary map.
    have hboundary (i : ι) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
        (hx : s i t ∈ Set.range σ) :
        q i t = (h ⟨s i t, hx⟩ : ℂ) := by
      have htend : t = 0 ∨ t = 1 := affine_lineMap_mem_circle_endpoint
        (σ := σ) (u := u i) (v := v i) (hAvoid i) ht hx
      rcases htend with rfl | rfl <;> simp [s, q, a, b]
    let F : X → Y := fun x ↦
      if hx : x.1 ∈ Set.range σ then
        ⟨(h ⟨x.1, hx⟩ : ℂ), Or.inl ⟨h ⟨x.1, hx⟩, rfl⟩⟩
      else
        let p := (hparameter x hx).choose
        ⟨q p.1 p.2, Or.inr (mem_iUnion.mpr
          ⟨p.1, lineMap_mem_segment ℝ _ _ p.2.property⟩)⟩
    have hFbase (x : X) (hx : x.1 ∈ Set.range σ) :
        (F x).1 = (h ⟨x.1, hx⟩ : ℂ) := by
      simp only [F, dite_eq_left hx]
    have hFchord (i : ι) (t : ℝ) (x : X) (ht : t ∈ Set.Icc 0 1)
        (hx : x.1 = s i t) : (F x).1 = q i t := by
      by_cases hb : x.1 ∈ Set.range σ
      · rw [hFbase x hb]
        calc
          _ = (h ⟨s i t, hx ▸ hb⟩ : ℂ) :=
            congrArg (fun z : Set.range σ ↦ (h z : ℂ)) (Subtype.ext hx)
          _ = q i t := (hboundary i ht (hx ▸ hb)).symm
      · let p := (hparameter x hb).choose
        have hp : s p.1 p.2 = x.1 := (hparameter x hb).choose_spec
        obtain ⟨hi, ht'⟩ := hparameter_unique hb p.2.property ht hp hx.symm
        simp only [F, dite_eq_right hb]
        change q p.1 p.2 = q i t
        rw [hi, ht']
    have hFsurj : Function.Surjective F := by
      intro y
      rcases y.2 with hy | hy
      · obtain ⟨z, hz⟩ := hy
        obtain ⟨w, hw⟩ := h.surjective z
        let x : X := ⟨w.1, Or.inl w.2⟩
        refine ⟨x, Subtype.ext ?_⟩
        rw [hFbase x w.2]
        exact (congrArg (fun z : Circle ↦ (z : ℂ)) hw).trans hz
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hy
        rw [segment_eq_image_lineMap] at hi
        obtain ⟨t, ht, heq⟩ := hi
        let x : X := ⟨s i t, Or.inr (mem_iUnion.mpr
          ⟨i, lineMap_mem_segment ℝ _ _ ht⟩)⟩
        refine ⟨x, Subtype.ext ?_⟩
        exact (hFchord i t x ht rfl).trans heq
    have htarget_distinct (i : ι) : a i ≠ b i := by
      intro hab
      apply hDistinct i
      apply hσ.injective
      exact congrArg Subtype.val (h.injective (Subtype.ext hab))
    have hq_injective (i : ι) : Function.Injective (q i) :=
      AffineMap.lineMap_injective ℝ (htarget_distinct i)
    -- Strict convexity puts every target open chord strictly inside the circle.
    have htarget_avoid (i : ι) : Disjoint (openSegment ℝ (a i) (b i))
        (Set.range (fun p : Circle ↦ (p : ℂ))) := by
      apply Set.disjoint_left.mpr
      rintro z hz ⟨w, rfl⟩
      have ha : a i ∈ Metric.closedBall (0 : ℂ) 1 := by simp [a]
      have hb : b i ∈ Metric.closedBall (0 : ℂ) 1 := by simp [b]
      have hn := openSegment_subset_ball_of_ne ha hb (htarget_distinct i) hz
      simp at hn
    have hparameter_open {x : X} (hx : x.1 ∉ Set.range σ)
        {i : ι} {t : ℝ} (ht : t ∈ Set.Icc 0 1) (heq : s i t = x.1) :
        t ∈ Set.Ioo 0 1 := by
      have hzero : t ≠ 0 := by
        intro he
        apply hx
        exact ⟨u i, by simpa [s, he] using heq⟩
      have hone : t ≠ 1 := by
        intro he
        apply hx
        exact ⟨v i, by simpa [s, he] using heq⟩
      exact ⟨lt_of_le_of_ne ht.1 (Ne.symm hzero), lt_of_le_of_ne ht.2 hone⟩
    have hFoffbase (x : X) (hx : x.1 ∉ Set.range σ) :
        (F x).1 ∉ Set.range (fun p : Circle ↦ (p : ℂ)) := by
      obtain ⟨⟨i, t⟩, heq⟩ := hparameter x hx
      rw [hFchord i t x t.2 heq.symm]
      exact fun hmem ↦ Set.disjoint_left.mp (htarget_avoid i)
        (lineMap_mem_openSegment ℝ _ _ (hparameter_open hx t.2 heq)) hmem
    have hFinj (htargetDisjoint : Pairwise fun i j ↦
        Disjoint (openSegment ℝ (a i) (b i)) (openSegment ℝ (a j) (b j))) :
        Function.Injective F := by
      intro x y hxy
      have hval := congrArg Subtype.val hxy
      by_cases hx : x.1 ∈ Set.range σ
      · have hy : y.1 ∈ Set.range σ := by
          by_contra hy
          apply hFoffbase y hy
          rw [← hval, hFbase x hx]
          exact ⟨_, rfl⟩
        rw [hFbase x hx, hFbase y hy] at hval
        exact Subtype.ext (congrArg (fun z : Set.range σ ↦ z.1)
          (h.injective (Subtype.ext hval)))
      · have hy : y.1 ∉ Set.range σ := by
          intro hy
          apply hFoffbase x hx
          rw [hval, hFbase y hy]
          exact ⟨_, rfl⟩
        obtain ⟨⟨i, t⟩, hi⟩ := hparameter x hx
        obtain ⟨⟨j, r⟩, hj⟩ := hparameter y hy
        rw [hFchord i t x t.2 hi.symm, hFchord j r y r.2 hj.symm] at hval
        have hij : i = j := by
          by_contra hne
          exact Set.disjoint_left.mp (htargetDisjoint hne)
            (lineMap_mem_openSegment ℝ _ _ (hparameter_open hx t.2 hi))
            (by
              change q i t ∈ openSegment ℝ (a j) (b j)
              rw [hval]
              exact lineMap_mem_openSegment ℝ _ _ (hparameter_open hy r.2 hj))
        subst j
        have htr := hq_injective i hval
        exact Subtype.ext (hi.symm.trans ((congrArg (s i) htr).trans hj))
    -- The newly landed arc-classification helper identifies each parameter arc
    -- with one of the two directed circle paths.  This is the interface used by
    -- the remaining null-family/cyclic-order argument below.
    have hArcClass (i : ι) :
        arcs i ⊆ Circle.path (u i) (v i) '' Ioo 0 1 ∨
          arcs i ⊆ Circle.path (v i) (u i) '' Ioo 0 1 :=
      circle_arc_subset_directed_path (arcs i) (u i) (v i)
        (hOpen i) (hConnected i) (hEndpoints i) (hDistinct i)
    have hImageArcsDisjoint :
        Pairwise (fun i j ↦ Disjoint
          ((fun p : Circle ↦ (h ⟨σ p, ⟨p, rfl⟩⟩ : Circle)) '' arcs i)
          ((fun p : Circle ↦ (h ⟨σ p, ⟨p, rfl⟩⟩ : Circle)) '' arcs j)) :=
      accumulatingChord_boundary_image_pairwise_disjoint σ hσ h arcs hArcsDisjoint
    -- Remaining geometry: the source null-family gives compactness and continuity;
    -- disjoint parameter arcs give noncrossing target chord interiors.
    have hXcompact : IsCompact X := accumulatingChordSkeleton_compact σ hσ h arcs u v
      hOpen hConnected hProper hEndpoints hDistinct hArcsDisjoint hAvoid hChordsDisjoint
    have hFcontinuous : Continuous F := by
      let τ : Circle → ℂ × ℂ := fun p ↦ (σ p, (h ⟨σ p, ⟨p, rfl⟩⟩ : ℂ))
      have hτ : Continuous τ := hσ.continuous.prodMk
        (continuous_subtype_val.comp (h.continuous.comp
          (hσ.continuous.subtype_mk (fun p ↦ ⟨p, rfl⟩))))
      let g : X → ℂ × ℂ := fun x ↦ (x.1, (F x).1)
      have hgraph : range τ ∪ ⋃ i, segment ℝ (τ (u i)) (τ (v i)) = range g := by
        apply Set.Subset.antisymm
        · intro w hw
          rcases hw with ⟨p, rfl⟩ | hw
          · let x : X := ⟨σ p, Or.inl ⟨p, rfl⟩⟩
            refine ⟨x, Prod.ext rfl ?_⟩
            exact hFbase x ⟨p, rfl⟩
          · obtain ⟨i, hi⟩ := mem_iUnion.mp hw
            rw [segment_eq_image_lineMap] at hi
            obtain ⟨t, ht, rfl⟩ := hi
            let x : X := ⟨s i t, Or.inr (mem_iUnion.mpr
              ⟨i, lineMap_mem_segment ℝ _ _ ht⟩)⟩
            refine ⟨x, Prod.ext ?_ ?_⟩
            · simp [g, x, τ, s, AffineMap.lineMap_apply_module]
            · simpa [g, τ, q, a, b, AffineMap.lineMap_apply_module] using
                hFchord i t x ht rfl
        · rintro w ⟨x, rfl⟩
          by_cases hb : x.1 ∈ range σ
          · obtain ⟨p, hp⟩ := hb
            refine Or.inl ⟨p, Prod.ext hp ?_⟩
            change (h ⟨σ p, ⟨p, rfl⟩⟩ : ℂ) = (F x).1
            rw [hFbase x ⟨p, hp⟩]
            exact congrArg (fun z : range σ ↦ (h z : ℂ)) (Subtype.ext hp)
          · obtain ⟨⟨i, t⟩, hi⟩ := hparameter x hb
            apply Or.inr
            apply mem_iUnion.mpr
            refine ⟨i, ?_⟩
            rw [segment_eq_image_lineMap]
            refine ⟨t, t.2, Prod.ext ?_ ?_⟩
            · simpa [g, τ, s, AffineMap.lineMap_apply_module] using hi
            · simpa [g, τ, q, a, b, AffineMap.lineMap_apply_module] using
                (hFchord i t x t.2 hi.symm).symm
      have hcompactGraph : IsCompact (range g) := hgraph ▸
        accumulatingChord_metric_skeleton_compact τ hτ arcs u v hOpen hConnected
          hEndpoints hDistinct hArcsDisjoint
      let : CompactSpace (range g) := isCompact_iff_compactSpace.mp hcompactGraph
      let π : range g → X := fun w ↦ ⟨w.1.1, by
        rcases w.2 with ⟨x, hx⟩
        rw [← hx]
        exact x.2⟩
      have hπ : Continuous π :=
        (continuous_fst.comp continuous_subtype_val).subtype_mk _
      have hπinj : Function.Injective π := by
        rintro ⟨w, ⟨x, rfl⟩⟩ ⟨z, ⟨y, rfl⟩⟩ heq
        change x = y at heq
        subst y
        rfl
      have hπsurj : Function.Surjective π := fun x ↦ ⟨⟨g x, mem_range_self x⟩, rfl⟩
      let e : range g ≃ X := Equiv.ofBijective π ⟨hπinj, hπsurj⟩
      let H : range g ≃ₜ X := Continuous.homeoOfEquivCompactToT2 (f := e) hπ
      have hinv (x : X) : H.symm x = ⟨g x, mem_range_self x⟩ := by
        apply H.injective
        exact H.apply_symm_apply x
      have hc : Continuous (fun x : X ↦ (F x).1) := by
        have hc := (continuous_snd.comp continuous_subtype_val).comp H.symm.continuous
        convert hc using 1
        funext x
        simp only [Function.comp_apply, hinv]
        rfl
      exact hc.subtype_mk (fun x ↦ (F x).2)
    have hremaining : IsCompact X ∧ Continuous F ∧
        Pairwise (fun i j ↦ Disjoint (openSegment ℝ (a i) (b i))
          (openSegment ℝ (a j) (b j))) := by
      exact ⟨hXcompact, hFcontinuous,
        accumulatingChord_target_noncrossing σ hσ h arcs u v hOpen hConnected hProper
          hEndpoints hDistinct hArcsDisjoint hAvoid hChordsDisjoint⟩
    let : CompactSpace X := isCompact_iff_compactSpace.mp hremaining.1
    let e : X ≃ Y := Equiv.ofBijective F ⟨hFinj hremaining.2.2, hFsurj⟩
    let H : X ≃ₜ Y := Continuous.homeoOfEquivCompactToT2 (f := e) hremaining.2.1
    refine ⟨H, hFbase, ?_⟩
    intro i t x ht hx
    change (F x).1 = (1 - t) • a i + t • b i
    simpa only [q, AffineMap.lineMap_apply_module] using
      hFchord i t x ht (hx.trans (AffineMap.lineMap_apply_module _ _ _).symm)

end HolomorphicAnosov

