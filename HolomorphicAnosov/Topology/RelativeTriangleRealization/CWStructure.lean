import HolomorphicAnosov.Topology.RelativeTriangleRealization.TriangleInteriorNotVertex
import HolomorphicAnosov.Topology.RelativeTriangleRealization.FiniteClassicalCWOfDisks
import HolomorphicAnosov.Topology.RelativeTriangleRealization.InteriorEmbedding
import HolomorphicAnosov.Topology.RelativeTriangleRealization.EdgeInteriorClasses
import HolomorphicAnosov.Topology.RelativeTriangleRealization.InteriorClasses
import HolomorphicAnosov.Topology.RelativeTriangleRealization.PairedTriangleQuotientT2
import HolomorphicAnosov.Topology.RelativeTriangleRealization.EdgeInteriorEmbedding
import HolomorphicAnosov.Topology.RelativeTriangleRealization.DistinguishedEdgeSubcomplex
import HolomorphicAnosov.Topology.RelativeTriangleRealization.VertexClassFinite
import HolomorphicAnosov.Topology.RelativeTriangleRealization.VertexClassStratum
import HolomorphicAnosov.Topology.RelativeTriangleRealization.TriangleStrata
import HolomorphicAnosov.Topology.RelativeTriangleRealization.FaceBoundaryVertex
import HolomorphicAnosov.Topology.RelativeTriangleRealization.FaceInteriorNotVertex
import HolomorphicAnosov.Topology.RelativeTriangleRealization.EdgeBoundaryVertexClass
import HolomorphicAnosov.Topology.CWComplex.FiniteCellAdjunction
import HolomorphicAnosov.Topology.RelativeTriangleRealization.IntervalDiskParameter
import HolomorphicAnosov.Topology.RelativeTriangleRealization.TriangleDiskParameter

noncomputable section
namespace HolomorphicAnosov.RelativeTriangleRealization

/-- The quotient of finitely many ordered triangles by an involution on their
ordered edge occurrences is a finite Hausdorff classical CW complex, with
exactly the original open triangles, the edge orbits, and the vertex classes
as cells. Every edge, together with all vertices, is a subcomplex.

Source: Hatcher, Algebraic Topology, pp.103–104 (ordered simplex quotients
and their CW structures), p.167 (paired triangles), and Appendix pp.519–522
(characteristic topology, subcomplexes, and Hausdorffness).

Proof: On vertices take the equivalence relation induced by paired endpoints.
There are finitely many vertex classes. An interior point of a triangle has
singleton class by `triangleInterior_eq_iff`; their open-embedding property is supplied by
`triangleInterior_isOpenEmbedding`. An interior edge point lies on
exactly one face, since precisely one barycentric coordinate vanishes. A
relation generator preserves its ordered edge parameter. Involutivity then
makes its class exactly that point and its paired point, as proved in
`edgeInterior_class_iff`. Vertex points remain
vertices, so these three strata are disjoint. Fixed occurrences simply yield
single edge classes; multiple fixed occurrences are allowed.

Start with the finite discrete set of vertex classes. Attach one interval for
each edge orbit, using the two endpoint classes of a representative. Paired
edges have identical quotient parameters, so this does not depend on that
representative. Attach one triangle per original label. Its boundary map is
the union of the three ordered edge maps; these agree at shared endpoints,
and finite closed-face pasting proves continuity. Interval and triangle
barycentric coordinates identify their parameters with compact convex bodies
with nonempty interiors. Radial projection from an interior point gives
homeomorphisms to the closed balls for the norm on Fin 1 → ℝ and Fin 2 → ℝ,
carrying their relative interiors to open balls. This realizes the attachments
as finite disk adjunctions. The adjunction theorem proves compactness and
Hausdorffness. Its categorical CW witness is not used as a classical witness.

The attachment quotient and paired-triangle quotient have exactly the strata
just described, hence the characteristic maps induce a bijection. Their
quotient topologies agree: triangle preimages test openness, edge preimages
follow by continuous face restriction, and zero-cell preimages are automatic.
Transport the Hausdorff property along this homeomorphism.

For the classical CW structure, use vertex classes in degree zero, edge orbits
in degree one, triangle labels in degree two, and the empty type thereafter.
Each characteristic map, parametrized by its disk homeomorphism, is injective
on its open ball and is a homeomorphism there onto its stratum. This follows
from the saturated-open quotient test for the triangle interiors and from the
corresponding graph attachment test for edge interiors. Extend the inverse
arbitrarily off that stratum to obtain a PartialEquiv whose source is exactly
the open ball. Zero-cells use the unique point of Fin 0 → ℝ. The strata prove
pairwise disjointness and coverage; boundaries lie in lower strata. The
quotient closed-set test and compact Hausdorff closed-cell images give the
closed-set axiom of `Topology.CWComplex.mkFiniteType`. That constructor retains
the chosen characteristic maps and cell types. Every cell family is finite,
and empty above degree two, so the structure is finite. The identity cell
index equivalences give the required exact map equalities on closed disks.
Finally, all vertices and the chosen edge are closed under characteristic
boundaries. The corresponding native subcomplex has precisely the union of
the zero-skeleton and the image of the chosen edge. Self-pairings, repeated
vertex identifications, and disconnected quotients are all included. -/
theorem pairedTriangles_hasCWStructure {m : ℕ}
    (pair : Occurrence m → Occurrence m) (hinv : Function.Involutive pair)
    (distinguished : Occurrence m) : HasCWStructure pair distinguished := by
  classical
  obtain ⟨disk1, hdisk1⟩ := intervalDiskParameter
  obtain ⟨disk2, hdisk2⟩ := triangleDiskParameter
  -- Descend the original edge maps to their actual occurrence classes.
  have hedge (o : Occurrence m) : edge pair o = edge pair (pair o) := by
    ext t
    exact Quotient.sound (Relation.EqvGen.rel _ _ ⟨o, t, rfl, rfl⟩)
  let edgeMap : EdgeClass pair → C(Simplex 1, Space pair) :=
    Quotient.lift (edge pair) (by
      intro a b h
      induction h with
      | rel a b hab => exact hab ▸ hedge a
      | refl a => rfl
      | symm a b hab ih => exact ih.symm
      | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc)
  have hedgeMap (o : Occurrence m) : edgeMap (edgeClass pair o) = edge pair o := rfl
  -- These are continuous characteristic maps on the exact native CW disks.
  let χ1 (o : EdgeClass pair) :
      C(Metric.closedBall (0 : Fin 1 → ℝ) 1, Space pair) :=
    (edgeMap o).comp ⟨disk1.symm, disk1.symm.continuous⟩
  let χ2 (i : Fin m) : C(Metric.closedBall (0 : Fin 2 → ℝ) 1, Space pair) :=
    (triangle pair i).comp ⟨disk2.symm, disk2.symm.continuous⟩
  have hχ1 (o : Occurrence m) (t : Simplex 1) :
      χ1 (edgeClass pair o) (disk1 t) = edge pair o t := by
    change edgeMap (edgeClass pair o) (disk1.symm (disk1 t)) = _
    rw [disk1.symm_apply_apply, hedgeMap]
  have hχ2 (i : Fin m) (t : Simplex 2) :
      χ2 i (disk2 t) = triangle pair i t := by
    change triangle pair i (disk2.symm (disk2 t)) = _
    rw [disk2.symm_apply_apply]
  let disk2Interior : interior 2 ≃ₜ Metric.ball (0 : Fin 2 → ℝ) 1 := {
    toFun := fun t ↦ ⟨(disk2 t.val).val, (hdisk2 t.val).mpr t.property⟩
    invFun := fun t ↦ ⟨disk2.symm ⟨t.val, Metric.ball_subset_closedBall t.property⟩,
      (hdisk2 _).mp (by simpa only [disk2.apply_symm_apply] using t.property)⟩
    left_inv := fun t ↦ by apply Subtype.ext; exact disk2.symm_apply_apply t.val
    right_inv := fun t ↦ Subtype.ext
      (congrArg (fun z : Metric.closedBall (0 : Fin 2 → ℝ) 1 ↦ z.val)
        (disk2.apply_symm_apply ⟨t.val, Metric.ball_subset_closedBall t.property⟩))
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hχ2embedding (i : Fin m) :
      Topology.IsEmbedding (fun t : Metric.ball (0 : Fin 2 → ℝ) 1 ↦
        χ2 i ⟨t.val, Metric.ball_subset_closedBall t.property⟩) :=
    (triangleInterior_isOpenEmbedding pair i).isEmbedding.comp
      disk2Interior.symm.isEmbedding
  have hχ1interior (a b : EdgeClass pair)
      (t s : Metric.ball (0 : Fin 1 → ℝ) 1)
      (h : χ1 a ⟨t.val, Metric.ball_subset_closedBall t.property⟩ =
        χ1 b ⟨s.val, Metric.ball_subset_closedBall s.property⟩) : a = b ∧ t = s := by
    obtain ⟨o, rfl⟩ := Quotient.mk_surjective a
    obtain ⟨p, rfl⟩ := Quotient.mk_surjective b
    let u : interior 1 :=
      ⟨disk1.symm ⟨t.val, Metric.ball_subset_closedBall t.property⟩,
        (hdisk1 _).mp (by simpa only [disk1.apply_symm_apply] using t.property)⟩
    let v : interior 1 :=
      ⟨disk1.symm ⟨s.val, Metric.ball_subset_closedBall s.property⟩,
        (hdisk1 _).mp (by simpa only [disk1.apply_symm_apply] using s.property)⟩
    have he : edge pair o u.val = edge pair p v.val := h
    obtain ⟨hop, huv⟩ := edgeInterior_eq_classes pair hinv he
    refine ⟨hop, Subtype.ext ?_⟩
    have hv := congrArg (fun z : interior 1 ↦ (disk1 z.val).val) huv
    simpa only [u, v, disk1.apply_symm_apply] using hv
  have hχ2interior (i j : Fin m)
      (t s : Metric.ball (0 : Fin 2 → ℝ) 1)
      (h : χ2 i ⟨t.val, Metric.ball_subset_closedBall t.property⟩ =
        χ2 j ⟨s.val, Metric.ball_subset_closedBall s.property⟩) : i = j ∧ t = s := by
    obtain ⟨hij, hts⟩ := (triangleInterior_eq_iff pair i j
      (disk2Interior.symm t).val (disk2Interior.symm s).val
      (disk2Interior.symm t).property).mp h
    exact ⟨hij, disk2Interior.symm.injective (Subtype.ext hts)⟩
  -- The original maps cover the quotient; parametrization keeps this exact.
  have hχ2cover : (⋃ i : Fin m, Set.range (χ2 i)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨⟨i, t⟩, rfl⟩ := Quotient.mk_surjective x
    exact Set.mem_iUnion.mpr ⟨i, ⟨disk2 t, hχ2 i t⟩⟩
  have htriangleStrata (t : Simplex 2) :
      t ∈ interior 2 ∨ (∃ j s, s ∈ interior 1 ∧ t = face j s) ∨
        ∃ j, t = Convexity.StdSimplex.single j :=
    triangle_strata t
  have hfaceBoundary (j : Fin 3) (t : Simplex 1)
      (ht : ¬ t ∈ interior 1) :
      ∃ v : Fin 3, face j t = Convexity.StdSimplex.single v :=
    face_boundary_vertex ht
  have hinteriorEdge (i : Fin m) (o : Occurrence m) (t : interior 2)
      (s : Simplex 1) : triangle pair i t.val ≠ edge pair o s :=
    triangleInterior_ne_edge pair i o t s
  have hedgeBoundary (o : Occurrence m) (t : Simplex 1)
      (ht : ¬ t ∈ interior 1) : edge pair o t ∈ VertexClass pair :=
    edge_boundary_mem_vertexClass pair o t ht
  have hT2 : T2Space (Space pair) := pairedTriangle_quotient_t2 pair hinv
  have hedgeEmbedding (o : Occurrence m) :
      Topology.IsEmbedding (fun t : interior 1 ↦ edge pair o t.val) :=
    edgeInterior_isEmbedding pair hinv o
  have hvertexFinite : (VertexClass pair).Finite := vertexClass_finite pair
  have hvertexStratum : ∀ (v : Fin m × Fin 3) (x : Fin m × Simplex 2),
      vertex pair v = Quotient.mk _ x →
        ∃ w : Fin m × Fin 3,
          x = (w.1, Convexity.StdSimplex.single w.2) :=
    vertexClass_classifies pair hinv
  have hedgeVertex (o : Occurrence m) (t : interior 1) :
      edge pair o t.val ∉ VertexClass pair := by
    intro h
    obtain ⟨v, hv⟩ := h
    have hv' : vertex pair v = Quotient.mk _ (o.1, face o.2 t.val) := by
      change Quotient.mk _ (v.1, Convexity.StdSimplex.single v.2) =
        Quotient.mk _ (o.1, face o.2 t.val) at hv
      exact hv
    obtain ⟨w, hw⟩ := vertexClass_classifies pair hinv v
      (o.1, face o.2 t.val) hv'
    exact face_interior_ne_vertex t.property w.2 (congrArg Prod.snd hw)
  let disk1Interior : interior 1 ≃ₜ Metric.ball (0 : Fin 1 → ℝ) 1 := {
    toFun := fun t ↦ ⟨(disk1 t.val).val, (hdisk1 t.val).mpr t.property⟩
    invFun := fun t ↦ ⟨disk1.symm ⟨t.val, Metric.ball_subset_closedBall t.property⟩,
      (hdisk1 _).mp (by simpa only [disk1.apply_symm_apply] using t.property)⟩
    left_inv := fun t ↦ by apply Subtype.ext; exact disk1.symm_apply_apply t.val
    right_inv := fun t ↦ Subtype.ext
      (congrArg (fun z : Metric.closedBall (0 : Fin 1 → ℝ) 1 ↦ z.val)
        (disk1.apply_symm_apply ⟨t.val, Metric.ball_subset_closedBall t.property⟩))
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hχ1embedding (o : EdgeClass pair) :
      Topology.IsEmbedding (fun t : Metric.ball (0 : Fin 1 → ℝ) 1 ↦
        χ1 o ⟨t.val, Metric.ball_subset_closedBall t.property⟩) := by
    obtain ⟨o, rfl⟩ := Quotient.mk_surjective o
    exact (hedgeEmbedding o).comp disk1Interior.symm.isEmbedding
  let I : ℕ → Type := fun n ↦ match n with
    | 0 => VertexClass pair
    | 1 => EdgeClass pair
    | 2 => Fin m
    | _ + 3 => PEmpty
  let χ : (n : ℕ) → I n →
      C(Metric.closedBall (0 : Fin n → ℝ) 1, Space pair) := fun n ↦
    match n with
    | 0 => fun v ↦ ContinuousMap.const _ v.val
    | 1 => χ1
    | 2 => χ2
    | _ + 3 => fun v ↦ v.elim
  have hfinite (n : ℕ) : Finite (I n) := by
    rcases n with _ | n
    · exact hvertexFinite
    rcases n with _ | n
    · change Finite (EdgeClass pair)
      infer_instance
    rcases n with _ | n
    · exact inferInstanceAs (Finite (Fin m))
    · exact inferInstanceAs (Finite PEmpty)
  have heventual : ∀ᶠ n in Filter.atTop, IsEmpty (I n) := by
    filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    rcases n with _ | (_ | (_ | n)) <;> try omega
    exact inferInstanceAs (IsEmpty PEmpty)
  have hemb (n : ℕ) (i : I n) :
      Topology.IsEmbedding (fun t : Metric.ball (0 : Fin n → ℝ) 1 ↦
        χ n i ⟨t.val, Metric.ball_subset_closedBall t.property⟩) := by
    rcases n with _ | (_ | (_ | n))
    · exact Topology.IsEmbedding.of_subsingleton _
    · exact hχ1embedding i
    · exact hχ2embedding i
    · exact i.elim
  have hcover : (⋃ (n : ℕ) (i : I n), Set.range (χ n i)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i : Fin m, Set.range (χ2 i) := by rw [hχ2cover]; trivial
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨2, Set.mem_iUnion.mpr ⟨i, hi⟩⟩
  have hboundary (n : ℕ) (i : I n)
      (t : Metric.sphere (0 : Fin n → ℝ) 1) :
      χ n i ⟨t.val, Metric.sphere_subset_closedBall t.property⟩ ∈
        ⋃ (k < n) (j : I k), Set.range (χ k j) := by
    rcases n with _ | (_ | (_ | n))
    · exact isEmptyElim t
    · obtain ⟨o, rfl⟩ := Quotient.mk_surjective i
      let u := disk1.symm ⟨t.val, Metric.sphere_subset_closedBall t.property⟩
      have hu : u ∉ interior 1 := by
        intro hu
        have hb := (hdisk1 u).mpr hu
        have he : (disk1 u).val = t.val :=
          congrArg Subtype.val (disk1.apply_symm_apply _)
        rw [he] at hb
        exact Set.disjoint_left.mp Metric.sphere_disjoint_ball t.property hb
      have hv := hedgeBoundary o u hu
      refine Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by omega,
        Set.mem_iUnion.mpr ⟨⟨edge pair o u, hv⟩, ?_⟩⟩⟩
      exact ⟨⟨0, by simp⟩, rfl⟩
    · let u := disk2.symm ⟨t.val, Metric.sphere_subset_closedBall t.property⟩
      have hu : u ∉ interior 2 := by
        intro hu
        have hb := (hdisk2 u).mpr hu
        have he : (disk2 u).val = t.val :=
          congrArg Subtype.val (disk2.apply_symm_apply _)
        rw [he] at hb
        exact Set.disjoint_left.mp Metric.sphere_disjoint_ball t.property hb
      rcases htriangleStrata u with hi | ⟨j, v, hv, he⟩ | ⟨j, he⟩
      · exact (hu hi).elim
      · refine Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨by omega,
          Set.mem_iUnion.mpr ⟨edgeClass pair (i, j), ?_⟩⟩⟩
        refine ⟨disk1 v, ?_⟩
        rw [show χ 1 (edgeClass pair (i, j)) (disk1 v) = edge pair (i, j) v
          from hχ1 (i,j) v]
        change triangle pair i (face j v) = triangle pair i u
        rw [he]
      · refine Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by omega,
          Set.mem_iUnion.mpr ⟨⟨vertex pair (i,j), ⟨(i,j), rfl⟩⟩, ?_⟩⟩⟩
        refine ⟨⟨0, by simp⟩, ?_⟩
        change vertex pair (i,j) = triangle pair i u
        rw [he]
        rfl
    · exact i.elim
  have hd1 (t : Metric.ball (0 : Fin 1 → ℝ) 1) :
      disk1 (disk1Interior.symm t).val = ⟨t.val, Metric.ball_subset_closedBall t.property⟩ := by
    apply Subtype.ext
    change (disk1 (disk1Interior.symm t)).val = t.val
    exact congrArg Subtype.val (disk1Interior.right_inv t)
  have hd2 (t : Metric.ball (0 : Fin 2 → ℝ) 1) :
      disk2 (disk2Interior.symm t).val = ⟨t.val, Metric.ball_subset_closedBall t.property⟩ := by
    apply Subtype.ext
    change (disk2 (disk2Interior.symm t)).val = t.val
    exact congrArg Subtype.val (disk2Interior.right_inv t)
  have hχ1ball (o : Occurrence m) (t : Metric.ball (0 : Fin 1 → ℝ) 1) :
      χ1 (edgeClass pair o) ⟨t.val, Metric.ball_subset_closedBall t.property⟩ = edge pair o (disk1Interior.symm t).val := by
    rw [← hd1 t]
    exact hχ1 o _
  have hχ2ball (i : Fin m) (t : Metric.ball (0 : Fin 2 → ℝ) 1) :
      χ2 i ⟨t.val, Metric.ball_subset_closedBall t.property⟩ = triangle pair i (disk2Interior.symm t).val := by
    rw [← hd2 t]
    exact hχ2 i _
  have htriangleVertex (i : Fin m) (t : interior 2) :
      triangle pair i t.val ∉ VertexClass pair :=
    triangleInterior_ne_vertex pair hinv i t
  have hdisjoint : (Set.univ : Set (Σ n, I n)).PairwiseDisjoint
      (fun c ↦ Set.range (fun t : Metric.ball (0 : Fin c.1 → ℝ) 1 ↦
        χ c.1 c.2 ⟨t.val, Metric.ball_subset_closedBall t.property⟩)) := by
    rintro ⟨n, i⟩ - ⟨k, j⟩ - hne
    change Disjoint (Set.range (fun t : Metric.ball (0 : Fin n → ℝ) 1 ↦
      χ n i ⟨t.val, Metric.ball_subset_closedBall t.property⟩))
      (Set.range (fun t : Metric.ball (0 : Fin k → ℝ) 1 ↦
        χ k j ⟨t.val, Metric.ball_subset_closedBall t.property⟩))
    rw [Set.disjoint_left]
    intro x hx hy
    simp only [Set.mem_range] at hx hy
    rcases n with _ | (_ | (_ | n))
    · rcases k with _ | (_ | (_ | k))
      · have hix : (i.val : Space pair) = x := by
          rcases hx with ⟨t, ht⟩
          simpa [χ] using ht
        have hjx : (j.val : Space pair) = x := by
          rcases hy with ⟨t, ht⟩
          simpa [χ] using ht
        have hij : i = j := Subtype.ext (hix.trans hjx.symm)
        exact hne (by cases hij; rfl)
      · change EdgeClass pair at j
        obtain ⟨o, rfl⟩ := Quotient.mk_surjective j
        have hix : (i.val : Space pair) = x := by
          rcases hx with ⟨t, ht⟩
          simpa [χ] using ht
        rcases hy with ⟨t, ht⟩
        let u := disk1Interior.symm t
        obtain ⟨v, hv⟩ := i.property
        have htx : x = edge pair o u.val := by
          exact ht.symm.trans (hχ1ball o t)
        have hxe : vertex pair v = edge pair o u.val := hv.trans (hix.trans htx)
        exact hedgeVertex o u ⟨v, hxe⟩
      · rcases hx with ⟨u, hu⟩
        rcases hy with ⟨t, ht⟩
        have hix : (i.val : Space pair) = x := hu
        have htri : triangle pair j (disk2Interior.symm t).val = x :=
          (hχ2ball j t).symm.trans ht
        exact htriangleVertex j _ ((hix.trans htri.symm) ▸ i.property)
      · exact j.elim
    · change EdgeClass pair at i
      rcases k with _ | k
      · change VertexClass pair at j
        obtain ⟨o, rfl⟩ := Quotient.mk_surjective i
        rcases hx with ⟨t, ht⟩
        rcases hy with ⟨u, hu⟩
        let z := disk1Interior.symm t
        obtain ⟨v, hv⟩ := j.property
        have htx : edge pair o z.val = (j.val : Space pair) := by
          exact (hχ1ball o t).trans (ht.trans hu.symm)
        exact hedgeVertex o z ⟨v, hv.trans htx.symm⟩
      · rcases k with _ | k
        · change EdgeClass pair at j
          rcases hx with ⟨t, ht⟩
          rcases hy with ⟨u, hu⟩
          have heq : (χ1 i) ⟨t.val, Metric.ball_subset_closedBall t.property⟩ =
              (χ1 j) ⟨u.val, Metric.ball_subset_closedBall u.property⟩ := ht.trans hu.symm
          have hij := (hχ1interior i j t u heq).1
          exact hne (by cases hij; rfl)
        · rcases k with _ | k
          · change Fin m at j
            obtain ⟨o, rfl⟩ := Quotient.mk_surjective i
            rcases hx with ⟨t, ht⟩
            rcases hy with ⟨u, hu⟩
            let z := disk1Interior.symm t
            let q := disk2Interior.symm u
            have heq : edge pair o z.val = triangle pair j q.val := by
              exact (hχ1ball o t).trans ((ht.trans hu.symm).trans (hχ2ball j u).symm)
            exact (hinteriorEdge j o q z) heq.symm
          · exact j.elim
    · rcases k with _ | (_ | (_ | k))
      · rcases hx with ⟨t, ht⟩
        rcases hy with ⟨u, hu⟩
        have hjx : (j.val : Space pair) = x := hu
        have htri : triangle pair i (disk2Interior.symm t).val = x :=
          (hχ2ball i t).symm.trans ht
        exact htriangleVertex i _ ((hjx.trans htri.symm) ▸ j.property)
      · obtain ⟨o, rfl⟩ := Quotient.mk_surjective j
        rcases hx with ⟨t, ht⟩
        rcases hy with ⟨u, hu⟩
        exact hinteriorEdge i o (disk2Interior.symm t) (disk1Interior.symm u).val
          ((hχ2ball i t).symm.trans ((ht.trans hu.symm).trans (hχ1ball o u)))
      · rcases hx with ⟨t, ht⟩
        rcases hy with ⟨u, hu⟩
        have hij := (hχ2interior i j t u (ht.trans hu.symm)).1
        exact hne (by cases hij; rfl)
      · exact j.elim
    · exact i.elim
  obtain ⟨cw, hcwfinite, indices, hmaps⟩ :=
    HolomorphicAnosov.finiteClassicalCWOfDisks I hfinite heventual χ hemb hdisjoint hboundary hcover
  let := cw
  have hcellFinite : ∀ n, Finite (Topology.RelCWComplex.cell (Set.univ : Set (Space pair)) n) := by
    intro n
    exact Finite.of_injective (indices n).symm (indices n).symm.injective
  have hcellEmpty : ∀ n, 2 < n → IsEmpty (Topology.RelCWComplex.cell (Set.univ : Set (Space pair)) n) := by
    intro n hn
    have hn3 : 3 ≤ n := by omega
    obtain ⟨q, rfl⟩ : ∃ q, n = q + 3 := by
      exact ⟨n - 3, by omega⟩
    constructor
    intro c
    have hc' : PEmpty := by
      exact ((indices (q + 3)).symm).toFun c
    exact hc'.elim
  have hindex2 : Fin m ≃ Topology.RelCWComplex.cell (Set.univ : Set (Space pair)) 2 := by
    exact indices 2
  have hindex1 : EdgeClass pair ≃ Topology.RelCWComplex.cell (Set.univ : Set (Space pair)) 1 := by
    exact indices 1
  have hindex0 : VertexClass pair ≃ Topology.RelCWComplex.cell (Set.univ : Set (Space pair)) 0 := by
    exact indices 0
  have hmap2 : ∀ (i : Fin m) (t : Simplex 2),
      triangle pair i t = Topology.RelCWComplex.map 2 ((indices 2) i) (disk2 t).val := by
    intro i t
    exact (hχ2 i t).symm.trans (hmaps 2 i (disk2 t)).symm
  have hmap1 : ∀ (o : Occurrence m) (t : Simplex 1),
      edge pair o t = Topology.RelCWComplex.map 1 ((indices 1) (edgeClass pair o)) (disk1 t).val := by
    intro o t
    exact (hχ1 o t).symm.trans (hmaps 1 (edgeClass pair o) (disk1 t)).symm
  have hopen0 : ∀ v : VertexClass pair,
      Topology.RelCWComplex.openCell 0 ((indices 0) v) = ({v.val} : Set (Space pair)) := by
    intro v
    rw [Topology.RelCWComplex.openCell_zero_eq_singleton]
    congr 1
    simpa [χ] using congrArg id (hmaps 0 v ⟨0, by simp⟩)
  refine ⟨hT2, cw, hcwfinite, hcellEmpty, disk1, disk2, hdisk1, hdisk2,
    indices 2, indices 1, indices 0, hmap2, hmap1, hopen0, ?_⟩
  let E : Set (Space pair) :=
    (Topology.RelCWComplex.skeleton (Set.univ : Set (Space pair)) 0 : Set (Space pair)) ∪
      Set.range (edge pair distinguished)
  let I : ∀ n : ℕ, Set (Topology.RelCWComplex.cell (Set.univ : Set (Space pair)) n)
    | 0 => Set.univ
    | 1 => {indices 1 (edgeClass pair distinguished)}
    | _ => ∅
  have hclosed : ∀ (n : ℕ) (i : I n),
      Topology.RelCWComplex.closedCell n i.1 ⊆ E := by
    intro n i
    cases n with
    | zero =>
      exact (Topology.RelCWComplex.closedCell_subset_skeleton 0 i.1).trans
        (Set.subset_union_left)
    | succ n =>
      cases n with
      | zero =>
        have hi : i.1 = indices 1 (edgeClass pair distinguished) :=
          Set.mem_singleton_iff.mp (by exact i.2)
        rw [hi]
        rw [← Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell]
        intro x hx
        rcases hx with hx | hx
        · exact Set.mem_union_left _
            ((Topology.RelCWComplex.cellFrontier_subset_skeleton 0 _ ) hx)
        · rcases hx with ⟨z, hz, hzx⟩
          change z ∈ Metric.ball (0 : Fin 1 → ℝ) 1 at hz
          let t : Simplex 1 := disk1.symm ⟨z, Metric.ball_subset_closedBall hz⟩
          have ht : t ∈ interior 1 := (hdisk1 t).mp (by
            simpa [t] using hz)
          refine Set.mem_union_right _ ⟨t, ?_⟩
          have hzt : (disk1 t).val = z := by
            exact congrArg Subtype.val (disk1.apply_symm_apply ⟨z, Metric.ball_subset_closedBall hz⟩)
          have hmapeq :
              (Topology.RelCWComplex.map 1 (indices 1 (edgeClass pair distinguished)))
                  (disk1 t).val =
                (Topology.RelCWComplex.map 1 (indices 1 (edgeClass pair distinguished))) z := by
            rw [hzt]
          exact (hmap1 distinguished t).trans (hmapeq.trans hzx)
      | succ n =>
          exact False.elim (Set.notMem_empty i.1 (by exact i.2))
  have hunion : (⋃ (n : ℕ) (j : I n),
      Topology.RelCWComplex.openCell n j.1) = E := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hx⟩ := Set.mem_iUnion.mp hx
      cases n with
      | zero =>
          exact Set.mem_union_left _
            ((Topology.RelCWComplex.openCell_subset_skeleton 0 j.1) hx)
      | succ n =>
          cases n with
          | zero =>
              have hj : j.1 = indices 1 (edgeClass pair distinguished) :=
                Set.mem_singleton_iff.mp (by exact j.2)
              rw [hj] at hx
              obtain ⟨z, hz, hzx⟩ := hx
              change z ∈ Metric.ball (0 : Fin 1 → ℝ) 1 at hz
              let t : Simplex 1 := disk1.symm ⟨z, Metric.ball_subset_closedBall hz⟩
              refine Set.mem_union_right _ ⟨t, ?_⟩
              have hzt : (disk1 t).val = z := by
                exact congrArg Subtype.val (disk1.apply_symm_apply ⟨z, Metric.ball_subset_closedBall hz⟩)
              have hmapeq :
                  (Topology.RelCWComplex.map 1 (indices 1 (edgeClass pair distinguished)))
                      (disk1 t).val =
                    (Topology.RelCWComplex.map 1 (indices 1 (edgeClass pair distinguished))) z := by
                rw [hzt]
              exact (hmap1 distinguished t).trans (hmapeq.trans hzx)
          | succ n => exact False.elim (Set.notMem_empty j.1 (by exact j.2))
    · intro hx
      rcases hx with hx | ⟨t, rfl⟩
      · obtain ⟨n, hn, j, hj⟩ := Topology.CWComplex.mem_skeleton_iff.mp hx
        have hn0 : n = 0 := Nat.eq_zero_of_le_zero (WithTop.coe_le_zero.mp hn)
        subst n
        refine Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨⟨j, Set.mem_univ _⟩, ?_⟩⟩
        simpa only [Topology.RelCWComplex.openCell_zero_eq_singleton] using hj
      · by_cases ht : t ∈ interior 1
        · let z : Metric.ball (0 : Fin 1 → ℝ) 1 :=
            ⟨(disk1 t).val, (hdisk1 t).mpr ht⟩
          refine Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr
            ⟨⟨indices 1 (edgeClass pair distinguished), by simp [I]⟩, ?_⟩⟩
          refine ⟨z, (hdisk1 t).mpr ht, ?_⟩
          have hzt : (disk1 t).val = z.val := rfl
          exact (congrArg _ hzt).symm.trans (hmap1 distinguished t).symm
        · have hv : edge pair distinguished t ∈ VertexClass pair :=
            hedgeBoundary distinguished t ht
          obtain ⟨v, hv⟩ := hv
          let vv : VertexClass pair := ⟨vertex pair v, ⟨v, rfl⟩⟩
          rw [← hv]
          refine Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr
            ⟨⟨indices 0 vv, by simp [I]⟩, ?_⟩⟩
          rw [hopen0]
          rfl
  obtain ⟨B, hB⟩ := distinguishedEdgeSubcomplex_of_closedCells E I hclosed hunion
  exact ⟨B, hB⟩


end HolomorphicAnosov.RelativeTriangleRealization
