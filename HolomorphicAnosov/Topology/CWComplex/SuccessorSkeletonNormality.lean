import HolomorphicAnosov.Topology.NormalClosedAdjunction
import HolomorphicAnosov.Topology.NormalSigma
import HolomorphicAnosov.Topology.CWComplex.CompactGenerationSubspaces
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.Separation.Regular
import HolomorphicAnosov.Topology.CWComplex.GlueTwoClosed
import HolomorphicAnosov.Topology.CWComplex.RadialCharacteristicTarget
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Successor-skeleton normality interface

This module isolates the source-level interface omitted by the native classical CW API:
the ordinary adjunction of a predecessor skeleton with the coproduct of the next closed
characteristic disks.  The quotient comparison and disk-prism construction are kept as one
named theorem so that the parent normality induction has no hidden quotient assumption.

Source: Fritsch--Piccinini, *Cellular Structures in Topology*, Proposition 1.2.1,
pp.22--23 and Appendix A.4.8(iv), pp.260--261; the disk-prism retraction is §1.0,
pp.7--8.  The current Mathlib `RelCWComplex` interface does not expose this adjunction
quotient or its native-topology comparison.

DAG node: `topo.cw_successor_skeleton_adjunction_data_g7`.
-/

namespace HolomorphicAnosov.Topology.CWComplex

open Set _root_.Topology

universe u

abbrev predecessorSkeleton (X : Type u) [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :=
  ↥(_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X)

abbrev successorSkeleton (X : Type u) [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :=
  ↥(_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) ((n + 1 : ℕ) : ℕ∞) : Set X)

abbrev successorDisk (X : Type u) [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :=
  Σ _i : _root_.Topology.RelCWComplex.cell (Set.univ : Set X) (n + 1),
    Metric.closedBall (0 : Fin (n + 1) → ℝ) 1

def successorBoundarySet (X : Type u) [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) : Set (successorDisk X n) :=
  {z | dist (z.2 : Fin (n + 1) → ℝ) 0 = 1}

abbrev successorBoundary (X : Type u) [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :=
  ↥(successorBoundarySet X n)

def successorAttachmentRelation {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (α : successorBoundary X n → predecessorSkeleton X n) :
    (predecessorSkeleton X n ⊕ successorDisk X n) →
      (predecessorSkeleton X n ⊕ successorDisk X n) → Prop :=
  fun p q ↦ ∃ d : successorBoundary X n,
    p = Sum.inr (d : successorDisk X n) ∧ q = Sum.inl (α d)

/-- Data identifying the native successor skeleton with the ordinary closed adjunction.

The fields are exactly the two omitted source lemmas: the quotient comparison with the
native successor topology, and the closed-cofibration (disk-prism) extension property for
the coproduct of characteristic disks.  The normality and compact-generation fields record
the hypotheses needed by `normal_closed_adjunction`; they are proved from the metric disk
and coproduct constructions in the source argument.  This is an interface structure, not
a replacement topology or a quotient definition of the native skeleton.
-/
structure SuccessorSkeletonAdjunctionData {X : Type u} [TopologicalSpace X]
    [T2Space X] [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) where
  alpha : successorBoundary X n → predecessorSkeleton X n
  alpha_continuous : Continuous alpha
  quotient_homeomorph :
    Quot (successorAttachmentRelation n alpha) ≃ₜ successorSkeleton X n
  predecessor_normal : NormalSpace (predecessorSkeleton X n)
  predecessor_compactly_generated : CompactlyGeneratedSpace (predecessorSkeleton X n)
  disk_normal : NormalSpace (successorDisk X n)
  disk_compactly_generated : CompactlyGeneratedSpace (successorDisk X n)
  boundary_closed : IsClosed (successorBoundarySet X n)
  cofibration : ∀ (T : Type u) [TopologicalSpace T]
      (g : successorDisk X n → T)
      (h : unitInterval × successorBoundary X n → T),
      Continuous g → Continuous h →
      (∀ d : successorBoundary X n, h (0, d) = g d) →
      ∃ H : unitInterval × successorDisk X n → T,
        Continuous H ∧ (∀ y, H (0, y) = g y) ∧
          ∀ (t : unitInterval) (d : successorBoundary X n), H (t, d) = h (t, d)

/-! The source proof of the following named obligations is the direct successor-stage
argument from FP §1.0, Proposition 1.2.1 and Appendix A.4.8(iv): construct the native
characteristic-map attaching map, prove continuity on the disk coproduct, use the explicit
radial disk-prism retraction summandwise, and identify the resulting ordinary quotient
topology with the native skeleton final topology.  Those quotient and prism details are not
exported by Mathlib, so each remains a named source obligation rather than being hidden in
the parent induction. -/

/-- The native characteristic maps induce a continuous attaching map on the boundary coproduct.

Source: Fritsch--Piccinini, Proposition 1.2.1, pp.22--23, with continuity on a coproduct
checked by the characteristic-map continuity and domain-restriction lemmas in Mathlib.
DAG node: `topo.cw_successor_attachment_map_g7`.
-/
theorem successor_skeleton_attachment_map
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    ∃ alpha : successorBoundary X n → predecessorSkeleton X n, Continuous alpha := by
  let f : successorDisk X n → X := fun z ↦
    (_root_.Topology.RelCWComplex.map (C := (Set.univ : Set X)) (n + 1) z.1) z.2
  have hf : Continuous f := by
    apply continuous_sigma
    intro i
    convert (_root_.Topology.RelCWComplex.continuousOn (C := (Set.univ : Set X))
      (n + 1) i).domRestrict using 1
    rfl
  have hf_boundary : Continuous (fun d : successorBoundary X n => f d) :=
    hf.comp continuous_subtype_val
  have hmem : ∀ d : successorBoundary X n,
      f d ∈ (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X)
        (n : ℕ∞) : Set X) := by
    intro d
    apply (_root_.Topology.RelCWComplex.cellFrontier_subset_skeleton
      (C := (Set.univ : Set X)) n d.1.1)
    refine ⟨d.1.2, Metric.mem_sphere.mpr d.2, ?_⟩
    rfl
  let alpha : successorBoundary X n → predecessorSkeleton X n :=
    fun d ↦ ⟨f d, hmem d⟩
  refine ⟨alpha, ?_⟩
  simpa [alpha] using hf_boundary.subtype_mk (fun d ↦ hmem d)

/-- The predecessor skeleton inherits compact generation from the native CW structure.

Source: Fritsch--Piccinini, Appendix A.4.8(iv), pp.260--261, and the compact-generation
part of the classical CW final-topology argument.  DAG node:
`topo.cw_successor_predecessor_compactly_generated_g7`.
-/
theorem successor_skeleton_predecessor_compactly_generated
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    CompactlyGeneratedSpace (predecessorSkeleton X n) := by
  exact (compactlyGeneratedSpace_of_cw_subspaces (X := X)).2.2 n

/-- The coproduct of next closed characteristic disks is normal.

Source: Fritsch--Piccinini, Appendix A.4.8(iv), together with the metric closed-disk
normality and normal Sigma coproduct arguments.  DAG node:
`topo.cw_successor_disk_normal_g7`.
-/
theorem successor_skeleton_disk_normal
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    NormalSpace (successorDisk X n) := by
  exact normalSpace_sigma

/-- The coproduct of next closed characteristic disks is compactly generated.

Source: Fritsch--Piccinini, Appendix A.4.8(iv), using compact generation of metric disk
summands and the Sigma coproduct criterion.  DAG node:
`topo.cw_successor_disk_compactly_generated_g7`.
-/
theorem successor_skeleton_disk_compactly_generated
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    CompactlyGeneratedSpace (successorDisk X n) := by
  exact inferInstance

/-- The boundary coproduct is closed in the coproduct of closed disks.

Source: Fritsch--Piccinini, Appendix A.4.8(iv), with the metric sphere-closedness lemma
applied summandwise.  DAG node: `topo.cw_successor_boundary_closed_g7`.
-/
theorem successor_skeleton_boundary_closed
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    IsClosed (successorBoundarySet X n) := by
  change IsClosed {z : successorDisk X n | dist (z.2 : Fin (n + 1) → ℝ) 0 = 1}
  have hproj : Continuous (fun z : successorDisk X n => (z.2 : Fin (n + 1) → ℝ)) := by
    exact continuous_sigma (fun _ => continuous_subtype_val)
  have hdist : Continuous (fun z : successorDisk X n =>
      dist (z.2 : Fin (n + 1) → ℝ) 0) :=
    continuous_dist.comp (hproj.prodMk continuous_const)
  exact isClosed_singleton.preimage hdist

/-- The boundary inclusion has the disk-prism homotopy-extension property.

Source: Fritsch--Piccinini, §1.0, pp.7--8: conjugate the radial disk-prism retraction by
the characteristic disk homeomorphisms and take its Sigma coproduct.  DAG node:
`topo.cw_successor_disk_cofibration_g7`.
-/
theorem successor_skeleton_disk_cofibration
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    ∀ (T : Type u) [TopologicalSpace T]
      (g : successorDisk X n → T)
      (h : unitInterval × successorBoundary X n → T),
      Continuous g → Continuous h →
      (∀ d : successorBoundary X n, h (0, d) = g d) →
      ∃ H : unitInterval × successorDisk X n → T,
        Continuous H ∧ (∀ y, H (0, y) = g y) ∧
          ∀ (t : unitInterval) (d : successorBoundary X n), H (t, d) = h (t, d) := by
  intro T _ g h hg hh h0
  let C : Set (unitInterval × successorDisk X n) :=
    {p | p.1 = 0 ∨ p.2 ∈ successorBoundarySet X n}
  let rraw : (unitInterval × successorDisk X n) → (unitInterval × successorDisk X n) := fun p =>
    let q := HolomorphicAnosov.cw_prism_radial (p.2.2, p.1)
    (q.2, ⟨p.2.1, q.1⟩)
  have hrraw : Continuous rraw := by
    let qmap : (unitInterval × successorDisk X n) →
        (Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 × unitInterval) := fun p => (p.2.2, p.1)
    have hqmap : Continuous qmap := by
      change Continuous (fun p : unitInterval × successorDisk X n => (p.2.2, p.1))
      have hsnd : Continuous (fun z : successorDisk X n => z.2) := by
        apply continuous_sigma
        intro i
        exact continuous_id
      exact (hsnd.comp continuous_snd).prodMk continuous_fst
    let rq := HolomorphicAnosov.cw_prism_radial (E := Fin (n + 1) → ℝ)
    have hrq : Continuous (rq ∘ qmap) := continuous_cw_prism_radial.comp hqmap
    have htime : Continuous (fun p : unitInterval × successorDisk X n => (rq (qmap p)).2) :=
      continuous_snd.comp hrq
    have hdisk : Continuous (fun p : unitInterval × successorDisk X n =>
        (⟨p.2.1, (rq (qmap p)).1⟩ : successorDisk X n)) := by
      let e : (Σ i : _root_.Topology.RelCWComplex.cell (Set.univ : Set X) (n+1),
          Metric.closedBall (0 : Fin (n+1) → ℝ) 1) × unitInterval ≃ₜ
          Σ i : _root_.Topology.RelCWComplex.cell (Set.univ : Set X) (n+1),
            Metric.closedBall (0 : Fin (n+1) → ℝ) 1 × unitInterval :=
        Homeomorph.sigmaProdDistrib
      have hpre : Continuous (fun p : unitInterval × successorDisk X n => e (p.2, p.1)) :=
        e.continuous.comp (continuous_snd.prodMk continuous_fst)
      have hper : Continuous (fun q : (Σ i : _root_.Topology.RelCWComplex.cell (Set.univ : Set X) (n+1),
            Metric.closedBall (0 : Fin (n+1) → ℝ) 1 × unitInterval) =>
            (⟨q.1, (HolomorphicAnosov.cw_prism_radial q.2).1⟩ : successorDisk X n)) := by
        apply continuous_sigma
        intro i
        exact continuous_sigmaMk.comp
          (continuous_fst.comp (continuous_cw_prism_radial.comp
            (continuous_fst.prodMk continuous_snd)))
      exact hper.comp hpre
    exact htime.prodMk hdisk
  have hrc : ∀ p : unitInterval × successorDisk X n, rraw p ∈ C := by
    intro p
    rcases HolomorphicAnosov.cw_prism_radial_in_bottom_or_side (p.2.2, p.1) with hb | hs
    · exact Or.inl hb
    · exact Or.inr (by simpa [rraw, successorBoundarySet, dist_zero_right] using hs)
  let r : C(unitInterval × successorDisk X n, C) :=
    ⟨fun p => ⟨rraw p, hrc p⟩, hrraw.subtype_mk _⟩
  let bottom : Set C := {p | p.val.1 = 0}
  let side : Set C := {p | p.val.2 ∈ successorBoundarySet X n}
  have hbottom : IsClosed bottom := isClosed_singleton.preimage
    (continuous_fst.comp continuous_subtype_val)
  have hside : IsClosed side := by
    exact (successor_skeleton_boundary_closed (X := X) n).preimage
      (continuous_snd.comp continuous_subtype_val)
  have hcover : ∀ z : C, z ∈ bottom ∨ z ∈ side := by
    intro z
    have hz := z.property
    change z.val.1 = 0 ∨ z.val.2 ∈ successorBoundarySet X n at hz
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr hz
  let f : C(bottom, T) := ⟨fun p => g p.val.val.2,
    hg.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))⟩
  let kside : C(side, T) := by
    have hpBraw : Continuous (fun p : side => p.val.val.2) :=
      continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hpB : Continuous (fun p : side =>
        (⟨p.val.val.2, by exact p.property⟩ : successorBoundary X n)) :=
      hpBraw.subtype_mk _
    refine ⟨(fun p => h (p.val.val.1, ⟨p.val.val.2, by exact p.property⟩)), ?_⟩
    exact hh.comp ((continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk hpB)
  have hagree : ∀ (z : C) (hzs : z ∈ bottom) (hzt : z ∈ side),
      f ⟨z, hzs⟩ = kside ⟨z, hzt⟩ := by
    intro z hzs hzt
    change z.val.2 ∈ successorBoundarySet X n at hzt
    simp only [f, kside]
    change z.val.2 ∈ successorBoundarySet X n at hzt
    change g z.val.2 = h (z.val.1, ⟨z.val.2, hzt⟩)
    rw [show z.val.1 = 0 from hzs]
    exact (h0 ⟨z.val.2, hzt⟩).symm
  obtain ⟨k, hkbottom, hkside⟩ := HolomorphicAnosov.cw_glue_two_closed
    bottom side hbottom hside hcover f kside hagree
  let H : (unitInterval × successorDisk X n) → T := fun p => k (r p)
  refine ⟨H, k.continuous.comp r.continuous, ?_, ?_⟩
  · intro y
    have hb : (r (0, y) : C) ∈ bottom := by
      change (r (0, y)).val.1 = 0
      simp [r, rraw, HolomorphicAnosov.cw_prism_radial_bottom y.2]
    rw [show H (0, y) = k (r (0, y)) from rfl, hkbottom _ hb]
    change g (r (0, y)).val.2 = g y
    congr 1
    simp [r, rraw, HolomorphicAnosov.cw_prism_radial_bottom y.2]
  · intro t d
    have hs : (r (t, (d : successorDisk X n)) : C) ∈ side := by
      change (r (t, (d : successorDisk X n))).val.2 ∈ successorBoundarySet X n
      have hdnorm : ‖d.val.2.val‖ = 1 := by
        have hdprop := d.property
        change dist d.val.2.val 0 = 1 at hdprop
        simpa [dist_zero_right] using hdprop
      change dist (HolomorphicAnosov.cw_prism_radial (d.val.2, t)).1.val 0 = 1
      have heq := congrArg Prod.fst
        (HolomorphicAnosov.cw_prism_radial_side d.val.2 t hdnorm)
      rw [heq]
      simpa [dist_zero_right] using hdnorm
    rw [show H (t, (d : successorDisk X n)) = k (r (t, (d : successorDisk X n))) from rfl,
      hkside _ hs]
    simp only [kside]
    change h ((r (t, (d : successorDisk X n))).val.1,
      ⟨(r (t, (d : successorDisk X n))).val.2, hs⟩) = h (t, d)
    congr 1
    have hdnorm : ‖d.val.2.val‖ = 1 := by
      simpa [successorBoundarySet, Metric.mem_sphere, dist_zero_right] using d.property
    simp [r, rraw, HolomorphicAnosov.cw_prism_radial_side d.val.2 t hdnorm]


/-- The native characteristic attaching map on the successor boundary.

This is the map obtained by restricting each `(n+1)`-cell characteristic map to its
closed-ball sphere and using the native predecessor skeleton as codomain.  It is the
attaching map to which the source quotient comparison applies.
-/
def successor_skeleton_native_attachment
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    successorBoundary X n → predecessorSkeleton X n := fun d ↦
  ⟨(_root_.Topology.RelCWComplex.map (C := (Set.univ : Set X)) (n + 1) d.1.1) d.1.2,
    (_root_.Topology.RelCWComplex.cellFrontier_subset_skeleton
      (C := (Set.univ : Set X)) n d.1.1) ⟨d.1.2, Metric.mem_sphere.mpr d.2, rfl⟩⟩

/-- The native characteristic attaching map is continuous on the boundary Sigma coproduct.

Each characteristic map is continuous on its closed disk by the classical CW structure;
restricting to the sphere and applying the Sigma coproduct criterion gives continuity into the
ambient space, and subtype introduction uses the frontier containment above. -/
theorem successor_skeleton_native_attachment_continuous
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    Continuous (successor_skeleton_native_attachment (X := X) n) := by
  let f : successorDisk X n → X := fun z ↦
    (_root_.Topology.RelCWComplex.map (C := (Set.univ : Set X)) (n + 1) z.1) z.2
  have hf : Continuous f := by
    apply continuous_sigma
    intro i
    convert (_root_.Topology.RelCWComplex.continuousOn (C := (Set.univ : Set X))
      (n + 1) i).domRestrict using 1
    rfl
  have hfb : Continuous (fun d : successorBoundary X n => f d) :=
    hf.comp continuous_subtype_val
  exact hfb.subtype_mk (fun d ↦ (successor_skeleton_native_attachment (X := X) n d).property)

/-! The raw map from the predecessor plus all closed characteristic disks is the
native carrier map used in the source quotient comparison. -/

def successor_skeleton_native_raw
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    predecessorSkeleton X n ⊕ successorDisk X n → successorSkeleton X n
  | Sum.inl x => ⟨x.1, by
      exact _root_.Topology.RelCWComplex.skeleton_mono
        (ENat.natCast_le_natCast.mpr (Nat.le_succ n)) x.2⟩
  | Sum.inr z =>
      ⟨(_root_.Topology.RelCWComplex.map (C := (Set.univ : Set X)) (n + 1) z.1) z.2,
        _root_.Topology.RelCWComplex.closedCell_subset_skeleton (C := (Set.univ : Set X))
          (n + 1) z.1 ⟨z.2, z.2.property, rfl⟩⟩

theorem continuous_successor_skeleton_native_raw
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    Continuous (successor_skeleton_native_raw (X := X) n) := by
  refine continuous_sum_dom.mpr ⟨?_, ?_⟩
  · change Continuous (fun x : predecessorSkeleton X n =>
      (⟨x.1, _⟩ : successorSkeleton X n))
    exact continuous_subtype_val.subtype_mk _
  · let f : successorDisk X n → X := fun z ↦
      (_root_.Topology.RelCWComplex.map (C := (Set.univ : Set X)) (n + 1) z.1) z.2
    have hf : Continuous f := by
      apply continuous_sigma
      intro i
      convert (_root_.Topology.RelCWComplex.continuousOn (C := (Set.univ : Set X))
        (n + 1) i).domRestrict using 1
      rfl
    exact hf.subtype_mk (fun z ↦
      _root_.Topology.RelCWComplex.closedCell_subset_skeleton (C := (Set.univ : Set X))
        (n + 1) z.1 ⟨z.2, z.2.property, rfl⟩)

theorem successor_skeleton_native_raw_surjective
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    Function.Surjective (successor_skeleton_native_raw (X := X) n) := by
  intro y
  rcases _root_.Topology.CWComplex.mem_skeleton_iff.mp y.property with
    ⟨m, hm, i, hy⟩
  have hm' : m ≤ n + 1 := ENat.natCast_le_natCast.mp hm
  by_cases hmn : m ≤ n
  · have hmem : y.1 ∈
        (_root_.Topology.RelCWComplex.skeleton (Set.univ : Set X) (n : ℕ∞) : Set X) := by
      exact _root_.Topology.CWComplex.mem_skeleton_iff.mpr
        ⟨m, ENat.natCast_le_natCast.mpr hmn, i, hy⟩
    exact ⟨Sum.inl ⟨y.1, hmem⟩, rfl⟩
  · have hmn' : m = n + 1 := by omega
    subst m
    rcases hy with ⟨z, hz, hzy⟩
    let z' : Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 :=
      ⟨z, Metric.ball_subset_closedBall hz⟩
    refine ⟨Sum.inr ⟨i, z'⟩, ?_⟩
    apply Subtype.ext
    exact hzy

/-- The raw carrier map has the native CW quotient topology.

Source: Fritsch--Piccinini, Proposition 1.2.1, pp.22--23, and the weak closed-set
criterion in Mathlib's classical `RelCWComplex`.  The proof must show that a subset
of the successor skeleton is closed exactly when its pullback to the predecessor
summand and to every closed characteristic disk is closed.  The forward implication
is continuity.  For the reverse implication, each closed-disk characteristic map is
a compact-to-Hausdorff quotient onto its closed-cell image, so disk pullback
closedness gives closedness of the intersection with that closed cell; the native CW
closed criterion then gives closedness in the successor skeleton.  This is a named
source obligation because Mathlib exposes the weak criterion and characteristic
maps separately but not this assembled Sigma quotient map.
DAG node: `topo.cw_successor_native_raw_is_quotient_map_g8`. -/
theorem successor_skeleton_native_raw_isQuotientMap
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ) :
    Topology.IsQuotientMap (successor_skeleton_native_raw (X := X) n) := by
  apply Topology.isQuotientMap_iff_isClosed.mpr
  refine ⟨successor_skeleton_native_raw_surjective n, fun s ↦ ⟨fun hs ↦
    hs.preimage (continuous_successor_skeleton_native_raw n), ?_⟩⟩
  intro hs
  let A : Set X := Subtype.val '' s
  have hAs : A ⊆ (_root_.Topology.RelCWComplex.skeleton (univ : Set X) (n + 1) : Set X) := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hleft := hs.preimage continuous_inl
  have hright := hs.preimage continuous_inr
  have hpred : IsClosed (A ∩ (_root_.Topology.RelCWComplex.skeleton
      (univ : Set X) n : Set X)) := by
    have hc := (_root_.Topology.RelCWComplex.skeleton (univ : Set X) n).closed.isClosedMap_subtype_val
      _ hleft
    convert hc using 1
    ext x
    constructor
    · rintro ⟨hx, hxpred⟩
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨⟨y.val, hxpred⟩, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨successor_skeleton_native_raw n (Sum.inl y), hy, rfl⟩, y.property⟩
  have htop (i : _root_.Topology.RelCWComplex.cell (univ : Set X) (n+1)) :
      IsClosed (A ∩ _root_.Topology.RelCWComplex.closedCell (C := (univ : Set X)) (n+1) i) := by
    let f : Metric.closedBall (0 : Fin (n+1) → ℝ) 1 → X :=
      fun z ↦ _root_.Topology.RelCWComplex.map (C := (univ : Set X)) (n+1) i z
    have hf : Continuous f := (_root_.Topology.RelCWComplex.continuousOn (C := (univ : Set X))
      (n+1) i).domRestrict
    have hc := hf.isClosedMap _ (hright.preimage (continuous_sigmaMk (i := i)))
    convert hc using 1
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, z, hz, hzy⟩
      refine ⟨⟨z, hz⟩, ?_, hzy⟩
      change successor_skeleton_native_raw n (Sum.inr ⟨i, ⟨z,hz⟩⟩) ∈ s
      have he : successor_skeleton_native_raw n (Sum.inr ⟨i, ⟨z,hz⟩⟩) = y := Subtype.ext hzy
      rwa [he]
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨successor_skeleton_native_raw n (Sum.inr ⟨i,z⟩), hz, rfl⟩,
        ⟨z, z.property, rfl⟩⟩
  have hA : IsClosed A := by
    apply _root_.Topology.CWComplex.isClosed_of_disjoint_openCell_or_isClosed_inter_closedCell
      (C := (univ : Set X)) (subset_univ A)
    intro m hm i
    by_cases hmn : m ≤ n
    · right
      have hsub : _root_.Topology.RelCWComplex.closedCell (C := (univ : Set X)) m i ⊆
          (_root_.Topology.RelCWComplex.skeleton (univ : Set X) n : Set X) :=
        (_root_.Topology.RelCWComplex.closedCell_subset_skeleton m i).trans
          (_root_.Topology.RelCWComplex.skeleton_mono (by exact_mod_cast hmn))
      have he : A ∩ _root_.Topology.RelCWComplex.closedCell (C := (univ : Set X)) m i =
          (A ∩ (_root_.Topology.RelCWComplex.skeleton (univ : Set X) n : Set X)) ∩
          _root_.Topology.RelCWComplex.closedCell (C := (univ : Set X)) m i := by
        ext x; constructor
        · exact fun h ↦ ⟨⟨h.1, hsub h.2⟩, h.2⟩
        · exact fun h ↦ ⟨h.1.1,h.2⟩
      rw [he]
      exact hpred.inter _root_.Topology.RelCWComplex.isClosed_closedCell
    · by_cases heq : m = n+1
      · subst m
        exact Or.inr (htop i)
      · left
        exact (_root_.Topology.RelCWComplex.disjoint_skeleton_openCell
          (C := (univ : Set X)) (j := i) (by exact_mod_cast (show n+1 < m by omega))).mono_left hAs
  have he : Subtype.val ⁻¹' A = s := Set.preimage_image_eq s Subtype.val_injective
  rw [← he]
  exact hA.preimage continuous_subtype_val

/-- Each `(n+1)`-cell characteristic map, viewed as a map onto its closed-cell
subtype, is a quotient map.  This is the compact-to-Hausdorff local ingredient
for the arbitrary-cell-family weak-topology argument. -/
theorem successor_skeleton_characteristic_closedCell_quotient
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (i : _root_.Topology.RelCWComplex.cell (Set.univ : Set X) (n + 1)) :
    Topology.IsQuotientMap
      (fun z : Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 ↦
        (⟨⟨(_root_.Topology.RelCWComplex.map (C := (Set.univ : Set X)) (n + 1) i) z,
          _root_.Topology.RelCWComplex.closedCell_subset_skeleton (C := (Set.univ : Set X))
            (n + 1) i ⟨z, z.property, rfl⟩⟩,
          ⟨z, z.property, rfl⟩⟩ :
          {x : successorSkeleton X n //
            x.1 ∈ _root_.Topology.RelCWComplex.closedCell (C := (Set.univ : Set X))
              (n + 1) i})) := by
  let K := Metric.closedBall (0 : Fin (n + 1) → ℝ) 1
  let Y := {x : successorSkeleton X n //
    x.1 ∈ _root_.Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) (n + 1) i}
  let f : K → Y := fun z ↦
    ⟨⟨(_root_.Topology.RelCWComplex.map (C := (Set.univ : Set X)) (n + 1) i) z,
      _root_.Topology.RelCWComplex.closedCell_subset_skeleton (C := (Set.univ : Set X))
        (n + 1) i ⟨z, z.property, rfl⟩⟩, ⟨z, z.property, rfl⟩⟩
  change Topology.IsQuotientMap f
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact ((_root_.Topology.RelCWComplex.continuousOn (C := (Set.univ : Set X))
      (n + 1) i).domRestrict)
  have hsurj : Function.Surjective f := by
    intro y
    rcases y.property with ⟨z, hz, hzy⟩
    refine ⟨⟨z, hz⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hzy
  exact Topology.IsQuotientMap.of_surjective_continuous hsurj hf

/-- Corrected native-attaching-map quotient comparison.

Source: Fritsch--Piccinini, Proposition 1.2.1 and Appendix A.4.8(iv).  The hypothesis
`h_native` is essential: it identifies `alpha` with the characteristic attaching map above,
whereas the preceding arbitrary-`alpha` theorem is false.  The native quotient comparison
remains a named source obligation because Mathlib does not expose the CW final-topology
comparison in this form.

DAG node: `topo.cw_successor_native_quotient_homeomorph_g8`.
-/
theorem successor_boundary_quot_eq_of_raw_eq
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (d e : successorBoundary X n)
    (h : successor_skeleton_native_raw n (Sum.inr d.val) =
      successor_skeleton_native_raw n (Sum.inr e.val)) :
    Quot.mk (successorAttachmentRelation n (successor_skeleton_native_attachment n))
        (Sum.inr d.val) =
      Quot.mk (successorAttachmentRelation n (successor_skeleton_native_attachment n))
        (Sum.inr e.val) := by
  have ha : successor_skeleton_native_attachment n d =
      successor_skeleton_native_attachment n e :=
    Subtype.ext (congrArg (fun q : successorSkeleton X n => q.1) h)
  exact (Quot.sound ⟨d, rfl, rfl⟩).trans
    ((congrArg (fun a : predecessorSkeleton X n =>
      Quot.mk (successorAttachmentRelation n (successor_skeleton_native_attachment n))
        (Sum.inl a)) ha).trans (Quot.sound ⟨e, rfl, rfl⟩).symm)

theorem successor_disk_boundary_of_raw_eq_left
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (z : successorDisk X n) (x : predecessorSkeleton X n)
    (h : successor_skeleton_native_raw n (Sum.inr z) =
      successor_skeleton_native_raw n (Sum.inl x)) :
    z ∈ successorBoundarySet X n := by
  change dist z.2.val 0 = 1
  have hle : dist z.2.val 0 ≤ 1 := Metric.mem_closedBall.mp z.2.property
  apply le_antisymm hle
  by_contra hn
  have hlt : dist z.2.val 0 < 1 := lt_of_not_ge hn
  have hopen : x.val ∈ _root_.Topology.RelCWComplex.openCell (n+1) z.1 :=
    ⟨z.2.val, Metric.mem_ball.mpr hlt, congrArg Subtype.val h⟩
  exact Set.disjoint_left.mp
    (_root_.Topology.RelCWComplex.disjoint_skeleton_openCell
      (C := (univ : Set X)) (j := z.1) (by exact_mod_cast Nat.lt_succ_self n))
    x.property hopen

theorem successor_disk_left_quot_eq_of_raw_eq
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (z : successorDisk X n) (x : predecessorSkeleton X n)
    (h : successor_skeleton_native_raw n (Sum.inr z) =
      successor_skeleton_native_raw n (Sum.inl x)) :
    Quot.mk (successorAttachmentRelation n (successor_skeleton_native_attachment n))
        (Sum.inr z) =
      Quot.mk (successorAttachmentRelation n (successor_skeleton_native_attachment n))
        (Sum.inl x) := by
  have hz' := successor_disk_boundary_of_raw_eq_left n z x h
  change dist z.2.val 0 = 1 at hz'
  have hz : z.2.val ∈ Metric.sphere (0 : Fin (n + 1) → ℝ) 1 := Metric.mem_sphere.mpr hz'
  let d : successorBoundary X n := ⟨⟨z.1, z.2⟩, hz⟩
  have hx : x = successor_skeleton_native_attachment n d := by
    apply Subtype.ext
    exact congrArg (fun q : successorSkeleton X n => q.1) h.symm
  exact Quot.sound ⟨d, rfl, congrArg Sum.inl hx⟩

theorem successor_skeleton_native_raw_quotient_fibres
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (p q : predecessorSkeleton X n ⊕ successorDisk X n)
    (h : successor_skeleton_native_raw (X := X) n p = successor_skeleton_native_raw n q) :
    Quot.mk (successorAttachmentRelation n (successor_skeleton_native_attachment n)) p =
      Quot.mk (successorAttachmentRelation n (successor_skeleton_native_attachment n)) q := by
  have hInterior : ∀ (z w : successorDisk X n),
      ‖z.2.val‖ < 1 → ‖w.2.val‖ < 1 →
      successor_skeleton_native_raw n (Sum.inr z) =
        successor_skeleton_native_raw n (Sum.inr w) → z = w := by
    intro z w hz hw hzw
    have hval :
        (_root_.Topology.RelCWComplex.map (C := (univ : Set X)) (n+1) z.1) z.2.val =
        (_root_.Topology.RelCWComplex.map (C := (univ : Set X)) (n+1) w.1) w.2.val :=
      congrArg (fun q : successorSkeleton X n => q.1) hzw
    have hni : ¬ Disjoint
        (_root_.Topology.RelCWComplex.openCell (C := (univ : Set X)) (n+1) z.1)
        (_root_.Topology.RelCWComplex.openCell (C := (univ : Set X)) (n+1) w.1) :=
      Set.not_disjoint_iff.mpr ⟨_,
        ⟨z.2.val, by simpa [Metric.mem_ball, dist_zero_right] using hz, rfl⟩,
        ⟨w.2.val, by simpa [Metric.mem_ball, dist_zero_right] using hw, hval.symm⟩⟩
    have hcell : z.1 = w.1 := by
      have hs := _root_.Topology.CWComplex.eq_of_not_disjoint_openCell hni
      exact eq_of_heq (Sigma.mk.inj_iff.mp hs).2
    cases z with
    | mk zi zz =>
      cases w with
      | mk wi ww =>
        dsimp at hval hz hw hcell ⊢
        cases hcell
        apply congrArg (fun a => Sigma.mk zi a)
        apply Subtype.ext
        exact (_root_.Topology.RelCWComplex.map (C := (univ : Set X)) (n+1) zi).injOn
          (by rw [_root_.Topology.RelCWComplex.source_eq]
              simpa [Metric.mem_ball, dist_zero_right] using hz)
          (by rw [_root_.Topology.RelCWComplex.source_eq]
              simpa [Metric.mem_ball, dist_zero_right] using hw) hval
  rcases p with x | z <;> rcases q with y | w
  · have hxy : x = y := Subtype.ext (congrArg (fun q : successorSkeleton X n => q.1) h)
    simp [hxy]
  · exact (successor_disk_left_quot_eq_of_raw_eq n w x h.symm).symm
  · exact successor_disk_left_quot_eq_of_raw_eq n z y h
  · by_cases hz : ‖z.2.val‖ < 1
    · have hw : ‖w.2.val‖ < 1 := by
        by_contra hn
        have hw1 : ‖w.2.val‖ = 1 := by
          have hwle : ‖w.2.val‖ ≤ 1 := by
            simpa only [Metric.mem_closedBall, dist_zero_right] using w.2.property
          exact le_antisymm hwle (le_of_not_gt hn)
        have hne := cw_cell_boundary_ne_same_dim_interior (n+1) w.1 z.1 w.2 z.2 hw1 hz
        exact hne (congrArg (fun q : successorSkeleton X n => q.1) h.symm)
      have hzw := hInterior z w hz hw h
      simp [hzw]
    · have hz1 : ‖z.2.val‖ = 1 := by
        have hle : ‖z.2.val‖ ≤ 1 := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using z.2.property
        exact le_antisymm hle (le_of_not_gt hz)
      by_cases hw : ‖w.2.val‖ < 1
      · have hne := cw_cell_boundary_ne_same_dim_interior (n+1) z.1 w.1 z.2 w.2 hz1 hw
        exact False.elim (hne (congrArg (fun q : successorSkeleton X n => q.1) h))
      · have hw1 : ‖w.2.val‖ = 1 := by
          have hle : ‖w.2.val‖ ≤ 1 := by
            simpa only [Metric.mem_closedBall, dist_zero_right] using w.2.property
          exact le_antisymm hle (le_of_not_gt hw)
        let d : successorBoundary X n := ⟨z, by
          change dist z.2.val 0 = 1
          simpa [Metric.mem_sphere, dist_zero_right] using hz1⟩
        let e : successorBoundary X n := ⟨w, by
          change dist w.2.val 0 = 1
          simpa [Metric.mem_sphere, dist_zero_right] using hw1⟩
        exact successor_boundary_quot_eq_of_raw_eq n d e h

/-- The native quotient is homeomorphic to the successor skeleton once the attaching map is the
native characteristic restriction. The remaining fibre theorem is isolated above. -/
theorem successor_skeleton_native_quotient_homeomorph
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (alpha : successorBoundary X n → predecessorSkeleton X n)
    (h_native : alpha = successor_skeleton_native_attachment (X := X) n) :
    Nonempty (Quot (successorAttachmentRelation n alpha) ≃ₜ successorSkeleton X n) := by
  subst alpha
  let R := successorAttachmentRelation n (successor_skeleton_native_attachment (X := X) n)
  let q : predecessorSkeleton X n ⊕ successorDisk X n → Quot R := Quot.mk R
  let f : predecessorSkeleton X n ⊕ successorDisk X n → successorSkeleton X n :=
    successor_skeleton_native_raw (X := X) n
  have hresp : ∀ a b, R a b → f a = f b := by
    rintro a b ⟨d, ha, hb⟩
    subst a
    subst b
    rfl
  let g : Quot R → successorSkeleton X n := Quot.lift f hresp
  have hgcomp : g ∘ q = f := by
    funext z
    rfl
  have hgcont : Continuous g := by
    apply (isQuotientMap_quot_mk (r := R)).continuous_iff.mpr
    rw [hgcomp]
    exact continuous_successor_skeleton_native_raw (X := X) n
  have hgq : Topology.IsQuotientMap g := by
    apply (isQuotientMap_quot_mk (r := R)).of_comp_isQuotientMap
    rw [hgcomp]
    exact successor_skeleton_native_raw_isQuotientMap (X := X) n
  have hginj : Function.Injective g := by
    intro x y hxy
    induction x using Quot.inductionOn with | h a =>
      induction y using Quot.inductionOn with | h b =>
        exact successor_skeleton_native_raw_quotient_fibres n a b (by simpa [g, q, f] using hxy)
  have hhome : IsHomeomorph g :=
    isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hgq, hginj⟩
  exact ⟨hhome.homeomorph⟩

/-- The corrected quotient comparison, after the native characteristic attachment has been constructed.

The native-map hypothesis excludes arbitrary continuous attachments, whose quotients can have
extra disconnected predecessor components.  Source: Fritsch--Piccinini, Proposition 1.2.1. -/
theorem successor_skeleton_quotient_homeomorph
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    (alpha : successorBoundary X n → predecessorSkeleton X n)
    (h_alpha : Continuous alpha)
    (h_native : alpha = successor_skeleton_native_attachment (X := X) n) :
    Nonempty (Quot (successorAttachmentRelation n alpha) ≃ₜ successorSkeleton X n) := by
  subst alpha
  exact successor_skeleton_native_quotient_homeomorph (X := X) n
    (successor_skeleton_native_attachment (X := X) n) rfl

/-- Assemble the separately named successor-stage source obligations into the interface used
by `normal_closed_adjunction`.  The aggregate data must use
`successor_skeleton_native_attachment (X := X) n` as its `alpha`, together with the native
quotient comparison; the separately stated arbitrary-`alpha` theorem above is disputed and is
not used here.  This aggregate remains a named source obligation until the native quotient
comparison and disk-prism cofibration are supplied.  DAG node:
`topo.cw_successor_skeleton_adjunction_data_g7`.
-/
theorem successor_skeleton_adjunction_data
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    [NormalSpace (predecessorSkeleton X n)] :
    Nonempty (SuccessorSkeletonAdjunctionData (X := X) n) := by
  obtain ⟨hquot⟩ := successor_skeleton_native_quotient_homeomorph
    (X := X) n (successor_skeleton_native_attachment (X := X) n) rfl
  exact ⟨
    { alpha := successor_skeleton_native_attachment (X := X) n
      alpha_continuous := successor_skeleton_native_attachment_continuous (X := X) n
      quotient_homeomorph := hquot
      predecessor_normal := inferInstance
      predecessor_compactly_generated :=
        successor_skeleton_predecessor_compactly_generated (X := X) n
      disk_normal := successor_skeleton_disk_normal (X := X) n
      disk_compactly_generated := successor_skeleton_disk_compactly_generated (X := X) n
      boundary_closed := successor_skeleton_boundary_closed (X := X) n
      cofibration := successor_skeleton_disk_cofibration (X := X) n }⟩

/-- Normality of the successor obtained from explicit adjunction data.

This assembly is formal: `normal_closed_adjunction` proves normality of the ordinary quotient,
and the supplied quotient homeomorphism transports it to the native successor skeleton.
-/
theorem normality_of_successor_skeleton_of_adjunction_data
    {X : Type u} [TopologicalSpace X] [T2Space X]
    [_root_.Topology.CWComplex (Set.univ : Set X)] (n : ℕ)
    [NormalSpace (predecessorSkeleton X n)]
    (h : SuccessorSkeletonAdjunctionData (X := X) n) :
    NormalSpace (successorSkeleton X n) := by
  let : CompactlyGeneratedSpace (predecessorSkeleton X n) :=
    h.predecessor_compactly_generated
  let : CompactlyGeneratedSpace (successorDisk X n) := h.disk_compactly_generated
  let : NormalSpace (successorDisk X n) := h.disk_normal
  have hquot := normal_closed_adjunction
    (D := successorBoundarySet X n)
    h.boundary_closed h.cofibration h.alpha h.alpha_continuous
  let : NormalSpace (Quot (successorAttachmentRelation n h.alpha)) := hquot.1
  exact h.quotient_homeomorph.normalSpace

end HolomorphicAnosov.Topology.CWComplex


