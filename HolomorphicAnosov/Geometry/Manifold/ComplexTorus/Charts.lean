import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexModel
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Covering
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Linarith

/-!
The lattice quotient has a complex manifold atlas of local inverses of the quotient projection,
with transitions locally given by lattice translations. (Zhang, Thm 1.2, pp. 11–13)
-/

namespace HolomorphicAnosov

/-- The atlas on the complex torus consists of local inverses of the lattice quotient projection.
(Zhang, Thm 1.2, pp. 11–13) -/
noncomputable instance complexTorusChartedSpace {d : ℕ} (L : FullComplexLattice d) :
    ChartedSpace (ComplexModel d) (ComplexTorus L) :=
  (torus_quotient_covering L).isLocalHomeomorph.chartedSpace
    (H := ComplexModel d) (torus_quotient_covering L).surjective


open scoped ContDiff

/-- Each chart in the quotient atlas restricts near any point of its source to the inverse of the
quotient projection on a small ball. (Zhang, pp. 11–13) -/
theorem complexTorus_chart_smallBall_restriction {d : ℕ} (L : FullComplexLattice d)
    (e : OpenPartialHomeomorph (ComplexTorus L) (ComplexModel d))
    (he : e ∈ atlas (ComplexModel d) (ComplexTorus L))
    {x : ComplexTorus L} (hx : x ∈ e.source) :
    let q := (QuotientAddGroup.mk : ComplexModel d → ComplexTorus L)
    ∃ r : ℝ, 0 < r ∧ Metric.ball (e x) r ⊆ e.target ∧
      (∀ ell : L.lattice, ell ≠ 0 →
        Disjoint (Metric.ball (e x) r)
          ((fun z : ComplexModel d ↦ z + (ell : ComplexModel d)) '' Metric.ball (e x) r)) ∧
      Set.EqOn (fun z ↦ e (q z)) id (Metric.ball (e x) r) ∧
      Set.EqOn e.symm q (Metric.ball (e x) r) ∧
      q '' Metric.ball (e x) r ⊆ e.source := by
  have hsymm : (e.symm : ComplexModel d → ComplexTorus L) = QuotientAddGroup.mk := by
    change ∃ x : ComplexTorus L,
      ((torus_quotient_covering L).isLocalHomeomorph.localInverseAt
        ((torus_quotient_covering L).surjective.hasRightInverse.choose x)).trans
        (OpenPartialHomeomorph.refl (ComplexModel d)) = e at he
    obtain ⟨x, rfl⟩ := he
    simp
  have hball : ∃ r : ℝ, 0 < r ∧ Metric.ball (e x) r ⊆ e.target ∧
      ∀ ell : L.lattice, ell ≠ 0 →
        Disjoint (Metric.ball (e x) r)
          ((fun z : ComplexModel d ↦ z + (ell : ComplexModel d)) '' Metric.ball (e x) r) := by
    let : DiscreteTopology L.lattice := L.discrete
    obtain ⟨ε, hε, hεball⟩ :=
      Metric.exists_ball_inter_eq_singleton_of_mem_discrete
        (show IsDiscrete (L.lattice : Set (ComplexModel d)) from DiscreteTopology.isDiscrete)
        (L.lattice.zero_mem)
    obtain ⟨ρ, hρ, hρball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hx))
    let r := min ρ (ε / 3)
    have hr : 0 < r := lt_min hρ (by linarith)
    refine ⟨r, hr, (Metric.ball_subset_ball (min_le_left _ _)).trans hρball, ?_⟩
    intro ell hell
    apply Set.disjoint_left.mpr
    intro z hz hztrans
    obtain ⟨y, hy, rfl⟩ := hztrans
    have hz' : dist (y + (ell : ComplexModel d)) (e x) < r := hz
    have hy' : dist (e x) y < r := by simpa only [Metric.mem_ball, dist_comm] using hy
    have hd : dist (y + (ell : ComplexModel d)) y < ε := by
      have htriangle := dist_triangle (y + (ell : ComplexModel d)) (e x) y
      have hrε : r ≤ ε / 3 := min_le_right _ _
      linarith
    have hellball : (ell : ComplexModel d) ∈ Metric.ball 0 ε := by
      simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hd
    have hellzero : (ell : ComplexModel d) = 0 := by
      have hm : (ell : ComplexModel d) ∈
          Metric.ball 0 ε ∩ (L.lattice : Set (ComplexModel d)) := ⟨hellball, ell.property⟩
      rw [hεball] at hm
      exact Set.mem_singleton_iff.mp hm
    exact hell (Subtype.ext hellzero)
  obtain ⟨r, hr, hrtarget, hrdisjoint⟩ := hball
  refine ⟨r, hr, hrtarget, hrdisjoint, ?_, ?_, ?_⟩
  · intro z hz
    change e (QuotientAddGroup.mk z) = z
    rw [← hsymm]
    exact e.right_inv (hrtarget hz)
  · intro z _
    exact congrFun hsymm z
  · rintro y ⟨z, hz, rfl⟩
    change QuotientAddGroup.mk z ∈ e.source
    rw [← hsymm]
    exact e.symm.map_source (hrtarget hz)

/-- Every transition in the quotient atlas is a lattice translation on a neighborhood of each point
of its source. (Zhang, pp. 11–13) -/
theorem complexTorus_chart_transition_locally_translation {d : ℕ}
    (L : FullComplexLattice d)
    (e e' : OpenPartialHomeomorph (ComplexTorus L) (ComplexModel d))
    (he : e ∈ atlas (ComplexModel d) (ComplexTorus L))
    (he' : e' ∈ atlas (ComplexModel d) (ComplexTorus L))
    {z : ComplexModel d} (hz : z ∈ (e.symm.trans e').source) :
    ∃ ell : L.lattice, ∃ U : Set (ComplexModel d),
      IsOpen U ∧ z ∈ U ∧ U ⊆ (e.symm.trans e').source ∧
        Set.EqOn (e.symm.trans e') (fun w ↦ w + (ell : ComplexModel d)) U := by
  have hsymm : ∀ (a : OpenPartialHomeomorph (ComplexTorus L) (ComplexModel d)),
      a ∈ atlas (ComplexModel d) (ComplexTorus L) →
      (a.symm : ComplexModel d → ComplexTorus L) = QuotientAddGroup.mk := by
    intro a ha
    change ∃ x : ComplexTorus L,
      ((torus_quotient_covering L).isLocalHomeomorph.localInverseAt
        ((torus_quotient_covering L).surjective.hasRightInverse.choose x)).trans
        (OpenPartialHomeomorph.refl (ComplexModel d)) = a at ha
    obtain ⟨x, rfl⟩ := ha
    simp
  let t := e.symm.trans e'
  have hm : ∀ w ∈ t.source, t w - w ∈ L.lattice := by
    intro w hw
    have hq : (QuotientAddGroup.mk (t w) : ComplexTorus L) = QuotientAddGroup.mk w := by
      change (QuotientAddGroup.mk (e' (e.symm w)) : ComplexTorus L) = QuotientAddGroup.mk w
      have hw' : e.symm w ∈ e'.source := hw.2
      calc
        QuotientAddGroup.mk (e' (e.symm w)) = e'.symm (e' (e.symm w)) :=
          (congrFun (hsymm e' he') (e' (e.symm w))).symm
        _ = e.symm w := e'.left_inv hw'
        _ = QuotientAddGroup.mk w := congrFun (hsymm e he) w
    exact QuotientAddGroup.eq_iff_sub_mem.mp hq
  let D : t.source → L.lattice := fun w ↦ ⟨t w - w, hm w w.property⟩
  have hc : Continuous D :=
    (t.continuousOn.domRestrict.sub continuous_subtype_val).subtype_mk _
  have : DiscreteTopology L.lattice := L.discrete
  have hlc : IsLocallyConstant D := (IsLocallyConstant.iff_continuous D).2 hc
  let p : t.source := ⟨z, hz⟩
  obtain ⟨V, hV, hpV, hconst⟩ := hlc.exists_open p
  refine ⟨D p, Subtype.val '' V, t.open_source.isOpenMap_subtype_val V hV,
    ⟨p, hpV, rfl⟩, ?_, ?_⟩
  · rintro w ⟨v, _, rfl⟩
    exact v.property
  · rintro w ⟨v, hv, rfl⟩
    have h := congrArg Subtype.val (hconst v hv)
    change t v - (v : ComplexModel d) = (D p : ComplexModel d) at h
    exact ((sub_eq_iff_eq_add).1 h).trans (add_comm _ _)

/-- The local-inverse quotient atlas defines a complex manifold structure on `ComplexTorus L`. -/
theorem complexTorus_isManifold {d : ℕ} (L : FullComplexLattice d) :
    IsManifold (complexModel d) ∞ (ComplexTorus L) := by
  apply isManifold_of_contDiffOn (complexModel d) ∞ (ComplexTorus L)
  intro e e' he he'
  suffices h : ContDiffOn ℂ ∞ (e.symm.trans e') (e.symm.trans e').source by
    simpa only [complexModel, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ] using h
  intro z hz
  obtain ⟨ell, U, hU, hzU, hUS, hEq⟩ :=
    complexTorus_chart_transition_locally_translation L e e' he he' hz
  have htranslation : ContDiff ℂ ∞ (fun w : ComplexModel d ↦ w + (ell : ComplexModel d)) :=
    contDiff_id.add contDiff_const
  exact ((htranslation.contDiffOn.congr hEq).contDiffAt (hU.mem_nhds hzU)).contDiffWithinAt



end HolomorphicAnosov
