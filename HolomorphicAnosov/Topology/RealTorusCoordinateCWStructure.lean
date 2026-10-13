import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.CWComplex.Classical.Finite

/-!
# Coordinate CW cells of the real torus

Source: Hatcher, Algebraic Topology, Example 0.3, p. 6, Theorem A.6, p. 524,
and Proposition A.2, p. 521; Bredon, Topology and Geometry, IV section 12,
p. 211 and Theorem 12.3, p. 214. The carrier is Mathlib's original period-one
quotient-circle product `UnitAddTorus (Fin r)`.
-/

namespace HolomorphicAnosov

noncomputable section

theorem coordinate_ball_iff {n : ℕ} (u : Fin n → ℝ) :
    u ∈ Metric.ball 0 1 ↔ ∀ i, -1 < u i ∧ u i < 1 := by
  rw [ball_pi _ (by norm_num : (0 : ℝ) < 1)]
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_ball, Pi.zero_apply,
    dist_zero_right, Real.norm_eq_abs, abs_lt]

theorem coordinate_closedBall_iff {n : ℕ} (u : Fin n → ℝ) :
    u ∈ Metric.closedBall 0 1 ↔ ∀ i, -1 ≤ u i ∧ u i ≤ 1 := by
  rw [closedBall_pi _ (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [Set.mem_pi, Set.mem_univ, forall_const, Metric.mem_closedBall, Pi.zero_apply,
    dist_zero_right, Real.norm_eq_abs, abs_le]

private lemma circle_affine_ne_zero {t : ℝ} (ht : -1 < t ∧ t < 1) :
    (((t + 1) / 2 : ℝ) : UnitAddCircle) ≠ 0 := by
  have h := (AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0).map_source
    (show (t + 1) / 2 ∈ Set.Ioo 0 (0 + 1) by constructor <;> linarith)
  simpa using h

private lemma circle_affine_ne_zero_iff {t : ℝ} (ht : -1 ≤ t ∧ t ≤ 1) :
    (((t + 1) / 2 : ℝ) : UnitAddCircle) ≠ 0 ↔ -1 < t ∧ t < 1 := by
  refine ⟨fun h ↦ ?_, circle_affine_ne_zero⟩
  constructor
  · by_contra hn
    have he : t = -1 := by linarith
    simp [he] at h
  · by_contra hn
    have he : t = 1 := by linarith
    simp [he, AddCircle.coe_period] at h


open Set Topology _root_.Topology

/-- The real coordinate torus has its finite Hausdorff CW structure with one cell per support.

The torus keeps its quotient/product topology. The dimension-`d` indices are exactly the subsets
of `Fin r` of cardinality `d`. The open cell indexed by `S` consists of points whose nonzero
coordinates are precisely `S`; the empty-subset zero cell is the origin. The characteristic-map
formula is asserted on the native closed maximum-norm disk after choosing an enumeration of `S`.
Its forward map uses the actual quotient `ℝ → AddCircle 1`. The `CWComplex` fields retain the
native open-disk source, closed-disk continuity, inverse continuity, lower-boundary and
weak-topology conditions. There is no supplied CW structure among the hypotheses. For `r = 0`, the empty product
has its single zero cell and the coordinate formula has no coordinates.

Source: Hatcher, Algebraic Topology, Example 0.3, printed p. 6, Theorem A.6 and proof,
printed p. 524, Proposition A.2, p. 521; Bredon, Topology and Geometry (1993), IV section 12,
printed p. 211, Theorem 12.3 and proof, p. 214, using I.13.19, p. 43.
Local files: literature/hatcher-at.pdf/.txt and
literature/Bredon-Topology-and-Geometry-1993.pdf/.txt.
The period-one formulas, native maximum-norm blocks, support identification and empty product
are the explicit source-omitted guards in the DAG proof, built using the named Mathlib primitives.

Complete natural-language proof of `topo.real_torus_coordinate_cw_structure`:
The product characteristic maps are those of Hatcher A.6 and Bredon IV section 12.
The following explicit coordinate verification is an agent-written implementation of their
finite product cells on Mathlib's native disks, rather than an invocation of an already
constructed abstract product CW structure.

TP1. In the period-one quotient circle, the quotient chart on (0,1) is a homeomorphism
onto the complement of zero, with inverse the representative in [0,1). The affine
coordinate t↦(t+1)/2 takes (-1,1) to (0,1). On [-1,1], its quotient is nonzero exactly
when -1<t<1: the endpoints map to zero, and the chart excludes any interior zero.
The quotient norm supplies the original circle's Hausdorff topology and the finite
product is Hausdorff. Positive-radius native maximum-norm ball identities hold also
for an empty coordinate type.

TP2. In dimension n the index is an actual subset S of Fin r of cardinality n. Choose
an equivalence e:Fin n≃S. Define the characteristic map coordinatewise: at i∈S its
value is the quotient of (u(e⁻¹i)+1)/2, and otherwise its value is zero. Define the
inverse on the exact target {z: z_i≠0 iff i∈S} by twice the [0,1) representative
of z_(e j), minus one. Every such representative is in (0,1), so the inverse belongs
to the native open unit ball. The circle chart's two inverse equations, and the
zero coordinates outside S, give both PartialEquiv inverse laws. Its source is the
native open unit ball; its target is precisely the specified nonzero support.
The forward map is continuous on the whole parameter space by coordinatewise
quotient and affine continuity. The inverse is continuous on its target because
all relevant circle coordinates avoid zero; no endpoint inverse continuity is used.

TP3. For any torus point z, let S be the finite set of its nonzero coordinates. The
inverse from TP2 gives an open-disk representative of z, hence also a closed-disk
representative. Thus the closed characteristic images cover the entire original
torus. If two open images meet at z, both index subsets are its nonzero support;
the subsets, their cardinalities, and their dependent dimension-indexed cells are
equal. This proves pairwise disjointness with the actual indexing types.

TP4. A sphere point u lies in the native closed unit ball. Let T be the nonzero
support of its characteristic image. It is a subset of S. If T=S, every active
affine coordinate is nonzero, so TP1 implies -1<u_j<1 for every j. The finite-product
open-ball identity would put u in the open ball, contradicting its sphere equation.
Thus T is a proper subset of S and |T|<n. The TP3 representative of the same image
in its T-indexed disk proves that every sphere image belongs to a strictly lower
dimensional closed characteristic image. The empty-coordinate sphere is empty,
so this argument requires no positive-dimension exception or extra cell.

TP5. Each dimension has finitely many subset indices. If n≥r+1, no subset of Fin r
has cardinality n. These are precisely finite cells and eventual emptiness.
Apply Mathlib CWComplex.mkFinite to the constructed PartialEquivs, their exact
sources, closed-disk and inverse continuity, disjoint open images, lower sphere
images, and full coverage. This constructor proves the native weak-topology
fields in the existing topology; it introduces no new product topology or
supplied CW hypothesis. CWComplex.finite_mkFinite proves finiteness of this same
structure. This is the direct finite characteristic-map packaging of the source
product cells; the separate binary quotient-cover descent is unnecessary here.

TP6. The constructor retains the index types and characteristic maps. Take the
index equivalences to be identity equivalences. Each open cell is the image of
the source, hence its PartialEquiv target, giving the exact support equation.
For S=∅ this target is precisely the zero function, so the zero cell is {0}.
The chosen enumeration gives the displayed characteristic formula, even beyond
its required closed-disk restriction. When r=0, all coordinate arguments are
vacuous and only the empty-subset zero cell remains. No new theorem about an
unspecified CW structure, dimension assumption, or alternative torus is used.
-/
theorem real_torus_coordinate_cw_structure (r : ℕ) :
    T2Space (UnitAddTorus (Fin r)) ∧
    ∃ cw : CWComplex (univ : Set (UnitAddTorus (Fin r))),
      letI : CWComplex (univ : Set (UnitAddTorus (Fin r))) := cw
      CWComplex.Finite (univ : Set (UnitAddTorus (Fin r))) ∧
      ∃ index : ∀ d : ℕ,
          {S : Finset (Fin r) // S.card = d} ≃
            RelCWComplex.cell (univ : Set (UnitAddTorus (Fin r))) d,
        (∀ (d : ℕ) (S : {S : Finset (Fin r) // S.card = d}),
          RelCWComplex.openCell (C := (univ : Set (UnitAddTorus (Fin r)))) d (index d S) =
            {z : UnitAddTorus (Fin r) | ∀ i : Fin r, z i ≠ 0 ↔ i ∈ S.val}) ∧
        RelCWComplex.openCell (C := (univ : Set (UnitAddTorus (Fin r)))) 0
            (index 0 ⟨∅, Finset.card_empty⟩) = {0} ∧
        (∀ (d : ℕ) (S : {S : Finset (Fin r) // S.card = d}),
          ∃ e : Fin d ≃ ↥S.val,
            ∀ u : Fin d → ℝ, u ∈ Metric.closedBall 0 1 →
              RelCWComplex.map (C := (univ : Set (UnitAddTorus (Fin r)))) d (index d S) u =
                fun i : Fin r ↦ if hi : i ∈ S.val then
                  (((u (e.symm ⟨i, hi⟩) + 1) / 2 : ℝ) : UnitAddCircle) else 0) := by
  classical
  let cells := fun n : ℕ ↦ {S : Finset (Fin r) // S.card = n}
  let enum := fun n (S : cells n) ↦ (Fintype.equivFinOfCardEq
    (show Fintype.card ↥S.val = n by simpa using S.property)).symm
  let forward := fun n (S : cells n) (u : Fin n → ℝ) (i : Fin r) ↦
    if hi : i ∈ S.val then
      (((u ((enum n S).symm ⟨i, hi⟩) + 1) / 2 : ℝ) : UnitAddCircle) else 0
  let inverse := fun n (S : cells n) (z : UnitAddTorus (Fin r)) (j : Fin n) ↦
    2 * ((AddCircle.equivIco (1 : ℝ) 0 (z (enum n S j))) : ℝ) - 1
  let target := fun n (S : cells n) ↦ {z : UnitAddTorus (Fin r) |
    ∀ i, z i ≠ 0 ↔ i ∈ S.val}
  have hforward : ∀ n (S : cells n) u, u ∈ Metric.ball 0 1 →
      forward n S u ∈ target n S := by
    intro n S u hu i
    dsimp [forward]
    split_ifs with hi
    · exact iff_of_true (circle_affine_ne_zero ((coordinate_ball_iff u).mp hu _)) hi
    · simp [hi]
  have hinverse : ∀ n (S : cells n) z, z ∈ target n S →
      inverse n S z ∈ Metric.ball 0 1 := by
    intro n S z hz
    apply (coordinate_ball_iff _).mpr
    intro j
    have hn : z (enum n S j) ≠ 0 := (hz _).mpr (enum n S j).property
    have hm := (AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0).map_target
      (show z (enum n S j) ∈ ({((0 : ℝ) : UnitAddCircle)} : Set UnitAddCircle)ᶜ by
        simpa using hn)
    change 0 < ((AddCircle.equivIco (1 : ℝ) 0 (z (enum n S j))) : ℝ) ∧
      ((AddCircle.equivIco (1 : ℝ) 0 (z (enum n S j))) : ℝ) < 0 + 1 at hm
    dsimp [inverse]
    constructor <;> linarith
  have hleft : ∀ n (S : cells n) u, u ∈ Metric.ball 0 1 →
      inverse n S (forward n S u) = u := by
    intro n S u hu
    funext j
    have ht := (coordinate_ball_iff u).mp hu j
    have he := (AddCircle.openPartialHomeomorphCoe (1 : ℝ) 0).left_inv
      (show (u j + 1) / 2 ∈ Set.Ioo 0 (0 + 1) by constructor <;> linarith)
    dsimp [inverse, forward]
    simp only [ite_eq_left (enum n S j).property, Equiv.symm_apply_apply]
    change 2 * ((AddCircle.equivIco (1 : ℝ) 0
      (((u j + 1) / 2 : ℝ) : UnitAddCircle)) : ℝ) - 1 = u j
    change ((AddCircle.equivIco (1 : ℝ) 0
      (((u j + 1) / 2 : ℝ) : UnitAddCircle)) : ℝ) = (u j + 1) / 2 at he
    rw [he]
    ring
  have hright : ∀ n (S : cells n) z, z ∈ target n S →
      forward n S (inverse n S z) = z := by
    intro n S z hz
    funext i
    dsimp [forward]
    split_ifs with hi
    · dsimp [inverse]
      rw [Equiv.apply_symm_apply]
      have he := (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply (z i)
      have ha : (2 * ((AddCircle.equivIco (1 : ℝ) 0 (z i)) : ℝ) - 1 + 1) / 2 =
          ((AddCircle.equivIco (1 : ℝ) 0 (z i)) : ℝ) := by ring
      rw [ha]
      exact he
    · exact (not_ne_iff.mp ((hz i).not.mpr hi)).symm
  let maps := fun n (S : cells n) ↦
    ({ toFun := forward n S
       invFun := inverse n S
       source := Metric.ball 0 1
       target := target n S
       map_source' := hforward n S
       map_target' := hinverse n S
       left_inv' := hleft n S
       right_inv' := hright n S } : PartialEquiv (Fin n → ℝ) (UnitAddTorus (Fin r)))
  have hcontinuous : ∀ n (S : cells n), Continuous (forward n S) := by
    intro n S
    apply continuous_pi
    intro i
    dsimp [forward]
    split_ifs
    · exact (AddCircle.continuous_mk' (1 : ℝ)).comp
        (((continuous_apply _).add continuous_const).div_const 2)
    · exact continuous_const
  have hcontinuous_inv : ∀ n (S : cells n), ContinuousOn (inverse n S) (target n S) := by
    intro n S
    apply continuousOn_pi.mpr
    intro j z hz
    have hv : ContinuousAt (fun z : UnitAddTorus (Fin r) ↦
        ((AddCircle.equivIco (1 : ℝ) 0 (z (enum n S j))) : ℝ)) z :=
      continuousAt_subtype_val.comp
        ((AddCircle.continuousAt_equivIco (1 : ℝ) 0
          (by simpa using (hz _).mpr (enum n S j).property)).comp
            (continuous_apply _).continuousAt)
    exact ((continuousAt_const.mul hv).sub continuousAt_const).continuousWithinAt
  let support := fun z : UnitAddTorus (Fin r) ↦ Finset.univ.filter (fun i ↦ z i ≠ 0)
  have hsupport : ∀ z i, i ∈ support z ↔ z i ≠ 0 := by
    intro z i
    simp [support]
  have htarget_support : ∀ z, z ∈ target (support z).card ⟨support z, rfl⟩ := by
    intro z i
    exact (hsupport z i).symm
  have hrepresentation : ∀ z, ∃ u ∈ Metric.ball 0 1,
      maps (support z).card ⟨support z, rfl⟩ u = z := by
    intro z
    exact ⟨inverse _ _ z, hinverse _ _ z (htarget_support z),
      hright _ _ z (htarget_support z)⟩
  have hdisjoint : (univ : Set (Σ n, cells n)).PairwiseDisjoint
      (fun ni ↦ maps ni.1 ni.2 '' Metric.ball 0 1) := by
    rw [Set.pairwiseDisjoint_iff]
    rintro ⟨n, S⟩ _ ⟨m, T⟩ _ ⟨z, ⟨⟨u, hu, huz⟩, ⟨v, hv, hvz⟩⟩⟩
    have hs : z ∈ target n S := huz ▸ hforward n S u hu
    have ht : z ∈ target m T := hvz ▸ hforward m T v hv
    have hST : S.val = T.val := Finset.ext fun i ↦ (hs i).symm.trans (ht i)
    have hnm : n = m := S.property.symm.trans (hST ▸ T.property)
    subst m
    exact congrArg (Sigma.mk n) (Subtype.ext hST)
  have hboundary : ∀ n (S : cells n), MapsTo (maps n S) (Metric.sphere 0 1)
      (⋃ (m < n) (j : cells m), maps m j '' Metric.closedBall 0 1) := by
    intro n S u hu
    let z := forward n S u
    let T := support z
    have huc : u ∈ Metric.closedBall 0 1 := Metric.sphere_subset_closedBall hu
    have hTS : T ⊆ S.val := by
      intro i hi
      have hz : z i ≠ 0 := (hsupport z i).mp hi
      by_contra hn
      exact hz (by simp [z, forward, hn])
    have hne : T ≠ S.val := by
      intro he
      have hub : u ∈ Metric.ball 0 1 := by
        apply (coordinate_ball_iff u).mpr
        intro j
        have hz : z (enum n S j) ≠ 0 := (hsupport z _).mp
          (by change _ ∈ T; rw [he]; exact (enum n S j).property)
        have hj := (coordinate_closedBall_iff u).mp huc j
        apply (circle_affine_ne_zero_iff hj).mp
        simpa [z, forward] using hz
      have hh := Metric.mem_sphere.mp hu
      have hl := Metric.mem_ball.mp hub
      linarith
    have hcard : T.card < n := by
      rw [← S.property]
      exact Finset.card_lt_card (ssubset_iff_subset_ne.mpr ⟨hTS, hne⟩)
    obtain ⟨v, hv, hev⟩ := hrepresentation z
    exact mem_iUnion.mpr ⟨T.card, mem_iUnion.mpr ⟨hcard,
      mem_iUnion.mpr ⟨⟨T, rfl⟩, ⟨v, Metric.ball_subset_closedBall hv, hev⟩⟩⟩⟩
  have hcover : (⋃ (n : ℕ) (S : cells n), maps n S '' Metric.closedBall 0 1) = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨u, hu, he⟩ := hrepresentation z
    exact mem_iUnion.mpr ⟨(support z).card, mem_iUnion.mpr
      ⟨⟨support z, rfl⟩, ⟨u, Metric.ball_subset_closedBall hu, he⟩⟩⟩
  have hempty : ∀ᶠ n in Filter.atTop, IsEmpty (cells n) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨r + 1, fun n hn ↦ ⟨fun S ↦ ?_⟩⟩
    have hc := Finset.card_le_univ S.val
    simp only [Fintype.card_fin] at hc
    have hs := S.property
    omega
  have hfinite : ∀ n, Finite (cells n) := fun n ↦ inferInstance
  have hsource : ∀ n (S : cells n), (maps n S).source = Metric.ball 0 1 :=
    fun _ _ ↦ rfl
  let cw := CWComplex.mkFinite univ cells maps hempty hfinite hsource
    (fun n S ↦ (hcontinuous n S).continuousOn) hcontinuous_inv hdisjoint hboundary hcover
  refine ⟨inferInstance, cw, ?_⟩
  let : CWComplex (univ : Set (UnitAddTorus (Fin r))) := cw
  have hcwfinite : CWComplex.Finite (univ : Set (UnitAddTorus (Fin r))) :=
    CWComplex.finite_mkFinite univ cells maps hempty hfinite hsource
      (fun n S ↦ (hcontinuous n S).continuousOn) hcontinuous_inv hdisjoint hboundary hcover
  refine ⟨hcwfinite, fun d ↦ Equiv.refl (cells d), ?_, ?_, ?_⟩
  · intro d S
    exact (maps d S).image_source_eq_target
  · change maps 0 ⟨∅, Finset.card_empty⟩ '' Metric.ball 0 1 = {0}
    rw [show Metric.ball 0 1 = (maps 0 ⟨∅, Finset.card_empty⟩).source from rfl,
      PartialEquiv.image_source_eq_target]
    change target 0 ⟨∅, Finset.card_empty⟩ = {0}
    ext z
    simp only [target, mem_ofPred_eq, Finset.notMem_empty, iff_false, not_ne_iff,
      mem_singleton_iff]
    exact ⟨fun h ↦ funext h, fun h i ↦ congrFun h i⟩
  · intro d S
    exact ⟨enum d S, fun _ _ ↦ rfl⟩


end

end HolomorphicAnosov

