import HolomorphicAnosov.Topology.HatcherRecursiveCellSelection
import HolomorphicAnosov.Topology.HatcherControlledExtensionUniformBall
import HolomorphicAnosov.Topology.HatcherCenteredBoundaryExtensionBound
import HolomorphicAnosov.Topology.HatcherDyadicComplementShrinkingCW
import HolomorphicAnosov.Topology.HatcherNearestPointFactorTwo
import HolomorphicAnosov.Topology.HatcherNestedNullhomotopicBalls
import HolomorphicAnosov.Topology.HatcherShrinkingCellsNeighborhood
import HolomorphicAnosov.Topology.HatcherCompatibleCellGluing

/-!
# Controlled higher-cell selection and gluing for Hatcher's construction

This module isolates the CW induction from the final metric estimate.  Hatcher,
*Algebraic Topology*, Theorem A.7, pp.525--526, selects a downward-closed family
of complement cells, extends each attaching map into the compact carrier with
controlled image diameter, and glues the compatible extensions using local
finiteness.  The resulting map is continuous on the selected union and fixes
its carrier.  The relative-open neighborhood estimate is included here; its metric epsilon-delta
reformulation is supplied by the companion module.
-/

namespace HolomorphicAnosov
open Metric Set

/-- The selected higher-cell subcomplex and its glued map.

Source: Hatcher, *Algebraic Topology*, Theorem A.7, printed pp.525--526.

Complete natural-language construction:

CS1. Choose the locally finite regular dyadic CW decomposition of the complement, of dimension at
most N. Each closed-cell boundary is a finite union of lower closed cells, each closed
characteristic disk maps homeomorphically to its cell, and closed cells meeting sufficiently small
balls about C lie in any prescribed larger ball. Choose nearest-point values for vertices; points
within ε/2 of c have chosen values within ε of c.

CS2. Induct on the cell dimension. Initially select every vertex. At the next dimension select
precisely the cells whose entire boundaries are already selected and whose prescribed boundary
maps extend. For each such cell choose an extension whose image diameter is at most twice that of
every extension. If the boundary data are constant, use their constant extension. Otherwise the
positive distance between two boundary values is a common positive lower bound on extension
diameters; compactness of the disk bounds these diameters, and approximation to their infimum
gives the factor-two choice. The finite lower-cell boundary cover and agreement of earlier maps
paste to a continuous boundary map. Regular characteristic maps identify each closed cell with a
disk. Extend without changing any earlier value. Intersections of distinct new cells lie in the
earlier skeleton, so the resulting maps agree on overlaps. Iterate through dimension N. Apply
recursive cell selection with Q consisting of nearest-point values in dimension zero and
simultaneous comparison-ball control in positive dimensions. Its geometric hypotheses hold: a
closed cell splits into its frontier and open cell; distinct open cells are disjoint, and the
lower skeleton containing the other frontier is disjoint from the larger-dimensional open cell.
The exact finite boundary cover gives the required lower cell through each boundary point. Hence
this recursion and all overlap compatibility are now proved in Lean; admissible extension
existence on small cells is established in the later local induction.

CS3. Fix c in C and a relative open neighborhood V, and choose ε>0 with its centered ball
contained in V. Obtain positive sequences r(n)<R(n), with R(0)=ε, nullhomotopic inclusions of the
r(n) balls into the R(n) balls, and r(n + 1)+4R(n + 1)<r(n). The r sequence is decreasing. Put
t=r(N)/2 and consider every closed cell contained in the open ambient t-ball. Lower cells
contained in such a cell boundary are also contained in that ball. In dimension zero nearest-point
control puts the chosen image in the r(N)-ball.

CS4. Prove by strong induction on d≤N that every closed d-cell inside the ambient t-ball is
selected and its chosen image lies in the r(N - d)-ball. For a positive-dimensional cell, all lower
boundary cells are small, so induction selects them and places their images in the r(N - d + 1)-ball,
using the monotonicity of r for faces of still lower dimension. Glue all globally selected
compatible maps first. The characteristic sphere maps into its selected union, so composing that
sphere map with the continuous glued map gives continuous boundary data. Apply the bounded disk
extension helper to fill this boundary map inside the R(N - d + 1)-ball. Compose the filling with the
inverse regular characteristic homeomorphism to obtain a continuous closed-cell map with exactly
the glued boundary values. Its agreement with every selected lower intersecting cell follows
because such an intersection lies on the boundary. The uniform-ball extension choice refines this
comparison map to an admissible Q-map, and the recursive criterion selects the cell. Pairwise
compatibility identifies the selected map with the glued map on every boundary point. A nonempty
positive-dimensional frontier supplies an anchor in the r(N - d + 1)-ball; compare the selected map to
the constructed filling in Q to bound all its values by r(N - d + 1)+4R(N - d + 1), strictly below r(N - d).
This completes the induction, including all faces, not only open-cell points.

CS5. The shrinking-cell hypothesis gives δ>0 such that every closed cell meeting the δ-ball about
c is contained in B. The complement is covered by cells, so each complement point in that δ-ball
lies in a cell of Y and hence in the selected union. Moreover every selected cell meeting that
ball is itself a cell of Y, so its whole image lies in V by the preceding induction. This proves
both the local covering assertion and image control, including points lying on cell boundaries.

CS6. Restrict local finiteness of all closed cells to the selected index subtype; each cell is
closed in the Hausdorff complement. Compatible-cell gluing yields a total map fixing C and
continuous on the ambient selected union Z. This map is used to define sphere boundary data in the
induction, without requiring continuity at C in advance. Shrinking supplies a positive δ such that
all closed cells meeting its ambient ball lie in the small t-ball. The complement cell cover and
the induction give coverage by selected cells; applying the same induction to any selected cell
meeting that ball gives its image inside V. Thus the δ-ball lies in Z union C and every selected
point in it maps into V, exactly the stated conclusion.
-/
theorem hatcher_controlled_partial_retraction_cell_selection
    (N : ℕ) (hN : 0 < N) (C : Set (EuclideanSpace ℝ (Fin N)))
    (hC : IsCompact C) (hne : C.Nonempty) (_hsub : ¬ C.Subsingleton)
    (hlocal : ∀ (c : C) (O : Set C), IsOpen O → c ∈ O →
      ∃ V : Set C, IsOpen V ∧ c ∈ V ∧
        ∃ hVO : V ⊆ O, (ContinuousMap.inclusion hVO).Nullhomotopic) :
    ∃ (Z : Set (EuclideanSpace ℝ (Fin N))) (r : EuclideanSpace ℝ (Fin N) → C),
      ContinuousOn r Z ∧ (∀ c : C, r c = c) ∧
      ∀ c : C, ∀ V : Set C, IsOpen V → c ∈ V →
        ∃ δ : ℝ, 0 < δ ∧ Metric.ball c.val δ ⊆ Z ∪ C ∧
          ∀ z ∈ Z, dist z c.val < δ → r z ∈ V := by
  obtain ⟨nearest, hnearest_fix, hnearest_control⟩ :=
    nearest_point_factor_two_lt N C hC hne
  have hnested (c : C) (R : ℝ) (hR : 0 < R) :=
    hatcher_nested_nullhomotopic_balls C hlocal c R hR
  obtain ⟨cw, hfinite, hdim, hfaces, hregular, hboundary, hshrink⟩ :=
    hatcher_dyadic_complement_shrinking_cw N hN C hC
  let : Topology.CWComplex (Set.univ : Set {x : EuclideanSpace ℝ (Fin N) // x ∉ C}) := cw
  have hcoverage (c : C) (ε : ℝ) (hε : 0 < ε) :=
    hatcher_shrinking_cells_neighborhood C c.val ε hε (hshrink c.val c.property)
  classical
  let X := {x : EuclideanSpace ℝ (Fin N) // x ∉ C}
  let Cell := Σ d : ℕ, Topology.RelCWComplex.cell (Set.univ : Set X) d
  let A : Cell → Set X := fun j ↦
    Topology.RelCWComplex.closedCell (C := (Set.univ : Set X)) j.1 j.2
  let B : Cell → Set X := fun j ↦
    Topology.RelCWComplex.cellFrontier (C := (Set.univ : Set X)) j.1 j.2
  have hinter (i j : Cell) (hij : i ≠ j) (hd : j.1 ≤ i.1) :
      A i ∩ A j ⊆ B i := by
    intro x hx
    have hi : x ∈ B i ∪ Topology.RelCWComplex.openCell i.1 i.2 := by
      rw [Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell]
      exact hx.1
    rcases hi with hi | hi
    · exact hi
    have hj : x ∈ B j ∪ Topology.RelCWComplex.openCell j.1 j.2 := by
      rw [Topology.RelCWComplex.cellFrontier_union_openCell_eq_closedCell]
      exact hx.2
    rcases hj with hj | hj
    · have hsk := Topology.RelCWComplex.cellFrontier_subset_skeletonLT j.1 j.2 hj
      exact False.elim ((Set.disjoint_left.mp
        (Topology.RelCWComplex.disjoint_skeletonLT_openCell
          (show (j.1 : ℕ∞) ≤ i.1 by exact_mod_cast hd))) hsk hi)
    · exact False.elim ((Set.disjoint_left.mp
        (Topology.RelCWComplex.disjoint_openCell_of_ne hij)) hi hj)
  have hface_cover (i : Cell) (x : X) (hx : x ∈ B i) :
      ∃ k : Cell, k.1 < i.1 ∧ A k ⊆ B i ∧ x ∈ A k := by
    obtain ⟨F, hFdim, hF⟩ := hboundary i.1 i.2
    change x ∈ Topology.RelCWComplex.cellFrontier i.1 i.2 at hx
    rw [hF] at hx
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hx
    refine ⟨k, hFdim k hk, ?_, hxk⟩
    intro y hy
    change y ∈ Topology.RelCWComplex.cellFrontier i.1 i.2
    rw [hF]
    exact Set.mem_iUnion₂.mpr ⟨k, hk, hy⟩
  -- The map property is independent of the center and neighborhood later used
  -- to verify local control. All choices are made once by dimension recursion.
  let Q (i : Cell) (g : C(A i, C)) : Prop :=
    (i.1 = 0 → ∀ x : A i, g x = nearest x.val.val) ∧
    (0 < i.1 → ∀ (c : C) (r R : ℝ), 0 ≤ R →
      (∃ x : A i, x.val ∈ B i ∧ dist (g x) c < r) →
      (∃ h : C(A i, C), (∀ x : A i, x.val ∈ B i → h x = g x) ∧
        ∀ x, dist (h x) c < R) → ∀ x, dist (g x) c < r + 4 * R)
  obtain ⟨J, f, hquality, hcompat, hcriterion⟩ :=
    hatcher_recursive_cell_selection A B (fun i : Cell ↦ i.1) Q hinter hface_cover
  have hvertices (i : Cell) (hi : i.1 = 0) : i ∈ J := by
    rcases i with ⟨d, i⟩
    change d = 0 at hi
    subst d
    apply (hcriterion ⟨0, i⟩).mpr
    refine ⟨?_, ?_⟩
    · intro k hk
      exact (Nat.not_lt_zero k.1 hk).elim
    · obtain ⟨x₀, hx₀⟩ := Topology.RelCWComplex.closedCell_nonempty 0 i
      let g : C(A ⟨0, i⟩, C) := ContinuousMap.const _ (nearest x₀.val)
      have hsingle : (A ⟨0, i⟩).Subsingleton := by
        change (Topology.RelCWComplex.closedCell 0 i).Subsingleton
        rw [Topology.RelCWComplex.closedCell_zero_eq_singleton]
        exact Set.subsingleton_singleton
      refine ⟨g, ⟨?_, ?_⟩, ?_⟩
      · intro _ x
        have hx : x.val = x₀ := hsingle x.property hx₀
        change nearest x₀.val = nearest x.val.val
        rw [hx]
      · intro hpos
        exact (Nat.not_lt_zero 0 hpos).elim
      · intro k hk
        exact (Nat.not_lt_zero k.val.1 hk).elim
  have hrefine (i : Cell) (hi : 0 < i.1) (g₀ : C(A i, C)) :
      ∃ g : C(A i, C), Q i g ∧
        ∀ x : A i, x.val ∈ B i → g x = g₀ x := by
    let boundary : Set (A i) := {x | x.val ∈ B i}
    have hboundary_ne : boundary.Nonempty := by
      obtain ⟨x, hx⟩ := Topology.RelCWComplex.nonempty_cellFrontier
        (Nat.ne_of_gt hi) i.2
      exact ⟨⟨x, Topology.RelCWComplex.cellFrontier_subset_closedCell i.1 i.2 hx⟩, hx⟩
    let : CompactSpace (A i) := isCompact_iff_compactSpace.mp
      Topology.RelCWComplex.isCompact_closedCell
    let b : C(boundary, C) := g₀.comp ⟨Subtype.val, continuous_subtype_val⟩
    obtain ⟨g, hg, _, hball⟩ := hatcher_controlled_extension_uniform_ball
      boundary hboundary_ne b ⟨g₀, fun _ ↦ rfl⟩
    have hagree (x : A i) (hx : x.val ∈ B i) : g x = g₀ x := hg ⟨x, hx⟩
    refine ⟨g, ⟨?_, ?_⟩, hagree⟩
    · intro hz
      exact (Nat.ne_of_gt hi hz).elim
    · intro _ c r R hR hanchor hcomp x
      apply hball c r R hR ?_ ?_ x
      · obtain ⟨a, ha, hadist⟩ := hanchor
        refine ⟨⟨a, ha⟩, ?_⟩
        change dist (g₀ a) c < r
        rwa [hagree a ha] at hadist
      · obtain ⟨h, hh, hsmall⟩ := hcomp
        refine ⟨h, ?_, hsmall⟩
        intro a
        exact (hh a.val a.property).trans (hagree a.val a.property)
  have hselect_extension (i : Cell) (hi : 0 < i.1)
      (hready : ∀ k : Cell, k.1 < i.1 → A k ⊆ B i → k ∈ J)
      (g₀ : C(A i, C))
      (hgood : ∀ k : J, k.val.1 < i.1 →
        ∀ x (hx : x ∈ A i) (hk : x ∈ A k.val),
          g₀ ⟨x, hx⟩ = f k ⟨x, hk⟩) : i ∈ J := by
    obtain ⟨g, hgQ, hagree⟩ := hrefine i hi g₀
    apply (hcriterion i).mpr
    refine ⟨hready, g, hgQ, ?_⟩
    intro k hk x hx hxk
    have hne : i ≠ k.val := by
      intro heq
      have heqdim := congrArg Sigma.fst heq
      exact (Nat.ne_of_gt hk) heqdim
    exact (hagree ⟨x, hx⟩ (hinter i k.val hne hk.le ⟨hx, hxk⟩)).trans
      (hgood k hk x hx hxk)
  -- Source p.526: induct on the dimension of cells contained in a sufficiently
  -- small ball. At dimension zero use nearest-point values. At the next stage
  -- the finite boundary cover pastes the earlier maps. Its nullhomotopy fills
  -- a characteristic disk; the uniform-ball extension choice yields Q. The
  -- selection criterion then includes the cell. Q and the nested-radius margin
  -- control its whole image. Shrinking cells finally supplies the ambient δ.
  have hlf : LocallyFinite (fun j : J ↦ A j.val) :=
    hfinite.comp_injective Subtype.val_injective
  have hcl (j : J) : IsClosed (A j.val) :=
    Topology.RelCWComplex.isClosed_closedCell
  obtain ⟨rglobal, hrcont, hrfix, hrpiece⟩ :=
    hatcher_compatible_cell_gluing C hne (fun j : J ↦ A j.val) hlf hcl f hcompat
  have hcontrol : ∀ (c : C) (V : Set C), IsOpen V → c ∈ V →
      ∃ δ : ℝ, 0 < δ ∧
        (∀ x : X, dist x.val c.val < δ → ∃ j : J, x ∈ A j.val) ∧
        ∀ (j : J) (x : A j.val), dist x.val.val c.val < δ → f j x ∈ V := by
    intro c V hV hcV
    obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV c hcV
    obtain ⟨radii, outer, houter, hradii, hstep⟩ := hnested c ε hε
    have hltε : ∀ n, radii n < ε := by
      intro n
      induction n with
      | zero => simpa [houter] using (hradii 0).2.1
      | succ n ih =>
          have hs := hstep n
          have hdec : radii (n + 1) < radii n := by
            have hp := (hradii (n + 1)).1.trans (hradii (n + 1)).2.1
            linarith
          exact hdec.trans ih
    have hanti : Antitone radii := by
      apply antitone_nat_of_succ_le
      intro n
      have hp := (hradii (n + 1)).1.trans (hradii (n + 1)).2.1
      have hs := hstep n
      linarith
    let t : ℝ := radii N / 2
    have ht : 0 < t := half_pos (hradii N).1
    obtain ⟨δ₀, hδ₀, hcover₀⟩ := hcoverage c t ht
    obtain ⟨δ₁, hδ₁, hshrink₁⟩ := hshrink c.val c.property t ht
    let δ : ℝ := min δ₀ δ₁
    have hδ : 0 < δ := lt_min hδ₀ hδ₁
    have hcell : ∀ d (i : Topology.RelCWComplex.cell (Set.univ : Set X) d), d ≤ N →
        (∀ x : A ⟨d, i⟩, dist x.val.val c.val < t) →
        ∃ hi : (⟨d, i⟩ : Cell) ∈ J,
          ∀ x : A ⟨d, i⟩, f ⟨⟨d, i⟩, hi⟩ x ∈ Metric.ball c (radii (N - d)) := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
        intro i hd hsmall
        by_cases hd0 : d = 0
        · subst d
          have hiJ := hvertices ⟨0, i⟩ rfl
          refine ⟨hiJ, ?_⟩
          intro x
          rw [(hquality ⟨⟨0, i⟩, hiJ⟩).1 rfl x]
          exact hnearest_control x.val.val c (radii N) (hradii N).1 (hsmall x)
        have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
        let ic : Cell := ⟨d, i⟩
        have hlow (k : Cell) (hk : k.1 < d) (hkB : A k ⊆ B ic) :
            ∃ hkJ : k ∈ J, ∀ x : A k,
              dist (f ⟨k, hkJ⟩ x) c < radii (N - d + 1) := by
          have hksmall : ∀ x : A k, dist x.val.val c.val < t := by
            intro x
            exact hsmall ⟨x.val,
              Topology.RelCWComplex.cellFrontier_subset_closedCell d i (hkB x.property)⟩
          obtain ⟨hkJ, hkbound⟩ := ih k.1 hk k.2 (by omega) hksmall
          refine ⟨hkJ, fun x ↦ (hkbound x).trans_le (hanti (by omega))⟩
        have hready : ∀ k : Cell, k.1 < ic.1 → A k ⊆ B ic → k ∈ J := by
          intro k hk hkB
          exact (hlow k hk hkB).choose
        have hboundary_image (x : X) (hx : x ∈ B ic) :
            x.val ∈ Subtype.val '' ⋃ j : J, A j.val ∧
              dist (rglobal x.val) c < radii (N - d + 1) := by
          obtain ⟨k, hkd, hkB, hxk⟩ := hface_cover ic x hx
          obtain ⟨hkJ, hkb⟩ := hlow k hkd hkB
          refine ⟨⟨x, Set.mem_iUnion.mpr ⟨⟨k, hkJ⟩, hxk⟩, rfl⟩, ?_⟩
          rw [hrpiece ⟨k, hkJ⟩ ⟨x, hxk⟩]
          exact hkb ⟨x, hxk⟩
        let sm : sphere (0 : Fin d → ℝ) 1 → X :=
          fun s ↦ Topology.RelCWComplex.map d i s.val
        have hsmB (s : sphere (0 : Fin d → ℝ) 1) : sm s ∈ B ic :=
          ⟨s.val, s.property, rfl⟩
        have hsmcont : Continuous sm :=
          ((Topology.RelCWComplex.continuousOn d i).mono sphere_subset_closedBall).domRestrict
        let b : C(sphere (0 : Fin d → ℝ) 1, C) :=
          { toFun := fun s ↦ rglobal (sm s).val
            continuous_toFun := by
              apply continuousOn_univ.mp
              exact hrcont.comp (continuous_subtype_val.comp hsmcont).continuousOn
                (fun s _ ↦ (hboundary_image (sm s) (hsmB s)).1) }
        obtain ⟨hball, hnull⟩ := (hradii (N - d + 1)).2.2
        obtain ⟨F, hFbound, hF⟩ := hatcher_centered_boundary_extension_bound
          C c (radii (N - d + 1)) (outer (N - d + 1)) (hradii (N - d + 1)).1
          hball hnull (by omega) b
          (fun s ↦ (hboundary_image (sm s) (hsmB s)).2)
        obtain ⟨e, he⟩ := hregular d i
        let g : C(A ic, C) := ⟨fun x ↦ F (e.symm x), F.continuous.comp e.symm.continuous⟩
        have hg (x : A ic) (hx : x.val ∈ B ic) : g x = rglobal x.val.val := by
          obtain ⟨s, hs, hsx⟩ := hx
          have hex : e ⟨s, sphere_subset_closedBall hs⟩ = x := by
            apply Subtype.ext
            exact (he _).trans hsx
          change F (e.symm x) = _
          rw [← hex, e.symm_apply_apply, hF ⟨s, hs⟩]
          change rglobal (Topology.RelCWComplex.map d i s).val = _
          congr 1
          exact congrArg Subtype.val (he ⟨s, sphere_subset_closedBall hs⟩).symm
        have hgsmall : ∀ x : A ic, dist (g x) c < outer (N - d + 1) :=
          fun x ↦ hFbound (e.symm x)
        have hiJ : ic ∈ J := by
          apply hselect_extension ic hdpos hready g
          intro k hk x hx hxk
          have hne : ic ≠ k.val := by
            intro heq
            have := congrArg Sigma.fst heq
            omega
          rw [hg ⟨x, hx⟩ (hinter ic k.val hne hk.le ⟨hx, hxk⟩)]
          exact hrpiece k ⟨x, hxk⟩
        have hfg (x : A ic) (hx : x.val ∈ B ic) :
            g x = f ⟨ic, hiJ⟩ x := by
          rw [hg x hx, hrpiece ⟨ic, hiJ⟩ x]
        refine ⟨hiJ, ?_⟩
        intro x
        apply lt_trans (?_ : dist (f ⟨ic, hiJ⟩ x) c <
          radii (N - d + 1) + 4 * outer (N - d + 1)) (hstep (N - d))
        apply (hquality ⟨ic, hiJ⟩).2 hdpos c _ _
          ((hradii (N - d + 1)).1.trans (hradii (N - d + 1)).2.1).le
        · obtain ⟨y, hy⟩ := Topology.RelCWComplex.nonempty_cellFrontier hd0 i
          let y' : A ic := ⟨y, Topology.RelCWComplex.cellFrontier_subset_closedCell d i hy⟩
          refine ⟨y', hy, ?_⟩
          rw [← hrpiece ⟨ic, hiJ⟩ y']
          exact (hboundary_image y hy).2
        · exact ⟨g, hfg, hgsmall⟩
    refine ⟨δ, hδ, ?_, ?_⟩
    · intro x hx
      rcases hcover₀ x.val (Metric.mem_ball.mpr (lt_of_lt_of_le hx (min_le_left _ _))) with
        hxc | ⟨y, d, i, hy, hcellmem, hsmall⟩
      · exact (x.property hxc).elim
      have hd : d ≤ N := hdim d i
      have hAi : ∀ z : A ⟨d, i⟩, dist z.val.val c.val < t := by
        intro z
        exact hsmall z.val z.property
      obtain ⟨hj, _⟩ := hcell d i hd hAi
      refine ⟨⟨⟨d, i⟩, hj⟩, ?_⟩
      have hyx : y = x := Subtype.ext hy
      simpa [hyx] using hcellmem
    · intro j x hx
      have hxδ₁ : dist x.val.val c.val < δ₁ := lt_of_lt_of_le hx (min_le_right _ _)
      have hAj : ∀ z : A j.val, dist z.val.val c.val < t := by
        intro z
        exact hshrink₁ j.val.1 j.val.2 ⟨x.val, x.property, hxδ₁⟩ z z.property
      obtain ⟨hj, hjbound⟩ := hcell j.val.1 j.val.2 (hdim j.val.1 j.val.2) hAj
      have hbx := hjbound ⟨x.val, x.property⟩
      change f j x ∈ Metric.ball c (radii (N - j.val.1)) at hbx
      apply hεV
      exact Metric.mem_ball.mpr ((Metric.mem_ball.mp hbx).trans (hltε (N - j.val.1)))
  refine ⟨Subtype.val '' ⋃ j : J, A j.val, rglobal, hrcont, hrfix, ?_⟩
  intro c V hV hcV
  obtain ⟨δ, hδ, hcover, hsmall⟩ := hcontrol c V hV hcV
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro z hz
    by_cases hzC : z ∈ C
    · exact Or.inr hzC
    · obtain ⟨j, hj⟩ := hcover ⟨z, hzC⟩ hz
      exact Or.inl ⟨⟨z, hzC⟩, Set.mem_iUnion.mpr ⟨j, hj⟩, rfl⟩
  · rintro z ⟨x, hx, rfl⟩ hdist
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    rw [hrpiece j ⟨x, hj⟩]
    exact hsmall j ⟨x, hj⟩ hdist


end HolomorphicAnosov
