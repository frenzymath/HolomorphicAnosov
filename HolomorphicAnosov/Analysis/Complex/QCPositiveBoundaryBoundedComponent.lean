import HolomorphicAnosov.Topology.MarkedRectangleG3JordanSeparationSchoenflies
import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingConstant
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingOmittedPath
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount.LoopWindingEqOfIncrement
import HolomorphicAnosov.Analysis.Complex.LoopHomotopyOfNormSubLt

/-! # Positive winding selects the bounded Jordan component

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem*
(1951), pp.860--867, and Tao, 246A Notes 3, Theorem 50 and the
clockwise/anticlockwise convention following it.  The point of this helper
is to connect the project's explicit positive logarithm lift with the bounded
component supplied by Schoenflies. -/

namespace HolomorphicAnosov

open Set Analysis.MarkedRectangle
open scoped _root_.Topology

/-- A positive boundary parametrization of a bounded connected Jordan region
identifies that region with the bounded complementary component of its Jordan
curve.  The conclusion also supplies the ambient chart and its closure image,
which are the exact hypotheses used by `qc_confine_punctured_homotopy`.

The exterior winding argument is explicit: the exterior is open and connected,
so a point in it joins a point of arbitrarily large norm; a large constant loop
is joined to the boundary loop by the norm-small straight homotopy and has
winding zero.  Positive logarithm increments give winding one for points in
the region, ruling out the exterior component. -/
theorem qc_positive_boundary_bounded_component
    (Q : Set ℂ) (hQne : Q.Nonempty) (hQopen : IsOpen Q)
    (hQconn : IsConnected Q) (_hQbounded : Bornology.IsBounded Q)
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ)
    (hfrontier : frontier Q = range γ)
    (β : Circle ≃ₜ frontier Q)
    (hpositive : PositiveBoundaryParametrization Q β) :
    ∃ (E : ℂ ≃ₜ ℂ), E '' Q = Metric.ball (0 : ℂ) 1 ∧
      E '' closure Q = Metric.closedBall (0 : ℂ) 1 := by
  classical
  let γβ : ComplexLoop :=
    ⟨fun z : Circle ↦ (β z : ℂ), continuous_subtype_val.comp β.continuous⟩
  have hγβavoid (q : ℂ) (hq : q ∈ Q) : ∀ z, γβ z ≠ q := by
    intro z hz
    have hdis : Disjoint Q (frontier Q) :=
      (disjoint_frontier_iff_isOpen.mpr hQopen).symm
    have hz' : (β z : ℂ) = q := by simpa [γβ] using hz
    have hqfront : q ∈ frontier Q := by
      rw [← hz']
      exact (β z).property
    exact disjoint_left.mp hdis hq hqfront
  have hwind_pos (q : ℂ) (hq : q ∈ Q) : loopWinding γβ q (hγβavoid q hq) = 1 := by
    obtain ⟨_, _, L, hL, hinc⟩ := hpositive q hq
    apply loopWinding_eq_of_increment γβ q (hγβavoid q hq) L
    · intro t
      exact hL t
    · simpa using hinc
  obtain ⟨H, Q₀, E₀, hHc, hHQ₀, hHE₀, hQ₀ne, hE₀ne, hQ₀E₀ne,
      hcover, hdisj, hcomponents, hQ₀open, hE₀open, hQ₀conn, hE₀conn,
      hQ₀bounded, hE₀unbounded, hQ₀frontier, hE₀frontier, hclosure₀,
      _hext, _hcross⟩ :=
    markedRectangleG3JordanSeparationSchoenflies γ hγ
  have hQsubcomp (q : ℂ) (hq : q ∈ Q) :
      q ∈ (range γ)ᶜ := by
    rw [← hfrontier]
    intro hqf
    exact disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hQopen).symm hq hqf
  obtain ⟨q₀, hq₀⟩ := hQne
  have hcomponent_choice : connectedComponentIn (range γ)ᶜ q₀ = Q₀ ∨
      connectedComponentIn (range γ)ᶜ q₀ = E₀ := by
    have hm := Set.mem_image_of_mem
      (fun w : ℂ ↦ connectedComponentIn (range γ)ᶜ w) (hQsubcomp q₀ hq₀)
    simpa only [hcomponents, mem_insert_iff, mem_singleton_iff] using hm
  have hcomponent_Q₀ : connectedComponentIn (range γ)ᶜ q₀ = Q₀ := by
    rcases hcomponent_choice with h | h
    · exact h
    · exfalso
      have hEsub : Q ⊆ E₀ := by
        have hcomp : Q ⊆ connectedComponentIn (range γ)ᶜ q₀ := by
          apply hQconn.isPreconnected.subset_connectedComponentIn hq₀
          intro x hx
          exact hQsubcomp x hx
        simpa [h] using hcomp
      have hγβavoidE (y : ℂ) (hy : y ∈ E₀) : ∀ z, γβ z ≠ y := by
        intro z hz
        have hdisjE : Disjoint E₀ (frontier E₀) :=
          (disjoint_frontier_iff_isOpen.mpr hE₀open).symm
        have hz' : (β z : ℂ) = y := by simpa [γβ] using hz
        have hyfront : y ∈ frontier E₀ := by
          rw [hE₀frontier, ← hfrontier]
          rw [← hz']
          exact (β z).property
        exact disjoint_left.mp hdisjE hy hyfront
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp
        (isCompact_range γβ.continuous).isBounded
      have hnot : ¬ E₀ ⊆ Metric.closedBall (0 : ℂ) (2 * R + 1) := by
        intro hsub
        apply hE₀unbounded
        exact (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr ⟨2 * R + 1, hsub⟩
      obtain ⟨y, hyE, hybig⟩ := not_subset.mp hnot
      have hybig' : 2 * R + 1 < ‖y‖ := by
        have hdist : 2 * R + 1 < dist y 0 := by
          exact lt_of_not_ge (fun hle ↦ hybig (Metric.mem_closedBall.mpr hle))
        simpa [dist_zero_right] using hdist
      have hpathconn : IsPathConnected E₀ :=
        hE₀open.isConnected_iff_isPathConnected.mp hE₀conn
      have hjoin : JoinedIn E₀ q₀ y := hpathconn.joinedIn q₀ (hEsub hq₀) y hyE
      have hp : OmittedValuePath γβ q₀ y := by
        refine ⟨hjoin.somePath, ?_⟩
        intro t z
        exact hγβavoidE _ (hjoin.somePath_mem t) z |>.symm
      have hbound (z : Circle) : ‖γβ z‖ ≤ R := by
        simpa [dist_zero_right] using Metric.mem_closedBall.mp (hR ⟨z, rfl⟩)
      have hsmall (z : Circle) : ‖(constantLoop (0 : ℂ)) z - γβ z‖ <
          ‖γβ z - y‖ := by
        have htri := norm_add_le (y - γβ z) (γβ z)
        have htri' : ‖y‖ ≤ ‖y - γβ z‖ + ‖γβ z‖ := by
          convert htri using 1; ring_nf
        rw [norm_sub_rev] at htri'
        have hlow : 2 * R + 1 - R < ‖γβ z - y‖ := by
          linarith [htri', hbound z]
        dsimp [constantLoop]
        have hz0 : ‖(0 : ℂ) - γβ z‖ = ‖γβ z‖ := by simp
        rw [hz0]
        linarith [hbound z, hlow]
      have hh := loopHomotopyAvoids_of_norm_sub_lt γβ (constantLoop 0) y hsmall
      have hy0 : (0 : ℂ) ≠ y := by
        intro hzero
        have : ‖y‖ = 0 := by rw [← hzero]; simp
        have hR0 : 0 ≤ R := le_trans (norm_nonneg (γβ ⟨1, by simp⟩))
          (hbound ⟨1, by simp⟩)
        linarith
      have hconst : loopWinding (constantLoop (0 : ℂ)) y (fun _ ↦ hy0) = 0 :=
        loopWinding_constant 0 y hy0
      have hywind : loopWinding γβ y (hγβavoidE y hyE) = 0 := by
        exact (loopWinding_homotopy γβ (constantLoop 0) y
          (hγβavoidE y hyE) (fun _ ↦ hy0) hh).trans hconst
      have hqwind : loopWinding γβ q₀ (hγβavoid q₀ hq₀) =
          loopWinding γβ y (hγβavoidE y hyE) := loopWinding_omittedPath γβ q₀ y
          (hγβavoid q₀ hq₀) (hγβavoidE y hyE) hp
      rw [hwind_pos q₀ hq₀, hywind] at hqwind
      norm_num at hqwind
  have hQsubset : Q ⊆ Q₀ := by
    have hcomp : Q ⊆ connectedComponentIn (range γ)ᶜ q₀ := by
      apply hQconn.isPreconnected.subset_connectedComponentIn hq₀
      intro x hx
      exact hQsubcomp x hx
    simpa [hcomponent_Q₀] using hcomp
  have hQ₀subset : Q₀ ⊆ Q := by
    have hQ₀frontdisj : Disjoint Q₀ (frontier Q) := by
      have hdisj₀ : Disjoint Q₀ (frontier Q₀) :=
        (disjoint_frontier_iff_isOpen.mpr hQ₀open).symm
      rw [hfrontier, ← hQ₀frontier]
      exact hdisj₀
    let S : Set ℂ := Q₀ \ closure Q
    have hSopen : IsOpen S := hQ₀open.sdiff isClosed_closure
    have hcoverQS : Q₀ ⊆ Q ∪ S := by
      intro x hx
      by_cases hxcl : x ∈ closure Q
      · left
        by_cases hxQ : x ∈ Q
        · exact hxQ
        · exfalso
          apply (disjoint_left.mp hQ₀frontdisj hx)
          rw [hQopen.frontier_eq]
          exact ⟨hxcl, hxQ⟩
      · exact Or.inr ⟨hx, hxcl⟩
    rcases hQ₀conn.isPreconnected.subset_or_subset hQopen hSopen
      (disjoint_left.mpr fun x hxQ hxS ↦ hxS.2 (subset_closure hxQ)) hcoverQS with h | h
    · exact h
    · have hs := h (hQsubset hq₀)
      exact False.elim (hs.2 (subset_closure hq₀))
  have hQeq : Q = Q₀ := subset_antisymm hQsubset hQ₀subset
  refine ⟨H, ?_, ?_⟩
  · simpa [hQeq] using hHQ₀
  · rw [hQeq, hclosure₀]
    rw [image_union, hHQ₀, hHc]
    ext z
    simp [Metric.mem_closedBall, dist_zero_right]

end HolomorphicAnosov

