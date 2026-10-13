import Mathlib.Analysis.Complex.CoveringMap

open Set

namespace HolomorphicAnosov.Analysis.Complex

/-- Continuous logarithms on two open sets glue when their intersection is nonempty
and connected. Source: Conway, Functions of One Complex Variable II, Chapter 14
Lemma 5.4, p.49. Choose a point in the intersection and translate the second branch
by the difference of the two branch values at that point. The exponential of this
constant is one, so this remains a logarithm. Uniqueness of lifts of the exponential
covering makes the branches agree on the connected intersection. Open pasting then
gives the required logarithm on the union. -/
theorem continuous_logarithm_on_union
    {X : Type*} [TopologicalSpace X] {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : IsConnected (U ∩ V)) {g L₁ L₂ : X → ℂ}
    (hL₁ : ContinuousOn L₁ U) (he₁ : EqOn (_root_.Complex.exp ∘ L₁) g U)
    (hL₂ : ContinuousOn L₂ V) (he₂ : EqOn (_root_.Complex.exp ∘ L₂) g V) :
    ∃ L : X → ℂ, ContinuousOn L (U ∪ V) ∧
      EqOn (_root_.Complex.exp ∘ L) g (U ∪ V) := by
  classical
  obtain ⟨a, haU, haV⟩ := hUV.nonempty
  let c := L₁ a - L₂ a
  have hc : _root_.Complex.exp c = 1 := by
    dsimp [c]
    rw [_root_.Complex.exp_sub, show _root_.Complex.exp (L₁ a) =
      _root_.Complex.exp (L₂ a) from (he₁ haU).trans (he₂ haV).symm]
    exact div_self (_root_.Complex.exp_ne_zero _)
  let L₂' : X → ℂ := fun z ↦ L₂ z + c
  have hL₂' : ContinuousOn L₂' V := hL₂.add continuousOn_const
  have he₂' : EqOn (_root_.Complex.exp ∘ L₂') g V := by
    intro z hz
    change _root_.Complex.exp (L₂ z + c) = g z
    rw [_root_.Complex.exp_add, hc, mul_one]
    exact he₂ hz
  have hmatch : EqOn L₁ L₂' (U ∩ V) := by
    refine _root_.Complex.isCoveringMap_exp.eqOn_of_comp_eqOn hUV.isPreconnected
      (hL₁.mono inter_subset_left) (hL₂'.mono inter_subset_right) ?_ ⟨haU, haV⟩ ?_
    · intro z hz
      apply Subtype.ext
      exact (he₁ hz.1).trans (he₂' hz.2).symm
    · simp [L₂', c]
  let L := U.piecewise L₁ L₂'
  have hEq₁ : EqOn L L₁ U := by
    intro z hz
    exact piecewise_eq_of_mem U L₁ L₂' hz
  have hEq₂ : EqOn L L₂' V := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact (hEq₁ hzU).trans (hmatch ⟨hzU, hz⟩)
    · exact piecewise_eq_of_notMem U L₁ L₂' hzU
  refine ⟨L, (hL₁.congr hEq₁).union_of_isOpen (hL₂'.congr hEq₂) hU hV, ?_⟩
  intro z hz
  rcases hz with hz | hz
  · change _root_.Complex.exp (L z) = g z
    rw [hEq₁ hz]
    exact he₁ hz
  · change _root_.Complex.exp (L z) = g z
    rw [hEq₂ hz]
    exact he₂' hz

end HolomorphicAnosov.Analysis.Complex

