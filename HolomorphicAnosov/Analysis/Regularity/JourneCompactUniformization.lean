import Mathlib.Topology.Compactness.Compact
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation

/-- Uniformize local estimates on a compact set when increasing their constant
and decreasing their radius preserves them. Choose a finite subcover with local
constants C_i and radii r_i. The positive choices C=1+sum C_i and
r=(1+sum r_i^{-1})^{-1} dominate every C_i and lie below every r_i in that
subcover. Monotonicity transfers the corresponding local estimate at each
point. The same formulas cover the empty compact set. This is the finite-cover
step in the locally uniform constants of Journé (1988), pp.187–188. -/
theorem compact_uniformize_constants_radius
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsCompact S)
    (P : X → ℝ → ℝ → Prop)
    (hmono : ∀ x C D r s, C ≤ D → 0 < s → s ≤ r → P x C r → P x D s)
    (hlocal : ∀ x ∈ S, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ y ∈ U, P y C r) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ x ∈ S, P x C r := by
  classical
  choose U hU hx C r hC hr hP using fun x : S ↦ hlocal x.val x.property
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover U hU (by
    intro x hxS
    exact Set.mem_iUnion.mpr ⟨⟨x, hxS⟩, hx ⟨x, hxS⟩⟩)
  let C₀ := 1 + ∑ i ∈ t, C i
  let R := 1 + ∑ i ∈ t, (r i)⁻¹
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    have h := Finset.sum_nonneg (fun i (_ : i ∈ t) ↦ (hC i).le)
    linarith
  have hR : 0 < R := by
    dsimp [R]
    have h := Finset.sum_nonneg (fun i (_ : i ∈ t) ↦ inv_nonneg.mpr (hr i).le)
    linarith
  refine ⟨C₀, R⁻¹, hC₀, inv_pos.mpr hR, ?_⟩
  intro x hxS
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (ht hxS)
  obtain ⟨hi, hxi⟩ := Set.mem_iUnion.mp hxi
  have hCi : C i ≤ C₀ := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ t) ↦ (hC j).le) hi
    dsimp [C₀]
    linarith
  have hri : R⁻¹ ≤ r i := by
    rw [inv_le_comm₀ hR (hr i)]
    have h := Finset.single_le_sum
      (fun j (_ : j ∈ t) ↦ inv_nonneg.mpr (hr j).le) hi
    dsimp [R]
    linarith
  exact hmono x (C i) C₀ (r i) R⁻¹ hCi (inv_pos.mpr hR) hri (hP i x hxi)

end HolomorphicAnosov.JourneLeafPolynomialApproximation
