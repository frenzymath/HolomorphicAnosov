import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.UnitInterval

/-!
# Normality from interval-valued closed-set extension

Source: Fritsch--Piccinini, *Cellular Structures in Topology* (1990),
Appendix A.4.8(iv), pp. 260--261.  The source proves normality from the
ability to extend interval-valued maps on closed subsets; this file records
that reusable converse separately from any CW induction.
DAG node: `topo.normality_of_interval_extension_g10`.
-/

namespace HolomorphicAnosov.Topology

universe u

/--
If every continuous map from a closed subtype into the unit interval extends
continuously, then the space is normal.

Source: Fritsch–Piccinini, Appendix A.4.8(iv), pp.260–261, invokes the Tietze
converse. The following is the explicit elementary expansion of that invocation.
For disjoint closed sets s,t, their union C is closed, and s is clopen in C
because its complement there is t. Its piecewise map, zero on s and one on t,
is continuous since the clopen partition has empty frontier. Extend it to F on X.
The inverse images of the relative interval rays below 1/3 and above 2/3 are open,
contain s and t respectively, and are disjoint by the order inequality 1/3≤2/3.
These sets prove normality. No T1, Hausdorff or nonemptiness assumption is used.
-/
theorem normalSpace_of_unitInterval_extension
    {X : Type u} [TopologicalSpace X]
    (hExtend : ∀ (C : Set X) (_hC : IsClosed C)
      (f : C(C, unitInterval)),
      ∃ F : C(X, unitInterval), ∀ x : C, F x = f x) :
    NormalSpace X := by
  classical
  constructor
  intro s t hs ht hst
  let C : Set X := s ∪ t
  have hC : IsClosed C := hs.union ht
  let u : Set C := {x | (x : X) ∈ s}
  have hu_closed : IsClosed u := hs.preimage continuous_subtype_val
  have hu_compl : uᶜ = {x : C | (x : X) ∈ t} := by
    ext x
    constructor
    · intro hx
      have hxC : (x : X) ∈ C := x.property
      rcases hxC with hxs | hxt
      · exact (hx hxs).elim
      · exact hxt
    · intro hxt hxs
      exact (hst.le_bot ⟨hxs, hxt⟩).elim
  have hu_open : IsOpen u := by
    rw [← isClosed_compl_iff, hu_compl]
    exact ht.preimage continuous_subtype_val
  have hfront : frontier u = ∅ := (show IsClopen u from ⟨hu_closed, hu_open⟩).frontier_eq
  let z : C → unitInterval := Set.piecewise u (fun _ ↦ (0 : unitInterval))
    (fun _ ↦ (1 : unitInterval))
  have hz_cont : Continuous z := by
    apply continuous_piecewise (s := u) (fun x hx ↦ by simp [hfront] at hx)
    · exact continuous_const.continuousOn
    · exact continuous_const.continuousOn
  let f : C(C, unitInterval) := ⟨z, hz_cont⟩
  obtain ⟨F, hF⟩ := hExtend C hC f
  let a : unitInterval := ⟨(1 / 3 : ℝ), by norm_num⟩
  let b : unitInterval := ⟨(2 / 3 : ℝ), by norm_num⟩
  let U : Set X := F ⁻¹' Set.Iio a
  let V : Set X := F ⁻¹' Set.Ioi b
  refine ⟨U, V, isOpen_Iio.preimage F.continuous,
    isOpen_Ioi.preimage F.continuous, ?_, ?_, ?_⟩
  · intro x hxs
    have hx : (⟨x, Or.inl hxs⟩ : C) ∈ u := hxs
    have hval : F x = 0 := by
      simpa [f, z, Set.piecewise, hx] using hF ⟨x, Or.inl hxs⟩
    change F x < a
    rw [hval]
    change (0 : ℝ) < 1 / 3
    norm_num
  · intro x hxt
    have hx : (⟨x, Or.inr hxt⟩ : C) ∉ u := by
      intro hxs
      exact hst.le_bot ⟨hxs, hxt⟩ |>.elim
    have hval : F x = 1 := by
      simpa [f, z, Set.piecewise, hx] using hF ⟨x, Or.inr hxt⟩
    change F x > b
    rw [hval]
    change (2 / 3 : ℝ) < 1
    norm_num
  · rw [Set.disjoint_left]
    intro x hxU hxV
    exact (not_lt_of_ge (show a ≤ b by
      change (1 / 3 : ℝ) ≤ 2 / 3
      norm_num)) (lt_trans hxV hxU)

end HolomorphicAnosov.Topology

