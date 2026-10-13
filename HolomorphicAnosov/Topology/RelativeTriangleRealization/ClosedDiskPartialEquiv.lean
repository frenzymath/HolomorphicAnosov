import Mathlib.Topology.CWComplex.Classical.Finite
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
open Set Topology _root_.Topology Metric
namespace HolomorphicAnosov
universe u

/-- Packaging a characteristic disk map as the exact PartialEquiv required
by Mathlib's classical CW constructor. The forward map agrees on the whole
closed disk, not just on its interior; the inverse is continuous on the cell.

This scratch theorem is an implementation lemma for Hatcher Appendix p.519,
not a separately published theorem. Proof: Extend the disk map by its value
at the center outside the disk. Restrict it to the open ball. The given
embedding identifies the open ball homeomorphically with its range. Extend
that homeomorphism's inverse by zero outside the range. These two extensions
are inverse precisely on the open ball and the cell. Their restricted
continuity follows from the original disk map and the inverse homeomorphism.
This includes dimension zero, whose sphere is empty and whose open and closed
balls both consist of the unique point. -/
theorem closedDiskPartialEquiv {X : Type*} [TopologicalSpace X] (n : ℕ)
    (χ : C(closedBall (0 : Fin n → ℝ) 1, X))
    (hemb : IsEmbedding (fun t : ball (0 : Fin n → ℝ) 1 ↦
      χ ⟨t.val, ball_subset_closedBall t.property⟩)) :
    ∃ e : PartialEquiv (Fin n → ℝ) X,
      e.source = ball 0 1 ∧
      (∀ t : closedBall (0 : Fin n → ℝ) 1, e t.val = χ t) ∧
      ContinuousOn e (closedBall 0 1) ∧ ContinuousOn e.symm e.target := by
  classical
  let f : ball (0 : Fin n → ℝ) 1 → X :=
    fun t ↦ χ ⟨t.val, ball_subset_closedBall t.property⟩
  let H : ball (0 : Fin n → ℝ) 1 ≃ₜ range f := hemb.toHomeomorph
  let center : closedBall (0 : Fin n → ℝ) 1 := ⟨0, by simp⟩
  let F (t : Fin n → ℝ) : X :=
    if ht : t ∈ closedBall 0 1 then χ ⟨t, ht⟩ else χ center
  let G (x : X) : Fin n → ℝ :=
    if hx : x ∈ range f then (H.symm ⟨x, hx⟩).val else 0
  have hF (t : closedBall (0 : Fin n → ℝ) 1) : F t.val = χ t := by
    simp only [F, dite_eq_left t.property]
  have hFt (t : ball (0 : Fin n → ℝ) 1) : F t.val = f t :=
    hF ⟨t.val, ball_subset_closedBall t.property⟩
  have hG (x : range f) : G x.val = (H.symm x).val := by
    simp only [G, dite_eq_left x.property]
  have hGF (t : ball (0 : Fin n → ℝ) 1) : G (F t.val) = t.val := by
    rw [hFt]
    change G (H t).val = t.val
    rw [hG, H.symm_apply_apply]
  let e : PartialEquiv (Fin n → ℝ) X := {
    toFun := F
    invFun := G
    source := ball 0 1
    target := range f
    map_source' := fun t ht ↦ by rw [hFt ⟨t, ht⟩]; exact ⟨⟨t, ht⟩, rfl⟩
    map_target' := fun x hx ↦ by rw [hG ⟨x, hx⟩]; exact (H.symm ⟨x,hx⟩).property
    left_inv' := fun t ht ↦ hGF ⟨t, ht⟩
    right_inv' := fun x hx ↦ by
      rw [hG ⟨x,hx⟩, hFt]
      exact congrArg Subtype.val (H.apply_symm_apply ⟨x,hx⟩) }
  refine ⟨e, rfl, hF, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun t : closedBall (0 : Fin n → ℝ) 1 ↦ F t.val)
    convert χ.continuous using 1
    funext t
    exact hF t
  · rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun x : range f ↦ G x.val)
    have hc := continuous_subtype_val.comp H.symm.continuous
    convert hc using 1
    funext x
    exact hG x

end HolomorphicAnosov
