import HolomorphicAnosov.Analysis.Complex.QCRectangleHorizontalSides
import HolomorphicAnosov.Analysis.Complex.QCPartitionTwoPieceRigidity

namespace HolomorphicAnosov
open Set Analysis.MarkedRectangle

/-- A closed rectangle homeomorphism matching interiors and the four corners
preserves complete horizontal sides. The open-side theorem handles interior
side points; the two remaining endpoints are the prescribed corners. -/
theorem qc_closed_rectangle_horizontal_sides
    {a b A B : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (e : ClosedRectangle a b ≃ₜ ClosedRectangle A B)
    (hint : ∀ z, (e z : ℂ) ∈ OpenRectangle A B ↔ (z : ℂ) ∈ OpenRectangle a b)
    (hc : ∀ (i : Fin 4) (z : ClosedRectangle a b),
      (z : ℂ) = RectangleCorner a b i → (e z : ℂ) = RectangleCorner A B i) :
    (∀ z : ClosedRectangle a b, (z : ℂ) ∈ ClosedRectangleSide a b 0 →
      (e z : ℂ) ∈ ClosedRectangleSide A B 0) ∧
    (∀ z : ClosedRectangle a b, (z : ℂ) ∈ ClosedRectangleSide a b 2 →
      (e z : ℂ) ∈ ClosedRectangleSide A B 2) := by
  have hs := (Analysis.marked_rectangle_coordinate_sides ha hb hA hB e hint
    (hc 0 _ rfl) (hc 1 _ rfl) (hc 2 _ rfl) (hc 3 _ rfl)).2
  constructor
  · intro z hz
    change (z : ℂ).re ∈ Icc 0 a ∧ (z : ℂ).im ∈ ({0} : Set ℝ) at hz
    have hzim : (z : ℂ).im = 0 := hz.2
    have him : (e z : ℂ).im = 0 := by
      by_cases h0 : (z : ℂ).re = 0
      · have heq : (z : ℂ) = RectangleCorner a b 0 := Complex.ext h0 hzim
        exact congrArg Complex.im (hc 0 z heq)
      by_cases ha' : (z : ℂ).re = a
      · have heq : (z : ℂ) = RectangleCorner a b 1 :=
          Complex.ext (by simpa [RectangleCorner] using ha') (by simpa [RectangleCorner] using hzim)
        exact congrArg Complex.im (hc 1 z heq)
      exact (hs z ⟨lt_of_le_of_ne hz.1.1 (Ne.symm h0),lt_of_le_of_ne hz.1.2 ha'⟩).1 hzim
    exact ⟨(e z).property.1,him⟩
  · intro z hz
    change (z : ℂ).re ∈ Icc 0 a ∧ (z : ℂ).im ∈ ({b} : Set ℝ) at hz
    have hzim : (z : ℂ).im = b := hz.2
    have him : (e z : ℂ).im = B := by
      by_cases h0 : (z : ℂ).re = 0
      · have heq : (z : ℂ) = RectangleCorner a b 3 :=
          Complex.ext (by simpa [RectangleCorner] using h0) (by simpa [RectangleCorner] using hzim)
        simpa [RectangleCorner] using congrArg Complex.im (hc 3 z heq)
      by_cases ha' : (z : ℂ).re = a
      · have heq : (z : ℂ) = RectangleCorner a b 2 :=
          Complex.ext (by simpa [RectangleCorner] using ha') (by simpa [RectangleCorner] using hzim)
        simpa [RectangleCorner] using congrArg Complex.im (hc 2 z heq)
      exact (hs z ⟨lt_of_le_of_ne hz.1.1 (Ne.symm h0),lt_of_le_of_ne hz.1.2 ha'⟩).2 hzim
    exact ⟨(e z).property.1,him⟩

/-- A topological rectangle model recording complete a-side placement transfers
those placements to the conformal model with the same four marks. Compare the
two closure models. They match interiors by their bijections and match corners
by the marks, so their transition homeomorphism preserves horizontal sides.
Composing with the given topological model gives exactly the two side-aware
conformal clauses. Source: Lehto–Virtanen I.Lemma 4.2, p.25. -/
theorem qc_complete_a_sides_of_boundary_model
    {Q : Set ℂ} {p : Fin 4 → ℂ} {m M a b : ℝ} {flip : Bool}
    (hmod : HasMarkedConformalModulus Q p m) (ha : 0 < a) (hb : 0 < b)
    (k : ClosedRectangle a b ≃ₜ closure Q)
    (hkint : ∀ z, (k z : ℂ) ∈ Q ↔ (z : ℂ) ∈ OpenRectangle a b)
    (hkcorner : ∀ (i : Fin 4) (z : ClosedRectangle a b),
      (z : ℂ) = RectangleCorner a b i → (k z : ℂ) = p i)
    (hkbottom : ∀ z : ClosedRectangle a b, (z : ℂ) ∈ ClosedRectangleSide a b 0 →
      (k z : ℂ) ∈ ClosedRectangleSide M 1 (if flip then 2 else 0))
    (hktop : ∀ z : ClosedRectangle a b, (z : ℂ) ∈ ClosedRectangleSide a b 2 →
      (k z : ℂ) ∈ ClosedRectangleSide M 1 (if flip then 0 else 2)) :
    HasMarkedConformalModulusWithCompleteASides Q p m M flip := by
  obtain ⟨A,B,hA,hB,hm,F,Fi,hF,hFi,hbij,hmaps,hFiF,hFFi,E,hE,hp⟩ := hmod
  have hR : OpenRectangle A B ⊆ ClosedRectangle A B := by
    rw [← RectangleModelPreparation.closure_openRectangle hA hB]
    exact subset_closure
  have hEint (z : ClosedRectangle A B) : (E z : ℂ) ∈ Q ↔ (z : ℂ) ∈ OpenRectangle A B := by
    constructor
    · intro hz
      obtain ⟨w,hw,heq⟩ := hbij.surjOn hz
      have hh : E ⟨w,hR hw⟩ = E z := Subtype.ext ((hE _ hw).trans heq)
      exact (congrArg Subtype.val (E.injective hh)) ▸ hw
    · intro hz
      rw [hE z hz]
      exact hbij.mapsTo hz
  let e := E.trans k.symm
  have heint (z : ClosedRectangle A B) :
      (e z : ℂ) ∈ OpenRectangle a b ↔ (z : ℂ) ∈ OpenRectangle A B := by
    rw [← hkint (e z)]
    simpa [e] using hEint z
  have hecorner (i : Fin 4) (z : ClosedRectangle A B)
      (hz : (z : ℂ) = RectangleCorner A B i) :
      (e z : ℂ) = RectangleCorner a b i := by
    let w : ClosedRectangle a b := ⟨RectangleCorner a b i,RectangleModelPreparation.corner_mem ha hb i⟩
    have hh : E z = k w := Subtype.ext ((hp i z hz).trans (hkcorner i w rfl).symm)
    change (k.symm (E z) : ℂ) = _
    rw [hh,k.symm_apply_apply]
  obtain ⟨hbottom,htop⟩ := qc_closed_rectangle_horizontal_sides hA hB ha hb e heint hecorner
  refine ⟨A,B,hA,hB,hm,F,Fi,hF,hFi,hbij,hmaps,hFiF,hFFi,E,hE,hp,?_,?_⟩
  · intro z hz
    simpa [e] using hkbottom (e z) (hbottom z hz)
  · intro z hz
    simpa [e] using hktop (e z) (htop z hz)

end HolomorphicAnosov
