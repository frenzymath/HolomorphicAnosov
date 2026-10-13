import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import HolomorphicAnosov.Topology.CWComplex.CharacteristicContinuity
import Mathlib.Topology.CWComplex.Classical.Subcomplex
import Mathlib.Topology.Homotopy.Basic

namespace HolomorphicAnosov

universe u v

/-- The final composition in Hatcher's Proposition 0.16: a retraction of the cylinder
onto its bottom and the subcomplex cylinder extends any map already pasted there.
Source: Hatcher, *Algebraic Topology*, Chapter 0, p.14. -/
theorem cw_pair_extension_of_retraction
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [Topology.CWComplex (Set.univ : Set X)]
    (B : Topology.CWComplex.Subcomplex (Set.univ : Set X))
    (f : C(X, Y)) (h : C(unitInterval × (B : Set X), Y))
    (C : Set (unitInterval × X))
    (r : C(unitInterval × X, C)) (k : C(C, Y))
    (r_bottom : ∀ x : X, (r (0, x)).val = (0, x))
    (r_side : ∀ (t : unitInterval) (b : (B : Set X)), (r (t, b.val)).val = (t, b.val))
    (k_bottom : ∀ (x : X) (hx : (0, x) ∈ C), k ⟨(0, x), hx⟩ = f x)
    (k_side : ∀ (t : unitInterval) (b : (B : Set X)) (hb : (t, b.val) ∈ C),
      k ⟨(t, b.val), hb⟩ = h (t, b)) :
    ∃ H : C(unitInterval × X, Y),
      (∀ x : X, H (0, x) = f x) ∧
      (∀ (t : unitInterval) (b : (B : Set X)), H (t, b.val) = h (t, b)) ∧
      ∀ (A : Topology.CWComplex.Subcomplex (Set.univ : Set X)) (hAB : A ≤ B),
        (∀ (t : unitInterval) (a : (A : Set X)),
          h (t, ⟨a.val, hAB a.property⟩) = f a.val) →
        ∀ (t : unitInterval) (a : (A : Set X)), H (t, a.val) = f a.val := by
  let H : C(unitInterval × X, Y) := ⟨fun z ↦ k (r z), k.continuous.comp r.continuous⟩
  have h_bottom (x : X) : H (0, x) = f x := by
    have hx : (0, x) ∈ C := r_bottom x ▸ (r (0, x)).property
    have heq : r (0, x) = ⟨(0, x), hx⟩ := Subtype.ext (r_bottom x)
    simpa [H, heq] using k_bottom x hx
  have h_side (t : unitInterval) (b : (B : Set X)) : H (t, b.val) = h (t, b) := by
    have hb : (t, b.val) ∈ C := r_side t b ▸ (r (t, b.val)).property
    have heq : r (t, b.val) = ⟨(t, b.val), hb⟩ := Subtype.ext (r_side t b)
    simpa [H, heq] using k_side t b hb
  refine ⟨H, h_bottom, h_side, ?_⟩
  intro A hAB h_fixed t a
  exact (h_side t ⟨a.val, hAB a.property⟩).trans (h_fixed t a)

end HolomorphicAnosov
