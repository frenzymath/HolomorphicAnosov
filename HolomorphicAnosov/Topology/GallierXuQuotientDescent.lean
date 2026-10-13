import HolomorphicAnosov.Topology.GallierXuSidePointDisk
import Mathlib.Topology.Homeomorph.Lemmas

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- Quotient comparison from exact fibres on the original face disks.

Source: the two-map comparison in Lee, Proposition 6.14, p.173. A continuous
surjection on the finite union of compact disks descends through the generated
edge relation. The fibre equivalence makes the descended map bijective. Its
compact source and Hausdorff target make it a homeomorphism; its inverse obeys
the required formula on every original face-disk representative. No separation
assumption on the disk quotient is used. -/
theorem realization_homeomorph_of_fibres {P : Presentation}
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (q : FaceDisks P → X) (hq : Continuous q) (hsurj : Function.Surjective q)
    (hfib : ∀ x y, q x = q y ↔ Relation.EqvGen (edgeIdentification P) x y) :
    ∃ H : X ≃ₜ Realization P, ∀ x, H (q x) = project P x := by
  let g : Realization P → X := Quotient.lift q (fun x y h ↦ (hfib x y).mpr h)
  have hg : Continuous g := continuous_quot_lift _ hq
  have hbij : Function.Bijective g := by
    constructor
    · intro x y
      refine Quotient.inductionOn₂ x y ?_
      intro a b hab
      exact Quotient.sound ((hfib a b).mp hab)
    · intro x
      obtain ⟨a, rfl⟩ := hsurj x
      exact ⟨project P a, rfl⟩
  let : CompactSpace Disk := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : ℂ) 1)
  let e : Realization P ≃ X := Equiv.ofBijective g hbij
  let H : Realization P ≃ₜ X := hg.homeoOfEquivCompactToT2 (f := e)
  refine ⟨H.symm, ?_⟩
  intro x
  exact H.symm_apply_apply (project P x)

/-- The quotient comparison satisfies OriginalParameters whenever the geometric
face map has the prescribed original edge values.

Source: the representative formula in Lee, Proposition 6.14, p.173 and the
prescribed boundary parameters in Gallier–Xu Proposition 3.2, p.31. Descend the
continuous surjection with exact generated-edge fibres. For a side representative
y and original carrier point x at the same edge parameter, the boundary formula
makes x = q y. The descended inverse therefore sends x to project y. -/
theorem triangle_comparison_of_face_map {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (q : FaceDisks (trianglePresentation K o) → ↥(carrier K))
    (hq : Continuous q) (hsurj : Function.Surjective q)
    (hfib : ∀ x y, q x = q y ↔
      Relation.EqvGen (edgeIdentification (trianglePresentation K o)) x y)
    (hside : ∀ (y : FaceDisks (trianglePresentation K o))
      (i : Fin ((trianglePresentation K o).get y.1).length) (u v : Fin N) (t : ℝ),
      u ≠ v → t ∈ Icc (0 : ℝ) 1 →
      (((trianglePresentation K o).get y.1).get i).1 = edgeLabel u v →
      (y.2 : ℂ) = sidePoint (trianglePresentation K o) y.1 i t →
      (q y : Fin N → ℝ) = originalEdgePoint u v t) :
    ∃ H : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o),
      OriginalParameters K o H := by
  obtain ⟨H, hH⟩ := realization_homeomorph_of_fibres q hq hsurj hfib
  refine ⟨H, ?_⟩
  intro x y i u v t huv ht hx hl hy
  have hxy : x = q y := Subtype.ext (hx.trans (hside y i u v t huv ht hl hy).symm)
  rw [hxy]
  exact hH y

/-- It suffices to check prescribed boundary values on canonical disk-side representatives.

Source: Gallier–Xu Proposition 3.2, p.31, with Lee Proposition 6.14, p.173.
Every representative whose coordinate equals a sidePoint is the corresponding
canonical sidePointDisk by subtype extensionality. Substitute that equality in
the canonical boundary formula and apply triangle_comparison_of_face_map. -/
theorem triangle_comparison_of_canonical_sides {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (q : FaceDisks (trianglePresentation K o) → ↥(carrier K))
    (hq : Continuous q) (hsurj : Function.Surjective q)
    (hfib : ∀ x y, q x = q y ↔
      Relation.EqvGen (edgeIdentification (trianglePresentation K o)) x y)
    (hside : ∀ (f : Fin (trianglePresentation K o).length)
      (i : Fin ((trianglePresentation K o).get f).length) (u v : Fin N) (t : ℝ),
      u ≠ v → t ∈ Icc (0 : ℝ) 1 →
      (((trianglePresentation K o).get f).get i).1 = edgeLabel u v →
      (q (f, sidePointDisk f i t) : Fin N → ℝ) = originalEdgePoint u v t) :
    ∃ H : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o),
      OriginalParameters K o H := by
  apply triangle_comparison_of_face_map K o q hq hsurj hfib
  intro y i u v t huv ht hl hy
  have hrep : y = (y.1, sidePointDisk y.1 i t) := by
    exact Prod.ext rfl (Subtype.ext hy)
  calc
    (q y : Fin N → ℝ) = (q (y.1, sidePointDisk y.1 i t) : Fin N → ℝ) :=
      congrArg (fun z ↦ (q z : Fin N → ℝ)) hrep
    _ = originalEdgePoint u v t := hside y.1 i u v t huv ht hl

end HolomorphicAnosov.Topology.GallierXu
