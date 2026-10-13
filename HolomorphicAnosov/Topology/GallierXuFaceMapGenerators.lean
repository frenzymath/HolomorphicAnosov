import HolomorphicAnosov.Topology.GallierXuQuotientDescent

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- Every side in the original triangle presentation has the label of two distinct
original vertices. This follows by reading the two finite list maps defining the
presentation and the triangle word; consecutive indices in Fin 3 are distinct. -/
lemma triangle_side_label_endpoints {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (f : Fin (trianglePresentation K o).length)
    (i : Fin ((trianglePresentation K o).get f).length) :
    ∃ u v : Fin N, u ≠ v ∧
      (((trianglePresentation K o).get f).get i).1 = edgeLabel u v := by
  have hf := List.get_mem (trianglePresentation K o) f
  simp only [trianglePresentation, List.mem_map] at hf
  obtain ⟨s, hs, heq⟩ := hf
  let t : Triangle K := ⟨s.val, by simpa [simplices] using s.property⟩
  have heq' : triangleWord t (o t) = (trianglePresentation K o).get f := heq
  have hi : ((trianglePresentation K o).get f).get i ∈ triangleWord t (o t) :=
    (congrArg (fun w : Word ↦ ((trianglePresentation K o).get f).get i ∈ w) heq').mpr
      (List.get_mem _ i)
  simp only [triangleWord, List.mem_map] at hi
  obtain ⟨j, hj, hjeq⟩ := hi
  refine ⟨(o t j).val, (o t (finRotate 3 j)).val, ?_, ?_⟩
  · intro h
    have hjrot : j = finRotate 3 j := (o t).injective (Subtype.ext h)
    fin_cases j <;> norm_num [finRotate_apply] at hjrot
  · exact congrArg Prod.fst hjeq.symm

/-- Prescribed native side values force a face map to preserve every literal edge
identification. Read distinct endpoints from the first original triangle side;
the second side has the same label, so both boundary formulas give the same
originalEdgePoint at the same parameter. -/
lemma face_map_eq_of_edgeIdentification {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (q : FaceDisks (trianglePresentation K o) → ↥(carrier K))
    (hside : ∀ (f : Fin (trianglePresentation K o).length)
      (i : Fin ((trianglePresentation K o).get f).length) (u v : Fin N) (t : ℝ),
      u ≠ v → t ∈ Icc (0 : ℝ) 1 →
      (((trianglePresentation K o).get f).get i).1 = edgeLabel u v →
      (q (f, sidePointDisk f i t) : Fin N → ℝ) = originalEdgePoint u v t)
    {x y : FaceDisks (trianglePresentation K o)}
    (hxy : edgeIdentification (trianglePresentation K o) x y) : q x = q y := by
  obtain ⟨i, j, t, ht, hl, hx, hy⟩ := hxy
  obtain ⟨u, v, huv, hi⟩ := triangle_side_label_endpoints K o x.1 i
  have hxc : x = (x.1, sidePointDisk x.1 i t) := Prod.ext rfl (Subtype.ext hx)
  have hyc : y = (y.1, sidePointDisk y.1 j t) := Prod.ext rfl (Subtype.ext hy)
  apply Subtype.ext
  calc
    (q x : Fin N → ℝ) = (q (x.1, sidePointDisk x.1 i t) : Fin N → ℝ) :=
      congrArg (fun z ↦ (q z : Fin N → ℝ)) hxc
    _ = originalEdgePoint u v t := hside x.1 i u v t huv ht hi
    _ = (q (y.1, sidePointDisk y.1 j t) : Fin N → ℝ) :=
      (hside y.1 j u v t huv ht (hl.symm.trans hi)).symm
    _ = (q y : Fin N → ℝ) :=
      congrArg (fun z ↦ (q z : Fin N → ℝ)) hyc.symm

/-- Native side values propagate equality along the generated edge relation:
apply the preceding generator calculation, then equality's reflexivity,
symmetry and transitivity to the four EqvGen constructors. -/
lemma face_map_eq_of_eqvGen {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (q : FaceDisks (trianglePresentation K o) → ↥(carrier K))
    (hside : ∀ (f : Fin (trianglePresentation K o).length)
      (i : Fin ((trianglePresentation K o).get f).length) (u v : Fin N) (t : ℝ),
      u ≠ v → t ∈ Icc (0 : ℝ) 1 →
      (((trianglePresentation K o).get f).get i).1 = edgeLabel u v →
      (q (f, sidePointDisk f i t) : Fin N → ℝ) = originalEdgePoint u v t)
    {x y : FaceDisks (trianglePresentation K o)}
    (hxy : Relation.EqvGen (edgeIdentification (trianglePresentation K o)) x y) :
    q x = q y := by
  induction hxy with
  | rel x y h => exact face_map_eq_of_edgeIdentification K o q hside h
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- For a face map with native side values only the geometric-to-generated
fibre implication remains to be checked: the reverse implication is forced by
the original triangle side labels. Apply the canonical side descent theorem
using the preceding EqvGen calculation for that reverse implication. -/
theorem triangle_comparison_of_fibre_inclusion {N : ℕ}
    (K : AbstractSimplicialComplex (Fin N))
    (o : (s : Triangle K) → Fin 3 ≃ ↥s.val)
    (q : FaceDisks (trianglePresentation K o) → ↥(carrier K))
    (hq : Continuous q) (hsurj : Function.Surjective q)
    (hfib : ∀ x y, q x = q y →
      Relation.EqvGen (edgeIdentification (trianglePresentation K o)) x y)
    (hside : ∀ (f : Fin (trianglePresentation K o).length)
      (i : Fin ((trianglePresentation K o).get f).length) (u v : Fin N) (t : ℝ),
      u ≠ v → t ∈ Icc (0 : ℝ) 1 →
      (((trianglePresentation K o).get f).get i).1 = edgeLabel u v →
      (q (f, sidePointDisk f i t) : Fin N → ℝ) = originalEdgePoint u v t) :
    ∃ H : ↥(carrier K) ≃ₜ Realization (trianglePresentation K o),
      OriginalParameters K o H := by
  apply triangle_comparison_of_canonical_sides K o q hq hsurj _ hside
  intro x y
  exact ⟨hfib x y, face_map_eq_of_eqvGen K o q hside⟩

end HolomorphicAnosov.Topology.GallierXu
