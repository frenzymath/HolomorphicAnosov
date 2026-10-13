import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Category.TopPair

/-!
# A compact support and the displacement homotopy of topological pairs

Source: Dold, Fixed point index and fixed point theorem for Euclidean neighborhood
retracts (1965), Proposition 1.7, printed p.2. The native pair homotopy is the
displacement deformation in the published proof.
-/

noncomputable section
open CategoryTheory Set TopologicalSpace
namespace HolomorphicAnosov

/-- Compact total fixed locus yields one compact ambient support and displacement
maps from its complement pair that are homotopic as actual topological pair maps.

Source: Dold Proposition 1.7, p.2. Project the total fixed locus to the Euclidean
space to obtain L. Its image is compact and contained in U. At every time,
vanishing displacement would put the point in L, so displacement maps U minus L
into the complement of zero. Bundle the ambient displacement deformation and its
subspace restriction as continuous homotopies. Both endpoints and their square
with the subspace inclusions agree pointwise. This supplies Dold's fixed-pair
deformation without assuming a homology equality or an index law. Empty U and
dimension zero are allowed; in dimension zero the complement of L is empty. -/
theorem euclidean_displacement_pair_homotopy
    {n : ℕ} {U : Opens (EuclideanSpace ℝ (Fin n))}
    (H : C(U × unitInterval, EuclideanSpace ℝ (Fin n)))
    (hH : IsCompact {p : U × unitInterval | H p = p.1.1}) :
    ∃ L : Set (EuclideanSpace ℝ (Fin n)), IsCompact L ∧ L ⊆ (U : Set _) ∧
      (∀ (t : unitInterval) (x : U), H (x,t) = x.val → x.val ∈ L) ∧
      ∃ d : unitInterval →
        (TopPair.ofSubset (X := TopCat.of U) {x : U | x.val ∉ L} ⟶
          TopPair.ofSubset (X := TopCat.of (EuclideanSpace ℝ (Fin n))) ({0} : Set _)ᶜ),
        (∀ (t : unitInterval) (x : U), TopPair.Hom.fst (d t) x = x.val - H (x,t)) ∧
        Nonempty (TopPair.Homotopy (d 0) (d 1)) := by
  let L : Set (EuclideanSpace ℝ (Fin n)) :=
    (fun p : U × unitInterval ↦ p.1.val) '' {p | H p = p.1.1}
  have hL : IsCompact L := hH.image_of_continuousOn
    (continuous_subtype_val.comp continuous_fst).continuousOn
  have hLU : L ⊆ (U : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    exact p.1.property
  have hn (t : unitInterval) (x : U) (hx : x.val ∉ L) : x.val - H (x,t) ≠ 0 := by
    intro hz
    exact hx ⟨(x,t), (sub_eq_zero.mp hz).symm, rfl⟩
  let P := TopPair.ofSubset (X := TopCat.of U) {x : U | x.val ∉ L}
  let Q := TopPair.ofSubset (X := TopCat.of (EuclideanSpace ℝ (Fin n))) ({0} : Set _)ᶜ
  let D (t : unitInterval) : C(U, EuclideanSpace ℝ (Fin n)) :=
    ⟨fun x ↦ x.val - H (x,t), continuous_subtype_val.sub
      (H.continuous.comp (continuous_id.prodMk continuous_const))⟩
  let d (t : unitInterval) : P ⟶ Q :=
    TopPair.ofHom (TopCat.ofHom (D t))
      (TopCat.ofHom
        ⟨fun x ↦ ⟨x.val.val - H (x.val,t), hn t x.val x.property⟩,
          ((D t).continuous.comp continuous_subtype_val).subtype_mk _⟩) (by rfl)
  refine ⟨L, hL, hLU, fun t x hx ↦ ⟨(x,t), hx, rfl⟩,
    d, fun _ _ ↦ rfl, ⟨?_⟩⟩
  exact
    { fst :=
        { toFun := fun p ↦ p.2.val - H (p.2,p.1)
          continuous_toFun := (continuous_subtype_val.comp continuous_snd).sub
            (H.continuous.comp (continuous_snd.prodMk continuous_fst))
          map_zero_left := fun _ ↦ rfl
          map_one_left := fun _ ↦ rfl }
      snd :=
        { toFun := fun p ↦ ⟨p.2.val.val - H (p.2.val,p.1), hn p.1 p.2.val p.2.property⟩
          continuous_toFun :=
            ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)).sub
              (H.continuous.comp
                ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst))).subtype_mk _
          map_zero_left := fun _ ↦ rfl
          map_one_left := fun _ ↦ rfl }
      w := by ext p; rfl }

end HolomorphicAnosov
