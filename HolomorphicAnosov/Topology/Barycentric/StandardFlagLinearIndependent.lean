import HolomorphicAnosov.Topology.Barycentric.StandardBarycenterCoordinate
import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.Finset.Max

namespace HolomorphicAnosov.BarycentricGeometry

/-- Barycenters of a finite strict chain of nonempty coordinate faces are linearly
independent. Agent-written direct-coordinate refinement of Schultz, Math 246A §I.2, Proposition 3, p.23. Remove the largest
face; a coordinate newly appearing in that face separates its barycenter from the
span of all earlier barycenters. Induct on the number of faces. -/
theorem standard_flag_linearIndependent {ι : Type*} [DecidableEq ι]
    (C : Finset (Finset ι))
    (hne : ∀ F ∈ C, F.Nonempty)
    (hchain : (C : Set (Finset ι)).Pairwise (fun F G ↦ F ⊂ G ∨ G ⊂ F)) :
    LinearIndepOn ℝ (fun F : Finset ι ↦
      (F.card : ℝ)⁻¹ • ∑ i ∈ F, (Pi.single i 1 : ι → ℝ)) (C : Set _) := by
  classical
  induction C using Finset.strongInductionOn with
  | _ C ih =>
    by_cases hC : C.Nonempty
    · obtain ⟨F, hF, hmax⟩ := C.exists_max_image Finset.card hC
      let D := C.erase F
      have hsub : D ⊆ C := Finset.erase_subset _ _
      have hsmall : D ⊂ C := Finset.erase_ssubset hF
      have hD := ih D hsmall (fun G hG ↦ hne G (hsub hG)) (hchain.mono hsub)
      have hlt : ∀ G ∈ D, G ⊂ F := by
        intro G hG
        rcases hchain (hsub hG) hF (Finset.mem_erase.mp hG).1 with h | h
        · exact h
        · exact False.elim ((not_lt_of_ge (hmax G (hsub hG))) (Finset.card_lt_card h))
      have hcoord : ∃ i ∈ F, ∀ G ∈ D, i ∉ G := by
        by_cases hDne : D.Nonempty
        · obtain ⟨G, hG, hGmax⟩ := D.exists_max_image Finset.card hDne
          obtain ⟨i, hi, hni⟩ := Finset.exists_of_ssubset (hlt G hG)
          refine ⟨i, hi, fun H hH hiH ↦ hni ?_⟩
          by_cases hHG : H = G
          · simpa [hHG] using hiH
          · rcases hchain (hsub hH) (hsub hG) hHG with h | h
            · exact h.subset hiH
            · exact False.elim ((not_lt_of_ge (hGmax H hH)) (Finset.card_lt_card h))
        · obtain ⟨i, hi⟩ := hne F hF
          exact ⟨i, hi, fun G hG ↦ False.elim (hDne ⟨G, hG⟩)⟩
      obtain ⟨i, hi, hzero⟩ := hcoord
      have hspan : (F.card : ℝ)⁻¹ • ∑ j ∈ F, (Pi.single j 1 : ι → ℝ) ∉
          Submodule.span ℝ ((fun G : Finset ι ↦
            (G.card : ℝ)⁻¹ • ∑ j ∈ G, (Pi.single j 1 : ι → ℝ)) '' (D : Set _)) := by
        intro hm
        have hv : ((F.card : ℝ)⁻¹ • ∑ j ∈ F, (Pi.single j 1 : ι → ℝ)) i = 0 := by
          apply Submodule.span_induction (p := fun v _ ↦ v i = 0) ?_ ?_ ?_ ?_ hm
          · rintro v ⟨G, hG, rfl⟩
            change ((G.card : ℝ)⁻¹ • ∑ j ∈ G, (Pi.single j 1 : ι → ℝ)) i = 0
            simp only [standard_barycenter_coordinate, ite_eq_right (hzero G hG)]
          · rfl
          · intro x y _ _ hx hy
            change x i + y i = 0
            rw [hx, hy, add_zero]
          · intro c x _ hx
            change c * x i = 0
            rw [hx, mul_zero]
        rw [standard_barycenter_coordinate, ite_eq_left hi] at hv
        exact (inv_ne_zero (Nat.cast_ne_zero.mpr (hne F hF).card_ne_zero)) hv
      have hnot : F ∉ (D : Set (Finset ι)) := Finset.notMem_erase F C
      have hresult := (linearIndepOn_insert hnot).mpr ⟨hD, hspan⟩
      simpa [D, ← Finset.coe_insert, Finset.insert_erase hF, Finset.insert_eq_of_mem hF] using hresult
    · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC
      subst C
      simp

end HolomorphicAnosov.BarycentricGeometry
