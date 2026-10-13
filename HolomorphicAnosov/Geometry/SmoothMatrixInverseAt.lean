import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Geometry.Manifold.Algebra.Structures

open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov
noncomputable section

/-- Inverse entries of a smooth matrix-valued function are smooth at points where the determinant is nonzero (Andrews, Lecture 10, p. 98). -/
theorem manifold_matrix_inverse_entry_smoothAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    {n : ℕ} (G : M → Matrix (Fin n) (Fin n) ℝ) (p : M)
    (hG : ∀ i j, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun q ↦ G q i j) p)
    (hd : (G p).det ≠ 0) (i j : Fin n) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun q ↦ ((G q)⁻¹) i j) p := by
  classical
  have hdet (A : M → Matrix (Fin n) (Fin n) ℝ)
      (hA : ∀ i j, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun q ↦ A q i j) p) :
      ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun q ↦ (A q).det) p := by
    simp only [Matrix.det_apply']
    refine ContMDiffAt.sum fun σ _ ↦ contMDiffAt_const.mul ?_
    exact ContMDiffAt.prod fun k _ ↦ hA (σ k) k
  have hadj : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun q ↦ (G q).adjugate i j) p := by
    simp only [Matrix.adjugate_apply]
    apply hdet
    intro k l
    by_cases h : k = j
    · subst k
      simpa only [Matrix.updateRow_self] using
        (contMDiffAt_const (c := ((Pi.single i (1 : ℝ)) : Fin n → ℝ) l)
          (I := 𝓘(ℝ, E)) (n := ∞) (x := p))
    · simpa only [Matrix.updateRow_ne h] using hG k l
  have hinv := (contDiffAt_inv ℝ hd (n := ∞)).contMDiffAt.comp p (hdet G hG)
  have hmul := hinv.mul hadj
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  convert hmul using 1
  rfl


end
end HolomorphicAnosov
