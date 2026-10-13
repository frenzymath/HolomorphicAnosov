import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.StableProjectionFibreIff
import HolomorphicAnosov.Paper.Zhang.InvariantHolomorphicOneForm.StableProjectionCommutes

open Set

open scoped _root_.Topology

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang


universe u

/-- The conjugacy and a coordinate on the stable summand define a surjective scalar projection with
a section, unstable fibres, and `q ∘ F = μ * q`. (Zhang, Lemma 4.2, p.14) -/
theorem stable_projection_construction
    {V Y : Type*} [AddCommGroup V] [Module ℝ V]
    (S U : Submodule ℝ V) (hSU : IsCompl S U)
    (H : Y ≃ V) (phi : S ≃ ℂ) (A : V →ₗ[ℝ] V) (F : Y → Y) (mu : ℂ)
    (hAS : ∀ v ∈ S, A v ∈ S) (hAU : ∀ v ∈ U, A v ∈ U)
    (hHF : ∀ y, H (F y) = A (H y))
    (hphiA : ∀ v : S, phi ⟨A v, hAS _ v.property⟩ = mu * phi v) :
    ∃ (q : Y → ℂ) (i : ℂ → Y),
      (∀ y, q y = phi (S.projectionOnto U hSU (H y))) ∧
      (∀ z, i z = H.symm (phi.symm z)) ∧
      (∀ z, q (i z) = z) ∧ Function.Surjective q ∧
      (∀ y z, q y = q z ↔ H y - H z ∈ U) ∧
      (∀ y, q (F y) = mu * q y) := by
  let q : Y → ℂ := fun y ↦ phi (S.projectionOnto U hSU (H y))
  let i : ℂ → Y := fun z ↦ H.symm (phi.symm z)
  have hi : ∀ z, q (i z) = z := by
    intro z
    simp only [q, i, Equiv.apply_symm_apply, S.projectionOnto_apply_left hSU]
  refine ⟨q, i, fun _ ↦ rfl, fun _ ↦ rfl, hi, ?_, ?_, ?_⟩
  · exact fun z ↦ ⟨i z, hi z⟩
  · exact stable_projection_fibre_iff S U hSU H phi
  · intro y
    change phi (S.projectionOnto U hSU (H (F y))) = _
    rw [hHF y, stable_projection_commutes S U hSU A hAS hAU]
    exact hphiA _


end HolomorphicAnosov.Paper.Zhang
