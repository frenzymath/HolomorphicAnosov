import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-! Continuous real linear equivalences transport automorphisms by conjugation and integer
submodules by image. Lattice preservation is invariant under this transport, with explicit
formulas for universe lifts. -/

namespace HolomorphicAnosov.UniverseLinearTransport
noncomputable section

universe u v w
variable {V : Type u} {W : Type v}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The continuous real linear automorphism `e ∘ R ∘ e⁻¹`. -/
def conjugate (e : V ≃L[ℝ] W) (R : V ≃L[ℝ] V) : W ≃L[ℝ] W :=
  e.symm.trans (R.trans e)

/-- The integer submodule obtained as the image of `Γ` under `e`. -/
def transportedLattice (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) : Submodule ℤ W :=
  Γ.map (e.toLinearMap.restrictScalars ℤ)

/-- The conjugated automorphism sends `x` to `e (R (e.symm x))`. -/
theorem conjugate_apply (e : V ≃L[ℝ] W) (R : V ≃L[ℝ] V) (x : W) :
    conjugate e R x = e (R (e.symm x)) := rfl

/-- The inverse of the conjugate of `R` is the conjugate of `R.symm`. -/
theorem conjugate_symm (e : V ≃L[ℝ] W) (R : V ≃L[ℝ] V) :
    (conjugate e R).symm = conjugate e R.symm := by
  ext x
  rfl

/-- A vector `x` belongs to the transported lattice exactly when `e.symm x` belongs to `Γ`. -/
theorem mem_transportedLattice (e : V ≃L[ℝ] W) (Γ : Submodule ℤ V) (x : W) :
    x ∈ transportedLattice e Γ ↔ e.symm x ∈ Γ := by
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp hx
    change e y = x at hxy
    rw [← hxy]
    simpa using hy
  · intro hx
    apply Submodule.mem_map.mpr
    exact ⟨e.symm x, hx, e.apply_symm_apply x⟩

/-- If `R` maps `Γ` onto itself, its conjugate maps the transported lattice onto itself. -/
theorem conjugate_image_transportedLattice
    (e : V ≃L[ℝ] W) (R : V ≃L[ℝ] V) (Γ : Submodule ℤ V)
    (hR : R '' (Γ : Set V) = (Γ : Set V)) :
    conjugate e R '' (transportedLattice e Γ : Set W) =
      (transportedLattice e Γ : Set W) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    apply (mem_transportedLattice e Γ _).mpr
    simp only [conjugate_apply, ContinuousLinearEquiv.symm_apply_apply]
    change R (e.symm x) ∈ (Γ : Set V)
    rw [← hR]
    exact ⟨e.symm x, (mem_transportedLattice e Γ x).mp hx, rfl⟩
  · intro x hx
    have hlow : e.symm x ∈ R '' (Γ : Set V) := by
      rw [hR]
      exact (mem_transportedLattice e Γ x).mp hx
    obtain ⟨y, hy, hRy⟩ := hlow
    refine ⟨e y, ?_, ?_⟩
    · apply (mem_transportedLattice e Γ _).mpr
      simpa using hy
    · simp only [conjugate_apply, ContinuousLinearEquiv.symm_apply_apply]
      rw [hRy]
      exact e.apply_symm_apply x

/-- The automorphism transported to `ULift` sends `x` to `ULift.up (R x.down)`. -/
theorem ulift_conjugate_apply {n : ℕ} (R : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (x : ULift.{w} (Fin n → ℝ)) :
    conjugate (ContinuousLinearEquiv.ulift.symm :
      (Fin n → ℝ) ≃L[ℝ] ULift.{w} (Fin n → ℝ)) R x = ULift.up (R x.down) := rfl

/-- The value of the transported automorphism projects down to `R x.down`. -/
theorem ulift_conjugate_down {n : ℕ} (R : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (x : ULift.{w} (Fin n → ℝ)) :
    (conjugate (ContinuousLinearEquiv.ulift.symm :
      (Fin n → ℝ) ≃L[ℝ] ULift.{w} (Fin n → ℝ)) R x).down = R x.down := rfl

/-- The transported automorphism sends `ULift.up x` to `ULift.up (R x)`. -/
theorem ulift_conjugate_up {n : ℕ} (R : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (x : Fin n → ℝ) :
    conjugate (ContinuousLinearEquiv.ulift.symm :
      (Fin n → ℝ) ≃L[ℝ] ULift.{w} (Fin n → ℝ)) R (ULift.up x) =
      ULift.up (R x) := rfl

/-- The inverse transported automorphism sends `x` to `ULift.up (R.symm x.down)`. -/
theorem ulift_conjugate_inverse_apply {n : ℕ}
    (R : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)) (x : ULift.{w} (Fin n → ℝ)) :
    (conjugate (ContinuousLinearEquiv.ulift.symm :
      (Fin n → ℝ) ≃L[ℝ] ULift.{w} (Fin n → ℝ)) R).symm x =
      ULift.up (R.symm x.down) := rfl

end
end HolomorphicAnosov.UniverseLinearTransport

