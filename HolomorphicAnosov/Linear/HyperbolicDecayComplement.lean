import HolomorphicAnosov.Linear.HyperbolicDecayAux41

open Filter
open scoped Topology _root_.Topology TensorProduct

namespace HolomorphicAnosov

/-!
Complementarity and unique decomposition for the full forward- and inverse-decay spaces of a
finite-dimensional real hyperbolic automorphism. (Alves, Def. 5.4 and Thm 5.5, pp. 15–17)
-/



/-- The full forward- and inverse-decay spaces of a finite-dimensional real hyperbolic automorphism
are complementary real submodules. Every vector has a unique decomposition into these
submodules. (Alves, Def. 5.4 and Thm 5.5) -/
theorem hyperbolic_decay_space_complement
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (A : V ≃L[ℝ] V)
    (hA : ∀ μ : ℂ,
      Module.End.HasEigenvalue (A.toLinearEquiv.toLinearMap.baseChange ℂ) μ →
        ‖μ‖ ≠ 1) :
    ∃ S U : Submodule ℝ V,
      (∀ v : V, v ∈ S ↔
        Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 (0 : V))) ∧
      (∀ v : V, v ∈ U ↔
        Tendsto (fun n : ℕ ↦ (A.symm ^ n) v) atTop (𝓝 (0 : V))) ∧
      IsCompl S U ∧
      (∀ v : V, ∃! p : S × U, (p.1 : V) + (p.2 : V) = v) := by
  let S := fullForwardDecay A
  let U := fullForwardDecay A.symm
  let B := RealDecayDescent.complexified A
  have hB : ∀ μ, Module.End.HasEigenvalue B.toLinearEquiv.toLinearMap μ → ‖μ‖ ≠ 1 := by
    intro μ hμ
    exact hA μ (RealDecayDescent.complexified_hasEigenvalue A hμ)
  have hcB := complex_full_decay_isCompl B hB
  have hc : IsCompl S U := RealDecayDescent.real_isCompl_of_complex_full_decay
    A S U (fullForwardDecay B) (fullForwardDecay B.symm)
    (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl) hcB
  exact ⟨S, U, (fun _ ↦ Iff.rfl), (fun _ ↦ Iff.rfl), hc,
    fun v ↦ Submodule.existsUnique_add_of_isCompl_prod hc v⟩

end HolomorphicAnosov

