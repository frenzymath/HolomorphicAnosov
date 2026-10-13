import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnstableOrbit
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnstableOrbitConverse

noncomputable section
namespace HolomorphicAnosov

/-- A centered image-invariant unit-slope graph is characterized by coherent backward histories with bounded normalized norms (HPS, pp.59–61, 62). -/
theorem parameter_graph_unstable_orbit_characterization
    {A : Type*} {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    (h : A ≃ A) (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : ∀ p, G p 0 = 0) (a k ε : NNReal) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ₁ : 1 ≤ ρ) (hsmall : (a : ℝ) * ε < 1)
    (hback : (a : ℝ) / (1 - (a : ℝ) * ε) ≤ ρ⁻¹)
    (hforward : (k : ℝ) + 2 * ε < ρ)
    (hT₁ : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hT₂ : ∀ p, ‖T₂ p‖ ≤ k)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2)))
    (s : ∀ p, E₁ p → E₂ p)
    (hs : ∀ p, s p 0 = 0 ∧ LipschitzWith 1 (s p))
    (himage : ∀ p, G p '' Set.range (fun x ↦ (x,s p x)) =
      Set.range (fun x ↦ (x,s (h p) x)))
    (d : ℝ) (p : A) (z : E₁ p × E₂ p) (hz : ‖z‖ < d) :
    z ∈ Set.range (fun x ↦ (x,s p x)) ↔
      ∃ v : ℕ → Sigma (fun p ↦ E₁ p × E₂ p),
        v 0 = ⟨p,z⟩ ∧
        (∀ n, (⟨h (v (n+1)).1, G (v (n+1)).1 (v (n+1)).2⟩ :
          Sigma (fun p ↦ E₁ p × E₂ p)) = v n) ∧
        (∀ n, ‖(v n).2‖ < d) ∧
        ∃ C : ℝ, 0 < C ∧ ∀ n, ‖(v n).2‖ ≤ C * (ρ⁻¹) ^ n := by
  constructor
  · intro hmem
    obtain ⟨v,hv0,hv,_,_,hbound⟩ := parameter_graph_unstable_orbit h T₁ T₂ G hG a ε
      hT₁ hsmall hR s hs himage p z hmem
    obtain ⟨hradius,hrate⟩ := hbound ρ d hρ hρ₁ hback hz
    exact ⟨v,hv0,hv,hradius,hrate⟩
  · rintro ⟨v,hv0,hv,_,hrate⟩
    apply parameter_graph_unstable_orbit_converse h
      (fun p ↦ (T₁ p).toContinuousLinearMap) T₂ G ρ hρ k ε hforward hT₂ hR s hs
      _ p z ⟨v,hv0,hv,hrate⟩
    intro q x
    have hmem : G q (x,s q x) ∈ Set.range (fun u ↦ (u,s (h q) u)) := by
      rw [← himage]
      exact ⟨(x,s q x),⟨x,rfl⟩,rfl⟩
    obtain ⟨u,hu⟩ := hmem
    rw [← hu]

end HolomorphicAnosov
