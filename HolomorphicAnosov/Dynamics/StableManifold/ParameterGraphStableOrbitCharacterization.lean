import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphStableOrbit
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphStableOrbitConverse

noncomputable section
namespace HolomorphicAnosov

/-- A centered invariant unit-slope stable graph is characterized by forward orbit retention and a bounded normalized orbit (HPS, pp.59–61, 62). -/
theorem parameter_graph_stable_orbit_characterization
    {A : Type*} {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    (h : A → A) (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : ∀ p, G p 0 = 0) (m ρ : ℝ) (hm : 0 ≤ m) (hρ : 0 < ρ)
    (k ε : NNReal) (hexpand : ρ < m - 3 * (ε : ℝ))
    (hcontract : (k : ℝ) + ε ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hT₁ : ∀ p, m * ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ 1)
    (hT₂ : ∀ p, ‖T₂ p‖ ≤ k)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2)))
    (t : ∀ p, E₂ p → E₁ p)
    (ht : ∀ p, t p 0 = 0 ∧ LipschitzWith 1 (t p))
    (hpre : ∀ p, G p ⁻¹' Set.range (fun y ↦ (t (h p) y,y)) =
      Set.range (fun y ↦ (t p y,y)))
    (d : ℝ) (p : A) (z : E₁ p × E₂ p) (hz : ‖z‖ < d) :
    z ∈ Set.range (fun y ↦ (t p y,y)) ↔
      let g : Sigma (fun p ↦ E₁ p × E₂ p) → Sigma (fun p ↦ E₁ p × E₂ p) :=
        fun v ↦ ⟨h v.1, G v.1 v.2⟩
      (∀ n : ℕ, ‖((g^[n]) ⟨p,z⟩).2‖ < d) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖((g^[n]) ⟨p,z⟩).2‖ ≤ C * ρ ^ n := by
  constructor
  · intro hmem
    exact (parameter_graph_stable_orbit h (fun p ↦ (T₁ p).toContinuousLinearMap)
      T₂ G hG k ε hT₂ hR t ht hpre p z hmem).2 ρ d hcontract hρ₁ hz
  · intro hbounded
    apply parameter_graph_stable_orbit_converse h T₁ T₂ G m ρ hm hρ ε hexpand
      hT₁ hR t ht _ p z hbounded.2
    intro q y
    have hmem : G q (t q y,y) ∈ Set.range (fun v ↦ (t (h q) v,v)) := by
      change (t q y,y) ∈ G q ⁻¹' Set.range (fun v ↦ (t (h q) v,v))
      rw [hpre]
      exact ⟨y,rfl⟩
    obtain ⟨v,hv⟩ := hmem
    rw [← hv]

end HolomorphicAnosov
