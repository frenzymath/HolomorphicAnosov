namespace HolomorphicAnosov.Ghys

universe u v w

/-! Forward and inverse inclusion equations for leaf transport maps. -/
theorem jet_dynamics_transport_intertwining
    {Q : Type u} {X : Q → Type v} {M : Type w}
    (σ : Q → Q) (σi : Q → Q)
    (F : ∀ q, X q → X (σ q)) (G : ∀ q, X q → X (σi q))
    (ι : ∀ q, X q → M) (f : M → M)
    (hF : ∀ q z, ι (σ q) (F q z) = f (ι q z))
    (hG : ∀ q z, ι (σi q) (G q z) = f (ι q z)) :
    (∀ q z, ι (σ q) (F q z) = f (ι q z)) ∧
      (∀ q z, ι (σi q) (G q z) = f (ι q z)) := by
  exact ⟨hF, hG⟩

end HolomorphicAnosov.Ghys
