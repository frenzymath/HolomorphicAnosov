import HolomorphicAnosov.Targets.Theorem12Support.RealToralAssembly
import HolomorphicAnosov.Targets.Theorem12Support.LiftedCarrier
import HolomorphicAnosov.Targets.Theorem12Support.UniverseLatticeTransport
import HolomorphicAnosov.Targets.Theorem12Support.UniverseLinearTransport
import HolomorphicAnosov.Targets.Theorem12Support.UniverseSpectralTransport
import HolomorphicAnosov.Targets.Theorem12Support.UniverseQuotientTransport

section
universe liftedUniverse
namespace HolomorphicAnosov.Theorem12LiftedAssembly
open Theorem12LiftedCarrier

/-- A hyperbolic real toral conjugacy gives a toral model on the universe-lifted real coordinate
space with a discrete full lattice and compact quotient. Its linear automorphism preserves the
lattice and has no complex eigenvalue of modulus one. -/
theorem lifted_real_toral_model {n : ℕ} {X : Type liftedUniverse}
    [TopologicalSpace X] (f : X → X) (hmodel : HyperbolicRealToralConjugacy n X f) :
    let e := liftEquiv.{liftedUniverse} n
    let Γ := (IntegerCoordinateLattice.integerLattice n).map
      (e.toLinearMap.restrictScalars ℤ)
    letI : DiscreteTopology Γ :=
      UniverseLatticeTransport.mapped_integerSpan_discrete (Pi.basisFun ℝ (Fin n)) e
    DiscreteTopology Γ ∧ IsZLattice ℝ Γ ∧
    Submodule.span ℝ (Γ : Set (Carrier.{liftedUniverse} n)) = ⊤ ∧
    Module.finrank ℝ (Carrier.{liftedUniverse} n) = n ∧
    CompactSpace ((Carrier.{liftedUniverse} n) ⧸ Γ.toAddSubgroup) ∧
    ∃ (R : Carrier.{liftedUniverse} n ≃L[ℝ] Carrier.{liftedUniverse} n)
      (h : X ≃ₜ (Carrier.{liftedUniverse} n) ⧸ Γ.toAddSubgroup),
      R '' (Γ : Set (Carrier.{liftedUniverse} n)) = Γ ∧
      (∀ μ : ℂ, Module.End.HasEigenvalue
        (R.toLinearEquiv.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1) ∧
      ∀ x v, (QuotientAddGroup.mk v : (Carrier.{liftedUniverse} n) ⧸ Γ.toAddSubgroup)
        = h x → h (f x) = QuotientAddGroup.mk (R v) := by
  dsimp only
  rcases Theorem12RealToralModel.real_toral_model_of_hyperbolic_conjugacy f hmodel with
    ⟨_hdiscrete, _hlattice, _hspan, _hdim, hcompact, R, hq, hR, hhyper, hconj⟩
  let e := liftEquiv.{liftedUniverse} n
  let Γ₀ := IntegerCoordinateLattice.integerLattice n
  let Γ := Γ₀.map (e.toLinearMap.restrictScalars ℤ)
  have hd : DiscreteTopology Γ :=
    UniverseLatticeTransport.mapped_integerSpan_discrete (Pi.basisFun ℝ (Fin n)) e
  have hz : IsZLattice ℝ Γ :=
    UniverseLatticeTransport.mapped_integerSpan_isZLattice (Pi.basisFun ℝ (Fin n)) e
  let E := UniverseQuotientTransport.quotientHomeomorph e Γ₀
  have hc₀ : CompactSpace ((Fin n → ℝ) ⧸ Γ₀.toAddSubgroup) := hcompact
  have hc : CompactSpace ((Carrier.{liftedUniverse} n) ⧸ Γ.toAddSubgroup) :=
    E.compactSpace
  refine ⟨hd, hz,
    UniverseLatticeTransport.mapped_integerSpan_full (Pi.basisFun ℝ (Fin n)) e,
    carrier_finrank n, hc, UniverseLinearTransport.conjugate e R, hq.trans E, ?_, ?_, ?_⟩
  · exact UniverseLinearTransport.conjugate_image_transportedLattice e R Γ₀ hR
  · intro μ hμ
    exact hhyper μ ((Theorem12UniverseSpectralScratch.hasEigenvalue_conjugate_baseChange_iff
      e R μ).mp hμ)
  · exact UniverseQuotientTransport.transported_model_conjugacy e Γ₀ R hq f hconj


end HolomorphicAnosov.Theorem12LiftedAssembly
end
