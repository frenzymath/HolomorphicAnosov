import HolomorphicAnosov.Geometry.Biholomorph
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LatticeLinearEquiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Quotient
import Mathlib.Algebra.Group.Units.Equiv
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.Charts
import HolomorphicAnosov.Geometry.Manifold.ComplexTorus.LinearMap
import HolomorphicAnosov.Paper.Zhang.Anosov
import Mathlib.LinearAlgebra.Eigenspace.Basic
import HolomorphicAnosov.Paper.Zhang.FixedBlockUniformAnosovEstimates
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Module.Convex
import HolomorphicAnosov.Paper.Ghys.QuotientAffineEquiv
import HolomorphicAnosov.Paper.Ghys.AffineConjugacyOfHyperbolic
import HolomorphicAnosov.Paper.Ghys.TorusCompactComplexManifold
import HolomorphicAnosov.Paper.Ghys.AffineAnosovHyperbolic

/-! This file develops the constructions and results stated below. -/

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

/-- An Anosov affine automorphism of a complex torus has hyperbolic linear part and is biholomorphically conjugate to that linear part by a translation. (Eisenberg–Hedlund, Lemma 1; HPS, Theorem 2.5) -/
theorem torusAffineLinearization {d : ℕ} (L : FullComplexLattice d)
    (A : LatticeLinearEquiv L) (b : ComplexModel d)
    (hAnosov : ∃ hM : IsManifold (complexModel d) ∞ (ComplexTorus L),
      letI := hM
      ∃ f : Biholomorph d d (ComplexTorus L) (ComplexTorus L),
        (∀ x, f x = quotientAffineEquiv A b x) ∧ Nonempty (AnosovDatum f)) :
    (∀ μ : ℂ, Module.End.HasEigenvalue A.linear.toLinearMap μ → ‖μ‖ ≠ 1) ∧
    ∃ (c : ComplexModel d) (τ : Biholomorph d d (ComplexTorus L) (ComplexTorus L)),
      (∀ x, τ x = x - (QuotientAddGroup.mk c : ComplexTorus L)) ∧
      Function.Semiconj (fun x ↦ τ x) (quotientAffineEquiv A b)
        (quotientLinearEquiv A) := by
  obtain ⟨hM, f, hf, ⟨a⟩⟩ := hAnosov
  have hh := affine_anosov_hyperbolic L A b f hf a
  exact ⟨hh, affine_conjugacy_of_hyperbolic L A b hh⟩


end HolomorphicAnosov
