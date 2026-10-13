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
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Complex.Basic
import HolomorphicAnosov.Paper.Ghys.QuotientAffineEquiv
import HolomorphicAnosov.Paper.Ghys.QuotientTranslation
import HolomorphicAnosov.Paper.Ghys.AffineCenter
import HolomorphicAnosov.Paper.Ghys.AffineTranslationSemiconj

namespace HolomorphicAnosov

open scoped ContDiff Topology _root_.Topology Manifold Bundle
open IsManifold
attribute [local instance] complexTorus_isManifold complex_isManifold_real
set_option backward.isDefEq.respectTransparency false

theorem affine_conjugacy_of_hyperbolic {d : ℕ} (L : FullComplexLattice d)
    (A : LatticeLinearEquiv L) (b : ComplexModel d)
    (hHyper : ∀ μ : ℂ, Module.End.HasEigenvalue A.linear.toLinearMap μ → ‖μ‖ ≠ 1) :
    ∃ (c : ComplexModel d) (τ : Biholomorph d d (ComplexTorus L) (ComplexTorus L)),
      (∀ x, τ x = x - (QuotientAddGroup.mk c : ComplexTorus L)) ∧
      Function.Semiconj (fun x ↦ τ x) (quotientAffineEquiv A b)
        (quotientLinearEquiv A) := by
  have h1 : ¬ Module.End.HasEigenvalue A.linear.toLinearMap 1 := by
    intro he
    exact hHyper 1 he (by simp)
  obtain ⟨c, hc⟩ := affine_center A b h1
  refine ⟨c, quotientTranslation L c, ?_, ?_⟩
  · intro x
    rfl
  · exact affine_translation_semiconj A b c hc

end HolomorphicAnosov
