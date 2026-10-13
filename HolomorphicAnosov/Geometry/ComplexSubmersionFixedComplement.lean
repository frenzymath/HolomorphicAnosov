import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Geometry.Manifold.Submersion
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions

open scoped ContDiff Manifold

namespace HolomorphicAnosov

/-- A complex scalar submersion on a finite-dimensional manifold has a standard complex complement of dimension `d - 1`. (Zhang, Lemma 2.4) -/
theorem complex_submersion_fixed_complement
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    {n : ℕ∞ω} {q : M → ℂ} {x : M}
    (h : Manifold.IsSubmersionAt (complexModel d) 𝓘(ℂ, ℂ) n q x) :
    Manifold.IsSubmersionAtOfComplement (ComplexModel (d - 1))
      (complexModel d) 𝓘(ℂ, ℂ) n q x := by
  let : FiniteDimensional ℂ (ℂ × h.complement) :=
    FiniteDimensional.of_injective h.equiv.symm.toLinearEquiv.toLinearMap h.equiv.symm.injective
  let : FiniteDimensional ℂ h.complement :=
    FiniteDimensional.of_injective (LinearMap.inr ℂ ℂ h.complement)
      (by intro v w heq; exact congrArg Prod.snd heq)
  have hdim : d = 1 + Module.finrank ℂ h.complement := by
    have he := h.equiv.toLinearEquiv.finrank_eq
    simpa only [ComplexModel, Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      smul_eq_mul, mul_one, Module.finrank_prod] using he
  let e : h.complement ≃L[ℂ] ComplexModel (d - 1) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa [ComplexModel] using (show
      Module.finrank ℂ h.complement = d - 1 by omega))
  exact h.isSubmersionAtOfComplement_complement.trans_F e

end HolomorphicAnosov
