import HolomorphicAnosov.Topology.DegreeOneHurewiczAbelianized
import HolomorphicAnosov.Topology.LoopSingularClass
import HolomorphicAnosov.Topology.DegreeOneHurewiczAbelianizedApply
import HolomorphicAnosov.Topology.AbelianizationLiftBijective

noncomputable section
universe u
namespace HolomorphicAnosov.Topology
/-- Surjectivity and the commutator-kernel identity give the canonical additive
Hurewicz equivalence with its original loop formula.
Source: Hatcher, Algebraic Topology, Theorem 2A.1 p.167. Apply the quotient-lift
bijection theorem, keep that lift as the forward map using `AddEquiv.ofBijective`,
and evaluate it on each loop by the abelianization representative formula. -/
theorem degreeOneHurewicz_equiv_of_kernel
    {X : Type u} [TopologicalSpace X] (x : X)
    (hs : Function.Surjective (degreeOneHurewicz x))
    (hk : (degreeOneHurewicz x).ker = commutator (FundamentalGroup X x)) :
    ∃ e : Additive (Abelianization (FundamentalGroup X x)) ≃+ IntegralSingularH1 X,
      (∀ a, e a = degreeOneHurewiczAbelianized x a) ∧
      (∀ α : Path x x,
        e (Additive.ofMul (Abelianization.of (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk α)))) = loopSingularClass α) := by
  have hb := abelianization_lift_bijective (degreeOneHurewicz x) hs hk
  have hb' : Function.Bijective (degreeOneHurewiczAbelianized x) := hb
  refine ⟨AddEquiv.ofBijective (degreeOneHurewiczAbelianized x) hb', ?_, ?_⟩
  · intro a
    rfl
  · intro α
    exact degreeOneHurewiczAbelianized_apply_of α
end HolomorphicAnosov.Topology
