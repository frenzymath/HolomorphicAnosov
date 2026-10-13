import HolomorphicAnosov.Topology.CircleSingularCohomologyWindingBaseG10
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.Topology.CircleHomologyG12
import HolomorphicAnosov.Topology.CircleDegreeZeroBasisG12
import HolomorphicAnosov.AlgebraicTopology.SingularFieldKronecker
import Mathlib.LinearAlgebra.Dual.Basis

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial


namespace HolomorphicAnosov.CircleSingularCohomology
open HolomorphicAnosov.SingularFieldKronecker
set_option backward.isDefEq.respectTransparency false in
theorem profile_of_homology (K : Type) [Field K]
    (z : chainCycles K circleSpace 1) (u : cocycles K circleSpace 0)
    (hu : ∀ σ : singularSet circleSpace _⦋0⦌,
      cocycleEval K circleSpace 0 u (simplexChain K circleSpace 0 σ) = 1)
    (B : Module.Basis Unit K (chainClass K circleSpace 1))
    (hB : B () = cycleClass K circleSpace 1 z)
    (hhigh : ∀ n, 2 ≤ n → Subsingleton (chainClass K circleSpace n)) :
    ∃ (a : cocycles K circleSpace 1)
      (Bcoh1 : Module.Basis Unit K (cohomology K circleSpace 1))
      (Bcoh0 : Module.Basis Unit K (cohomology K circleSpace 0)),
      Bcoh1 () = cocycleClass K circleSpace 1 a ∧
      Bcoh0 () = cocycleClass K circleSpace 0 u ∧
      cocycleEval K circleSpace 1 a z.val = 1 ∧
      (∀ a' : cocycles K circleSpace 1,
        cocycleEval K circleSpace 1 a' z.val = 1 →
          cocycleClass K circleSpace 1 a' = cocycleClass K circleSpace 1 a) ∧
      (∀ n : ℕ, 2 ≤ n → Subsingleton (cohomology K circleSpace n)) := by
  let E := singularKronecker (K := K) circleSpace 1
  let v := E.symm (B.dualBasis ())
  obtain ⟨a, ha⟩ := (Submodule.mkQ_surjective _ v)
  have ha' : cocycleClass K circleSpace 1 a = v := ha
  let Bc := B.dualBasis.map E.symm
  have heval : cocycleEval K circleSpace 1 a z.val = 1 := by
    have rep := singularKronecker_representative (K := K) circleSpace 1 a z
    change E (cocycleClass K circleSpace 1 a) (cycleClass K circleSpace 1 z) = cocycleEval K circleSpace 1 a z.val at rep
    rw [← rep]
    change E (cocycleClass K circleSpace 1 a) (cycleClass K circleSpace 1 z) = 1
    rw [ha', ← hB]
    change E (E.symm (B.dualBasis ())) (B ()) = 1
    simp
  obtain ⟨B0,hB0⟩ := circle_degree_zero_basis_of_unit_cocycle K u hu
  refine ⟨a, Bc, B0, ha'.symm, hB0, heval, ?_, ?_⟩
  · intro a' ha'
    apply E.injective
    apply B.ext
    intro i
    have hi : i = () := Subsingleton.elim _ _
    subst i
    rw [hB]
    change singularKronecker circleSpace 1 _ _ = singularKronecker circleSpace 1 _ _
    exact (singularKronecker_representative circleSpace 1 a' z).trans
      ((ha'.trans heval.symm).trans (singularKronecker_representative circleSpace 1 a z).symm)
  · intro n hn
    let := hhigh n hn
    exact (singularKronecker (K := K) circleSpace n).injective.subsingleton
end HolomorphicAnosov.CircleSingularCohomology

namespace HolomorphicAnosov.CircleSingularCohomology
noncomputable section

/-- The positive exponential loop gives the singleton homology basis over every field.
The integral Hurewicz basis is transported by extension of scalars, with its literal cycle
representative preserved. Sphere vanishing gives zero homology above degree one. Field
Kronecker duality then supplies the normalized degree-one cocycle and its unique class;
the constant-one cocycle supplies the degree-zero basis.

Source: Hatcher, Algebraic Topology, Theorem 2A.1 pp.166–168; universal coefficient
discussion pp.195–199 and sphere homology pp.114–115. -/
theorem circle_degree_one_profile_witness
    (K : Type) [Field K]
    (z : chainCycles K circleSpace 1) (u : cocycles K circleSpace 0)
    (hz : z.val = simplexChain K circleSpace 1 positiveSimplex)
    (hu : ∀ σ : singularSet circleSpace _⦋0⦌,
      cocycleEval K circleSpace 0 u (simplexChain K circleSpace 0 σ) = 1) :
    (∃ (a : cocycles K circleSpace 1)
      (B₁ : Module.Basis Unit K (chainClass K circleSpace 1))
      (Bcoh1 : Module.Basis Unit K (cohomology K circleSpace 1))
      (Bcoh0 : Module.Basis Unit K (cohomology K circleSpace 0)),
      B₁ () = cycleClass K circleSpace 1 z ∧
      Bcoh1 () = cocycleClass K circleSpace 1 a ∧
      Bcoh0 () = cocycleClass K circleSpace 0 u ∧
      cocycleEval K circleSpace 1 a z.val = 1 ∧
      (∀ a' : cocycles K circleSpace 1,
        cocycleEval K circleSpace 1 a' z.val = 1 →
          cocycleClass K circleSpace 1 a' = cocycleClass K circleSpace 1 a) ∧
      (∀ n : ℕ, 2 ≤ n → Subsingleton (cohomology K circleSpace n))) ∧
      z.val = simplexChain K circleSpace 1 positiveSimplex := by
  obtain ⟨B,hB⟩ := CircleHomology.field_positive_basis K z hz
  have hhigh (n : ℕ) (hn : 2 ≤ n) : Subsingleton (chainClass K circleSpace n) := by
    have h := CircleHomology.high K n hn
    have hz := h.of_iso ((chain K circleSpace).sc n).moduleCatHomologyIso.symm
    exact ModuleCat.subsingleton_of_isZero hz
  obtain ⟨a,B1,B0,h1,h0,he,huq,hhi⟩ := profile_of_homology K z u hu B hB hhigh
  exact ⟨⟨a,B,B1,B0,hB,h1,h0,he,huq,hhi⟩,hz⟩

end
end HolomorphicAnosov.CircleSingularCohomology

