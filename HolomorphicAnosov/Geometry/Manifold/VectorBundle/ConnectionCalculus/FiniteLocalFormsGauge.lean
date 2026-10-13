import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov
namespace ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- A subordinate weighted sum of local connection forms satisfies the gauge law when the weights
sum to one. (Zhang, after (4)) -/
theorem finite_local_forms_gauge
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    {ι : Type*} [Fintype ι] (O : ι → Opens X) (ρ : ι → X → ℂ)
    (hρsupport : ∀ i, Function.support (ρ i) ⊆ O i)
    (hρsum : ∀ x, ∑ i, ρ i x = 1)
    (B : ∀ _i : ι, ∀ V : Opens X, QuotientLineConnection.HolomorphicFrame P V →
      (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hB : ∀ i (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (e' : QuotientLineConnection.HolomorphicFrame P W) (x : X),
      x ∈ O i → x ∈ V → x ∈ W → B i W e' x = B i V e x +
        (e.coefficient e'.sectionValue x)⁻¹ •
          QuotientLineConnection.realDifferential (e.coefficient e'.sectionValue) x)
    (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (e' : QuotientLineConnection.HolomorphicFrame P W)
    (x : X) (hx : x ∈ V) (hx' : x ∈ W) :
    (∑ i, ρ i x • B i W e' x) = (∑ i, ρ i x • B i V e x) +
      (e.coefficient e'.sectionValue x)⁻¹ •
        QuotientLineConnection.realDifferential (e.coefficient e'.sectionValue) x := by
  have hterm (i : ι) : ρ i x • B i W e' x = ρ i x • B i V e x +
      ρ i x • ((e.coefficient e'.sectionValue x)⁻¹ •
        QuotientLineConnection.realDifferential (e.coefficient e'.sectionValue) x) := by
    by_cases hi : ρ i x = 0
    · ext v
      simp [hi]
    · rw [hB i V W e e' x (hρsupport i hi) hx hx', smul_add]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul, hρsum x, one_smul]



end ConnectionCalculus
end HolomorphicAnosov
