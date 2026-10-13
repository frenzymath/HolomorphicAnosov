import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.CovariantDerivativeFiniteLocalConnection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.FiniteLocalConnection

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
/-- A subordinate partition-of-unity sum of local Dolbeault- and Bott-compatible connection forms
defines a compatible connection. (Zhang, p.5, after (4)) -/
theorem finiteLocalConnection_compatible
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
    (hDolbeault : ∀ i (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (x : X), x ∈ O i → x ∈ V → ∀ v : TangentSpace (complexModel d) x,
      B i V e x (complexTangentToReal d x (Complex.I • v)) =
        Complex.I * B i V e x (complexTangentToReal d x v))
    (hBott : ∀ i (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (Y Z : (x : X) → TangentSpace (complexModel d) x),
      QuotientLineConnection.IsSmoothTangentField V Y →
      QuotientLineConnection.IsSmoothTangentField V Z →
      (∀ x ∈ V, Y x ∈ P x) → ∀ x (hx : x ∈ V), x ∈ O i →
      let s := fun y ↦ QuotientLineConnection.projection P y (Z y)
      let D := fun v ↦ (e.coordinate x hx).symm
        (QuotientLineConnection.realDifferential (e.coefficient s) x v +
          e.coefficient s x * B i V e x v)
      (1 / 2 : ℂ) • (D (complexTangentToReal d x (Y x)) -
        Complex.I • D (complexTangentToReal d x (Complex.I • Y x))) =
        QuotientLineConnection.projection P x (QuotientLineConnection.bottBracket Y Z x)) :
    QuotientLineConnection.IsCompatible (finiteLocalConnection O ρ hρsupport hρsum B hB) := by
  constructor
  · intro V e x hx v
    simp only [finiteLocalConnection, sum_apply, smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ρ i x = 0
    · simp [hi]
    · rw [hDolbeault i V e x (hρsupport i hi) hx v]
      ring
  · intro V e Y Z hY hZ hYP x hx
    rw [covariantDerivative_finiteLocalConnection,
      covariantDerivative_finiteLocalConnection]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    calc
      _ = ∑ i, ρ i x • QuotientLineConnection.projection P x
          (QuotientLineConnection.bottBracket Y Z x) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : ρ i x = 0
        · simp [hi]
        · rw [smul_comm Complex.I (ρ i x), ← smul_sub,
            smul_comm (1 / 2 : ℂ) (ρ i x), hBott i V e Y Z hY hZ hYP x hx
              (hρsupport i hi)]
      _ = _ := by rw [← Finset.sum_smul, hρsum x, one_smul]


end ConnectionCalculus
end HolomorphicAnosov
