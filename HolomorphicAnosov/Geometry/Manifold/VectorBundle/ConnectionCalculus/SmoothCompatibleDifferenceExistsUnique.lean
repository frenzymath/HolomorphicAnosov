import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.CompatibleDifferenceAnnihilates
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.ScalarDifferenceExistsUnique
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.ScalarDifferenceSmooth
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.CompatibleDifferenceComplexLinear

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- Two smooth quotient-line connections have a unique smooth scalar one-form difference; for a
compatible pair, this form is complex linear and annihilates the subbundle. (Zhang, §2.1, (3)
and (6), pp.4–5; Demailly, V §2, p.255) -/
theorem smooth_compatible_difference_exists_unique
    [T2Space X] [SecondCountableTopology X] [CompactSpace X]
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)} {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P)
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      Nonempty (QuotientLineConnection.HolomorphicFrame P V))
    (D D' : QuotientLineConnection.Connection P)
    (hD : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (QuotientLineConnection.coordinateForm D e c)
        (c.target ∩ c.symm ⁻¹' (V : Set X)))
    (hD' : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (QuotientLineConnection.coordinateForm D' e c)
        (c.target ∩ c.symm ⁻¹' (V : Set X))) :
    ∃! α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ,
      (∀ (c : OpenPartialHomeomorph X (ComplexModel d)),
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
        ContDiffOn ℝ ∞ (fun z ↦ (α (c.symm z)).comp
          ((mfderiv (realModel d) (realModel d) c.symm z).comp
            (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap)) c.target) ∧
      (∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (x : X), x ∈ V → D'.form V e x = D.form V e x + α x) ∧
      (QuotientLineConnection.IsCompatible D → QuotientLineConnection.IsCompatible D' →
        ∀ x (v : TangentSpace (complexModel d) x),
          α x (complexTangentToReal d x (Complex.I • v)) =
            Complex.I * α x (complexTangentToReal d x v) ∧
          (v ∈ P x → α x (complexTangentToReal d x v) = 0)) := by
  obtain ⟨α, hα, huniq⟩ := scalar_difference_exists_unique hcover D D'
  refine ⟨α, ⟨scalar_difference_smooth hcover D D' hD hD' α hα, hα, ?_⟩, ?_⟩
  · intro hc hc' x v
    obtain ⟨V, hx, ⟨e⟩⟩ := hcover x
    have hform : D'.form V e x - D.form V e x = α x := by
      rw [hα V e x hx]
      abel
    refine ⟨?_, compatible_difference_annihilates hP hcover D D' hc hc' α hα x v⟩
    rw [← hform]
    exact compatible_difference_complex_linear D D' hc hc' V e x hx v
  · intro β hβ
    exact huniq β hβ.2.1

end HolomorphicAnosov.ConnectionCalculus
