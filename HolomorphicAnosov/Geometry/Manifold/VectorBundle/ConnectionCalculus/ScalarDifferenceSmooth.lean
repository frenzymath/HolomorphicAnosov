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
/-- The scalar difference of two smooth quotient-line connections is smooth in chart coordinates.
(Zhang, (3)) -/
theorem scalar_difference_smooth
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
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
        (c.target ∩ c.symm ⁻¹' (V : Set X)))
    (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hα : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (x : X), x ∈ V → D'.form V e x = D.form V e x + α x) :
    ∀ (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (fun z ↦ (α (c.symm z)).comp
        ((mfderiv (realModel d) (realModel d) c.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap)) c.target := by
  intro c hc
  apply c.open_target.contDiffOn_iff.mpr
  intro z hz
  obtain ⟨V, hx, ⟨e⟩⟩ := hcover (c.symm z)
  have hs := (hD' V e c hc).sub (hD V e c hc)
  have heq : Set.EqOn
      (fun y ↦ (α (c.symm y)).comp
        ((mfderiv (realModel d) (realModel d) c.symm y).comp
          (NormedSpace.fromTangentSpace y).symm.toContinuousLinearMap))
      (fun y ↦ QuotientLineConnection.coordinateForm D' e c y -
        QuotientLineConnection.coordinateForm D e c y)
      (c.target ∩ c.symm ⁻¹' (V : Set X)) := by
    intro y hy
    ext v
    simp [QuotientLineConnection.coordinateForm, hα V e (c.symm y) hy.2]
  exact (hs.congr heq).contDiffAt
    ((c.isOpen_inter_preimage_symm V.isOpen).mem_nhds ⟨hz, hx⟩)



end ConnectionCalculus
end HolomorphicAnosov
