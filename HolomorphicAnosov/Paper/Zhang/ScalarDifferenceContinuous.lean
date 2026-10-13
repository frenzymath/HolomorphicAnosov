import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection

/-!
This file establishes continuity of the scalar difference of continuous
quotient-line connections in holomorphic tangent coordinates. (Zhang, §2.1,
equation (5) and Lemma 2.2, p.5)
-/

open Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection

/-- The scalar difference of two continuous quotient-line connections has continuous
coefficients in every holomorphic inverse-chart tangent frame. (Zhang, §2.1, equation (5)
and Lemma 2.2, p.5) -/
theorem scalar_difference_continuous
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧ Nonempty (HolomorphicFrame U V))
    (D D' : Connection U) (hD : IsContinuous D) (hD' : IsContinuous D')
    (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hα : ∀ (V : Opens X) (e : HolomorphicFrame U V) (x : X), x ∈ V →
      D'.form V e x = D.form V e x + α x) :
    ∀ (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContinuousOn (fun z ↦ (α (c.symm z)).comp
        ((mfderiv (realModel d) (realModel d) c.symm z).comp
          (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap)) c.target := by
  intro c hc z hz
  obtain ⟨V, hx, ⟨e⟩⟩ := hcover (c.symm z)
  have hs := (hD' V e c hc).sub (hD V e c hc)
  have heq : Set.EqOn
      (fun y ↦ (α (c.symm y)).comp
        ((mfderiv (realModel d) (realModel d) c.symm y).comp
          (NormedSpace.fromTangentSpace y).symm.toContinuousLinearMap))
      (fun y ↦ coordinateForm D' e c y - coordinateForm D e c y)
      (c.target ∩ c.symm ⁻¹' (V : Set X)) := by
    intro y hy
    ext v
    simp [coordinateForm, hα V e (c.symm y) hy.2]
  exact ((hs.congr heq).continuousAt
    ((c.isOpen_inter_preimage_symm V.isOpen).mem_nhds ⟨hz, hx⟩)).continuousWithinAt

end HolomorphicAnosov
