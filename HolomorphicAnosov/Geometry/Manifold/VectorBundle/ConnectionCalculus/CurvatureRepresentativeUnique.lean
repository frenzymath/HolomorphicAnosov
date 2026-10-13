import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

omit [T2Space X] [SecondCountableTopology X] [CompactSpace X] in
/-- A curvature representative satisfying the chart antisymmetrization formula is unique. (Zhang,
p.6) -/
theorem curvature_representative_unique
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (hcover : ∀ x : X, ∃ V : Opens X, x ∈ V ∧
      Nonempty (QuotientLineConnection.HolomorphicFrame P V))
    (D : QuotientLineConnection.Connection P)
    (R R' : (x : X) → TangentSpace (realModel d) x →L[ℝ]
      (TangentSpace (realModel d) x →L[ℝ] ℂ))
    (hR : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ∀ z ∈ c.target ∩ c.symm ⁻¹' (V : Set X), ∀ v w : ComplexModel d,
        R (c.symm z)
          (mfderiv (realModel d) (realModel d) c.symm z
            ((NormedSpace.fromTangentSpace z).symm v))
          (mfderiv (realModel d) (realModel d) c.symm z
            ((NormedSpace.fromTangentSpace z).symm w)) =
          fderiv ℝ (QuotientLineConnection.coordinateForm D e c) z v w -
            fderiv ℝ (QuotientLineConnection.coordinateForm D e c) z w v)
    (hR' : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ∀ z ∈ c.target ∩ c.symm ⁻¹' (V : Set X), ∀ v w : ComplexModel d,
        R' (c.symm z)
          (mfderiv (realModel d) (realModel d) c.symm z
            ((NormedSpace.fromTangentSpace z).symm v))
          (mfderiv (realModel d) (realModel d) c.symm z
            ((NormedSpace.fromTangentSpace z).symm w)) =
          fderiv ℝ (QuotientLineConnection.coordinateForm D e c) z v w -
            fderiv ℝ (QuotientLineConnection.coordinateForm D e c) z w v) : R' = R := by
  funext x
  ext v w
  obtain ⟨V, hxV, ⟨e⟩⟩ := hcover x
  have hparam (x : X) : Function.Surjective
      (fun v : ComplexModel d ↦
        mfderiv (realModel d) (realModel d) (chartAt (ComplexModel d) x).symm
          (chartAt (ComplexModel d) x x)
          ((NormedSpace.fromTangentSpace (chartAt (ComplexModel d) x x)).symm v)) := by
    exact ((mdifferentiable_chart (I := realModel d) x).symm.mfderiv_surjective
      (mem_chart_target (ComplexModel d) x)).comp
      (NormedSpace.fromTangentSpace (chartAt (ComplexModel d) x x)).symm.surjective
  obtain ⟨v', hv'⟩ := hparam x v
  obtain ⟨w', hw'⟩ := hparam x w
  have hz : chartAt (ComplexModel d) x x ∈
      (chartAt (ComplexModel d) x).target ∩
        (chartAt (ComplexModel d) x).symm ⁻¹' (V : Set X) := by
    exact ⟨mem_chart_target _ x, by simpa using hxV⟩
  have h1 := hR V e (chartAt (ComplexModel d) x)
    (IsManifold.chart_mem_maximalAtlas x) _ hz v' w'
  have h2 := hR' V e (chartAt (ComplexModel d) x)
    (IsManifold.chart_mem_maximalAtlas x) _ hz v' w'
  have hh := h2.trans h1.symm
  have hh' :
      R' ((chartAt (ComplexModel d) x).symm (chartAt (ComplexModel d) x x)) v w =
      R ((chartAt (ComplexModel d) x).symm (chartAt (ComplexModel d) x x)) v w := by
    simpa only [hv', hw'] using hh
  rw [(chartAt (ComplexModel d) x).left_inv (mem_chart_source _ x)] at hh'
  exact hh'

end HolomorphicAnosov.ConnectionCalculus
