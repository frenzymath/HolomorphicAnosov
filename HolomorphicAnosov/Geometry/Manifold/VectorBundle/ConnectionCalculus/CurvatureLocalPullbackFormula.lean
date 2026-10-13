import HolomorphicAnosov.Analysis.ScalarGaugePullbackCurvature
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
/-- For a local connection form pulled back by a C² coordinate map and transformed by a nonvanishing
scalar gauge, its curvature is the pullback of the source curvature. (Zhang, p.6) -/
theorem curvature_local_pullback_formula
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (D : QuotientLineConnection.Connection P)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (hD : ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (c : OpenPartialHomeomorph X (ComplexModel d)),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContDiffOn ℝ ∞ (QuotientLineConnection.coordinateForm D e c)
        (c.target ∩ c.symm ⁻¹' (V : Set X)))
    (F : ComplexModel d → ComplexModel d) (g : ComplexModel d → ℂ)
    (z : ComplexModel d) (hz : F z ∈ c.target ∩ c.symm ⁻¹' (V : Set X))
    (hF : ContDiffAt ℝ 2 F z) (hg : ContDiffAt ℝ 2 g z) (hg0 : g z ≠ 0)
    (v w : ComplexModel d) :
    fderiv ℝ (fun y ↦ (g y)⁻¹ • fderiv ℝ g y +
        (QuotientLineConnection.coordinateForm D e c (F y)).comp (fderiv ℝ F y)) z v w -
      fderiv ℝ (fun y ↦ (g y)⁻¹ • fderiv ℝ g y +
        (QuotientLineConnection.coordinateForm D e c (F y)).comp (fderiv ℝ F y)) z w v =
      fderiv ℝ (QuotientLineConnection.coordinateForm D e c) (F z)
          (fderiv ℝ F z v) (fderiv ℝ F z w) -
        fderiv ℝ (QuotientLineConnection.coordinateForm D e c) (F z)
          (fderiv ℝ F z w) (fderiv ℝ F z v) := by
  apply scalar_gauge_pullback_curvature _ hF hg hg0
  exact ((hD V e c hc).contDiffAt
    ((c.isOpen_inter_preimage_symm V.isOpen).mem_nhds hz)).differentiableAt (by simp)

end HolomorphicAnosov.ConnectionCalculus
