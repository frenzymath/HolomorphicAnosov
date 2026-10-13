import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Radial integrating factors for flat quotient-line connections. (Zhang, Lemma 2.4, p. 7;
Demailly, V.3, p. 256) -/

noncomputable section
namespace HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
open Set TopologicalSpace
open scoped ContDiff Manifold
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
universe u

/-- A flat quotient-line connection admits a nowhere-zero radial integrating factor satisfying `dg =
-gA` on a ball in any frame/chart overlap. (Zhang, Lemma 2.4, p. 7) -/
theorem flat_coordinate_integrating_factor
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (nabla : QuotientLineConnection.Connection U)
    (hflat : QuotientLineConnection.IsFlat nabla)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame U V)
    (c : OpenPartialHomeomorph X (ComplexModel d))
    (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
    (x : X) (hxc : x ∈ c.source) (hxV : x ∈ V) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (c x) r ⊆ c.target ∩ c.symm ⁻¹' (V : Set X) ∧
      let P := fun z ↦ curveIntegral (QuotientLineConnection.coordinateForm nabla e c)
        (Path.segment (c x) z)
      ∀ z ∈ Metric.ball (c x) r,
        HasFDerivAt P (QuotientLineConnection.coordinateForm nabla e c z) z ∧
        Complex.exp (-P z) ≠ 0 ∧
        HasFDerivAt (fun w ↦ Complex.exp (-P w))
          (-(Complex.exp (-P z)) • QuotientLineConnection.coordinateForm nabla e c z) z := by
  let A := QuotientLineConnection.coordinateForm nabla e c
  have hopen : IsOpen (c.target ∩ c.symm ⁻¹' (V : Set X)) :=
    c.isOpen_inter_preimage_symm V.isOpen
  have hx : c x ∈ c.target ∩ c.symm ⁻¹' (V : Set X) :=
    ⟨c.map_source hxc, by
      change c.symm (c x) ∈ V
      rw [c.left_inv hxc]
      exact hxV⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen (c x) hx
  obtain ⟨hdiff, hsymm⟩ := hflat V e c hc
  have hA (z) (hz : z ∈ Metric.ball (c x) r) :
      HasFDerivAt A (fderiv ℝ A z) z :=
    ((hdiff z (hball hz)).differentiableAt
      (hopen.mem_nhds (hball hz))).hasFDerivAt
  refine ⟨r, hr, hball, ?_⟩
  dsimp only
  intro z hz
  have hP : HasFDerivAt (fun w ↦ curveIntegral A (Path.segment (c x) w)) (A z) z :=
    ((convex_ball (c x) r).hasFDerivWithinAt_curveIntegral_segment_of_hasFDerivWithinAt_symmetric
      (fun w hw ↦ (hA w hw).hasFDerivWithinAt)
      (fun w hw v _ v' _ ↦ sub_eq_zero.mp (hsymm w (hball hw) v v'))
      (Metric.mem_ball_self hr) hz).hasFDerivAt (Metric.isOpen_ball.mem_nhds hz)
  refine ⟨hP, Complex.exp_ne_zero _, ?_⟩
  have hexp := hP.neg.cexp
  change HasFDerivAt (fun w ↦ Complex.exp (-curveIntegral A (Path.segment (c x) w)))
    (Complex.exp (-curveIntegral A (Path.segment (c x) z)) • -(A z)) z at hexp
  rw [smul_neg, ← neg_smul] at hexp
  exact hexp

end HolomorphicAnosov.Paper.Zhang.TransverseParallelSupport
