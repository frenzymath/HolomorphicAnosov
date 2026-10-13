import HolomorphicAnosov.Dynamics.HirschPughHyperbolicSetFactOne
import HolomorphicAnosov.Dynamics.HirschPughNativeLeafSystem
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPathMap

namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

local notation "I" => 𝓘(ℝ, E)

/-- Pointwise speed contraction for the actual advanced native path.

Agent-written chain-rule step in the intrinsic-length argument of
`hirschPughAdaptedOrbitPlaques`, using Lee (2003), p.275's speed convention.
The source path velocity lies in the source inclusion's derivative range, hence
in the given tangent distribution. The commuting inclusion equation identifies
the actual advanced ambient curve with the original map composed with the source
ambient curve. The within-interval chain rule then applies the given tangent
bound, including both endpoints of every nondegenerate closed piece. -/
theorem nativeLeafPath_advance_speed_le
    (f : Diffeomorph I I M M ∞)
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}
    (S : NativeInvariantLeafSystem I D f)
    (h : Bundle.ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (θ : ℝ)
    (hθ : ∀ (x : M) (v : TangentSpace I x), v ∈ D x →
      hyperbolicRiemannianNorm h (mfderiv I I f x v) ≤ θ * hyperbolicRiemannianNorm h v)
    (x : M) {y z : (S.leaf x).Carrier}
    (p : RiemannianPiecewiseSmoothPath 𝓘(ℝ, Fin (S.leaf x).rank → ℝ) y z)
    (i : Fin (p.n + 1)) {t : ℝ} (ht : t ∈ p.pieceInterval i) :
    (((p.map (S.advance x) (S.advance x).contMDiff).map
      (S.leaf (f x)).inclusion (S.leaf (f x)).inclusion_smooth).speed h i t) ≤
      θ * ((p.map (S.leaf x).inclusion (S.leaf x).inclusion_smooth).speed h i t) := by
  let c := p.map (S.leaf x).inclusion (S.leaf x).inclusion_smooth
  let q := (p.map (S.advance x) (S.advance x).contMDiff).map
    (S.leaf (f x)).inclusion (S.leaf (f x)).inclusion_smooth
  have hcurve : q.piece i = f ∘ c.piece i := by
    funext u
    exact S.inclusion_advance x (p.piece i u)
  have hunique := (uniqueDiffOn_Icc (p.time_strictMono Fin.castSucc_lt_succ)).uniqueMDiffOn t ht
  have hp := ((p.piece_smooth i).mdifferentiableOn (by simp)) t ht
  have hc := ((c.piece_smooth i).mdifferentiableOn (by simp)) t ht
  have hinc := (S.leaf x).inclusion_smooth.mdifferentiable (by simp)
  have htan : c.velocity i t ∈ D (c.piece i t) := by
    change (mfderivWithin 𝓘(ℝ) I ((S.leaf x).inclusion ∘ p.piece i)
      (p.pieceInterval i) t (show TangentSpace 𝓘(ℝ) t from (1 : ℝ))) ∈ D ((S.leaf x).inclusion (p.piece i t))
    erw [mfderiv_comp_mfderivWithin t (hinc _) hp hunique,
      ← (S.leaf x).inclusion_tangent (p.piece i t)]
    exact ⟨p.velocity i t, rfl⟩
  change hyperbolicRiemannianNorm h (q.velocity i t) ≤
    θ * hyperbolicRiemannianNorm h (c.velocity i t)
  unfold RiemannianPiecewiseSmoothPath.velocity
  change hyperbolicRiemannianNorm h
    (mfderivWithin 𝓘(ℝ) I (q.piece i) (p.pieceInterval i) t (show TangentSpace 𝓘(ℝ) t from (1 : ℝ))) ≤ _
  rw [hcurve]
  erw [mfderiv_comp_mfderivWithin t (f.contMDiff.mdifferentiable (by simp) _) hc hunique]
  exact hθ _ _ htan

end HolomorphicAnosov
