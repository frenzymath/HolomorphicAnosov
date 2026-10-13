import HolomorphicAnosov.Geometry.ConnectionChristoffelRegularity

/-!
Smoothness of the coordinate geodesic spray. (Andrews, Prop. 8.3.1, p.74; Prop. 8.11.2, p.84)
-/

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The coordinate geodesic spray `(v, -Γ(v, v))` is smooth on the tangent chart domain. (Andrews,
Prop. 8.11.2 and Ex. 8.11.3, p.84) -/
theorem connectionSprayCoordinate_contDiffOn (nabla : SmoothAffineConnection E M)
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M)) :
    ContDiffOn ℝ ∞ (fun z : E × E ↦ (z.2,
      -connectionChristoffelBilinear nabla b c hc (connectionChartInverse c z.1) z.2 z.2))
      (c.target ×ˢ (univ : Set E)) := by
  have hv (i : Fin n) : ContDiffOn ℝ ∞ (fun z : E × E ↦ b.repr z.2 i)
      (c.target ×ˢ (univ : Set E)) :=
    ((b.coord i).toContinuousLinearMap.contDiff.comp contDiff_snd).contDiffOn
  have hΓ (i j k : Fin n) : ContDiffOn ℝ ∞
      (fun z : E × E ↦ connectionChristoffel nabla b c hc i j k (c.symm z.1))
      (c.target ×ˢ (univ : Set E)) :=
    (connectionChristoffel_contDiffOn nabla b c hc i j k).comp contDiffOn_fst
      (fun _ hz ↦ hz.1)
  apply contDiffOn_snd.prodMk
  apply ContDiffOn.neg
  unfold connectionChristoffelBilinear connectionChartInverse
  apply ContDiffOn.sum
  intro k hk
  apply ContDiffOn.smul_const
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro j hj
  exact ((hv i).mul (hv j)).mul (hΓ i j k)

end
end HolomorphicAnosov

