import HolomorphicAnosov.Dynamics.HirschPughNativeLeafSystem
import HolomorphicAnosov.Geometry.Riemannian.PiecewiseSmoothPath
import HolomorphicAnosov.Geometry.Riemannian.ConnectedSmoothPathExists

/-!
# Piecewise-smooth path witnesses on native leaves

Source: Lee, *Introduction to Smooth Manifolds* (2003), Lemma 6.17,
pp.139–140, and Hirsch–Pugh–Shub (1977), §6B, pp.111–114.  The connected
finite-dimensional native smooth leaf is joined by finite coordinate-ball
pieces, and those pieces are assembled into the project's exact
`RiemannianPiecewiseSmoothPath` carrier.
-/

noncomputable section
open scoped ContDiff Manifold ENNReal
namespace HolomorphicAnosov

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Any two points of a native smooth leaf admit a finite piecewise-smooth path
in the exact path carrier used by `nativeLeafPathEDist`. -/
theorem nativeLeaf_piecewiseSmoothPath_exists
    {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ, E) x)}
    {x : M} (L : NativeSmoothLeaf 𝓘(ℝ, E) D x)
    (y z : L.Carrier) :
    Nonempty (RiemannianPiecewiseSmoothPath 𝓘(ℝ, Fin L.rank → ℝ) y z) := by
  obtain ⟨c, hc, hc0, hc1⟩ :=
    connected_smooth_path_exists (E := Fin L.rank → ℝ) (M := L.Carrier) y z
  let t : Fin 2 → ℝ := fun i ↦ (i : ℝ)
  have ht : StrictMono t := by
    intro i j hij
    simpa [t] using (show (i : ℝ) < (j : ℝ) by exact_mod_cast hij)
  have ht0 : t 0 = 0 := by simp [t]
  have ht1 : t (Fin.last 1) = 1 := by simp [t]
  refine ⟨{
    n := 0
    time := t
    time_strictMono := ht
    time_zero := ht0
    time_one := ht1
    piece := fun _ ↦ c
    piece_smooth := fun i ↦ by
      fin_cases i
      simpa [t] using hc.contMDiffOn
    source := by simpa using hc0
    target := by simpa using hc1
    junction := fun i ↦ Fin.elim0 i }⟩

end HolomorphicAnosov
