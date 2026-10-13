import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.FullSourceFrame
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.ChartVectorTransition
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.CoordinateCoefficientDifferentiable
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.Bilinear
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.Representation
import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
namespace ConnectionChristoffelLocal
/-- This is the Christoffel change-of-coordinates formula on a common chart domain. (Andrews, Exercise 8.3.2) -/
theorem fullSource_christoffel_transition (nabla : SmoothAffineConnection E M)
    (U : Opens M) {n m : ℕ} (b : Basis (Fin n) ℝ E) (d : Basis (Fin m) ℝ E)
    (c c' : OpenPartialHomeomorph U E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ U)
    (hc' : c' ∈ maximalAtlas 𝓘(ℝ, E) ∞ U)
    (hcs : c.source = univ) (hcs' : c'.source = univ)
    (Γ : Fin n → Fin n → Fin n → U → ℝ)
    (Δ : Fin m → Fin m → Fin m → U → ℝ)
    (hΓ : RepresentsCoefficients nabla U b c Γ)
    (hΔ : RepresentsCoefficients nabla U d c' Δ) (p : U) (u v : E) :
    let h := c' ∘ c.symm
    coefficientBilinear d Δ p (fderiv ℝ h (c p) u) (fderiv ℝ h (c p) v) =
      fderiv ℝ h (c p) (coefficientBilinear b Γ p u v) -
        fderiv ℝ (fderiv ℝ h) (c p) u v := by
  classical
  let h := c' ∘ c.symm
  have hp (q : U) : q ∈ c.source := by rw [hcs]; trivial
  have hp' (q : U) : q ∈ c'.source := by rw [hcs']; trivial
  obtain ⟨X, hX⟩ := HolomorphicAnosov.exists_coordinate_frame_of_source_eq_univ c hc hcs u
  obtain ⟨Y, hY⟩ := HolomorphicAnosov.exists_coordinate_frame_of_source_eq_univ c hc hcs v
  have hh (z : E) (hz : z ∈ c.target) : ContDiffAt ℝ ∞ h z :=
    ((contMDiffAt_of_mem_maximalAtlas hc' (hp' (c.symm z))).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas hc hz)).contDiffAt
  have hh₁ := (hh (c p) (c.map_source (hp p))).differentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hh₂ := ((hh (c p) (c.map_source (hp p))).fderiv_right (m := 1) (by simp)).differentiableAt (by simp)
  have hXp (q : U) : mvfderiv 𝓘(ℝ, E) c' q (X q) = fderiv ℝ h (c q) u := by
    rw [chartVector_transition U c c' hc hc' q (hp q) (hp' q), hX q]
  have hYp (q : U) : mvfderiv 𝓘(ℝ, E) c' q (Y q) = fderiv ℝ h (c q) v := by
    rw [chartVector_transition U c c' hc hc' q (hp q) (hp' q), hY q]
  have hYconst (k : Fin n) : LocalSmoothVectorField.coordinateCoefficient b c Y k =ᶠ[𝓝 (c p)]
      fun _ ↦ b.repr v k := by
    filter_upwards [c.open_target.mem_nhds (c.map_source (hp p))] with z hz
    exact congrArg (fun w ↦ b.repr w k) (hY (c.symm z))
  have hcov : mvfderiv 𝓘(ℝ, E) c p (nabla.cov U X Y p) = coefficientBilinear b Γ p u v := by
    apply b.repr.injective
    ext k
    have hk := hΓ X Y p (hp p) k
    have hderiv : fderiv ℝ (LocalSmoothVectorField.coordinateCoefficient b c Y k) (c p) = 0 := by
      rw [(hYconst k).fderiv_eq]
      exact fderiv_const_apply _
    simp only [LocalSmoothVectorField.tangentCoefficient, hX p, hY p, hderiv,
      zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at hk
    simpa [coefficientBilinear, map_sum, map_smul, Finsupp.sum_apply,
      Finsupp.smul_apply, b.repr_self_apply, Finsupp.single_apply, smul_eq_mul] using hk
  have hderivative (k : Fin m) :
      fderiv ℝ (LocalSmoothVectorField.coordinateCoefficient d c' Y k) (c' p) (fderiv ℝ h (c p) u) =
        d.repr (fderiv ℝ (fderiv ℝ h) (c p) u v) k := by
    have heq : (LocalSmoothVectorField.coordinateCoefficient d c' Y k ∘ h) =ᶠ[𝓝 (c p)]
        (fun z ↦ d.repr (fderiv ℝ h z v) k) := by
      filter_upwards [c.open_target.mem_nhds (c.map_source (hp p))] with z hz
      have hz' : c (c.symm z) = z := c.right_inv hz
      change d.repr (mvfderiv 𝓘(ℝ, E) c' (c'.symm (c' (c.symm z)))
        (Y (c'.symm (c' (c.symm z))))) k = _
      rw [c'.left_inv (hp' (c.symm z)), hYp (c.symm z), hz']
    have hkD := fullSource_coordinateCoefficient_differentiableAt U d c' hc' hcs' Y p k
    have hcp : h (c p) = c' p := by dsimp [h]; rw [c.left_inv (hp p)]
    have hkH : HasFDerivAt (LocalSmoothVectorField.coordinateCoefficient d c' Y k)
        (fderiv ℝ (LocalSmoothVectorField.coordinateCoefficient d c' Y k) (c' p))
        (h (c p)) := hcp.symm ▸ hkD.hasFDerivAt
    have hcomp := hkH.comp (c p) hh₁.hasFDerivAt
    have happly := hh₂.hasFDerivAt.clm_apply ((hasFDerivAt_const (𝕜 := ℝ) (E := E) (F := E) v (c p)))
    have hright := (d.coord k).toContinuousLinearMap.hasFDerivAt.comp (c p) happly
    have hfunc : fderiv ℝ (LocalSmoothVectorField.coordinateCoefficient d c' Y k ∘ h) (c p) =
        fderiv ℝ (fun z ↦ d.repr (fderiv ℝ h z v) k) (c p) := heq.fderiv_eq
    have hfuncu := congrArg (fun L : E →L[ℝ] ℝ ↦ L u) hfunc
    rw [hcomp.fderiv] at hfuncu
    have hrightu := congrArg (fun L : E →L[ℝ] ℝ ↦ L u) hright.fderiv
    have hrightu' : (fderiv ℝ (fun z ↦ d.repr (fderiv ℝ h z v) k) (c p)) u =
        (d.repr (fderiv ℝ (fderiv ℝ h) (c p) u v)) k := by
      simpa [Function.comp_def, ContinuousLinearMap.comp_apply] using hrightu
    exact hfuncu.trans hrightu'
  have htransition := chartVector_transition U c c' hc hc' p (hp p) (hp' p) (nabla.cov U X Y p)
  rw [hcov] at htransition
  apply d.repr.injective
  ext k
  have hk := hΔ X Y p (hp' p) k
  have hsum : (∑ i, d.repr (fderiv ℝ h (c p) u) i *
      fderiv ℝ (LocalSmoothVectorField.coordinateCoefficient d c' Y k) (c' p) (d i)) =
      fderiv ℝ (LocalSmoothVectorField.coordinateCoefficient d c' Y k) (c' p) (fderiv ℝ h (c p) u) := by
    have hs := congrArg (fderiv ℝ (LocalSmoothVectorField.coordinateCoefficient d c' Y k) (c' p))
      (d.sum_repr (fderiv ℝ h (c p) u))
    simpa only [map_sum, map_smul, smul_eq_mul] using hs
  simp only [LocalSmoothVectorField.tangentCoefficient, hXp p, hYp p,
    htransition, hsum, hderivative k] at hk
  simp only [map_sub, Finsupp.sub_apply]
  have hleft : d.repr (coefficientBilinear d Δ p (fderiv ℝ h (c p) u)
      (fderiv ℝ h (c p) v)) k =
      ∑ i, ∑ j, d.repr (fderiv ℝ h (c p) u) i * d.repr (fderiv ℝ h (c p) v) j * Δ i j k p := by
    simp [coefficientBilinear, map_sum, map_smul, Finsupp.single_apply, smul_eq_mul]
  rw [hleft]
  linarith

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
