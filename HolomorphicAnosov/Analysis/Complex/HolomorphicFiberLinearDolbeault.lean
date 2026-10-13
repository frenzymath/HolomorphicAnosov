import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

namespace HolomorphicAnosov

/-- A holomorphic function on base times fibre which is linear on the fixed fibre
commutes with the antiholomorphic derivative of a differentiable section.
Source: Demailly I §3.C pp.22–24 and V §11 (11.1), p.267. Apply the real chain
rule to the graph of the section. The derivative in the fibre direction is the
specified linear map, by derivative uniqueness on the fixed fibre. The base
terms cancel in the half-sum because the total derivative is complex linear. -/
theorem holomorphic_fiber_linear_dolbeault
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (H : E × F → ℂ) (a : E → F) (x : E) (L : F →L[ℂ] ℂ)
    (hH : DifferentiableAt ℂ H (x, a x)) (ha : DifferentiableAt ℝ a x)
    (hL : ∀ w, H (x, w) = L w) (v : E) :
    (1 / 2 : ℂ) * (fderiv ℝ (fun y ↦ H (y, a y)) x v +
      Complex.I * fderiv ℝ (fun y ↦ H (y, a y)) x (Complex.I • v)) =
      L ((1 / 2 : ℂ) • (fderiv ℝ a x v +
        Complex.I • fderiv ℝ a x (Complex.I • v))) := by
  let K := fderiv ℂ H (x, a x)
  have hvertical : ∀ w, K (0, w) = L w := by
    have hc := hH.hasFDerivAt.comp (a x)
      ((hasFDerivAt_const x (a x)).prodMk (hasFDerivAt_id (a x)))
    have heq : (fun w ↦ H (x, w)) = L := funext hL
    change HasFDerivAt (fun w ↦ H (x, w)) _ (a x) at hc
    rw [heq] at hc
    have hh := hc.unique L.hasFDerivAt
    intro w
    exact congrArg (fun T ↦ T w) hh
  have hgraph := (hH.hasFDerivAt.restrictScalars ℝ).comp x
    ((hasFDerivAt_id x).prodMk ha.hasFDerivAt)
  change HasFDerivAt (fun y ↦ H (y, a y)) _ x at hgraph
  rw [hgraph.fderiv]
  change (1 / 2 : ℂ) * (K (v, fderiv ℝ a x v) +
    Complex.I * K (Complex.I • v, fderiv ℝ a x (Complex.I • v))) = _
  have hsplit (u : E) (w : F) : K (u, w) = K (u, 0) + L w := by
    rw [← hvertical, ← map_add]
    simp
  rw [hsplit v (fderiv ℝ a x v), hsplit (Complex.I • v) (fderiv ℝ a x (Complex.I • v))]
  have hbase : K (Complex.I • v, 0) = Complex.I * K (v, 0) := by
    simpa only [Prod.smul_mk, smul_zero, smul_eq_mul] using K.map_smul Complex.I (v, 0)
  rw [hbase]
  simp only [map_smul, map_add, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

end HolomorphicAnosov
