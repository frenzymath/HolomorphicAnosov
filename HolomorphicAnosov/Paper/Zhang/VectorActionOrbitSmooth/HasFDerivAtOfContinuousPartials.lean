import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.Manifold.OneParameterSmoothGenerator
import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialDerivativesContinuous
import HolomorphicAnosov.Geometry.Biholomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import HolomorphicAnosov.Paper.Zhang.VectorActionOrbitSmooth.PartialDerivativeMap

universe u v
namespace HolomorphicAnosov.Paper.Zhang
open scoped ContDiff Topology _root_.Topology
open Set Filter

/-- A function with continuous coordinate partial derivatives on an open set has Fréchet derivative
`partialDerivativeMap` of those partials. (Bochner–Montgomery, eq. (27), p. 692) -/
theorem hasFDerivAt_of_continuous_partials
    {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → F}
    {H : (Fin n → ℝ) → Fin n → F} (hs : IsOpen s)
    (hH : ∀ i, ContinuousOn (fun x ↦ H x i) s)
    (hd : ∀ x ∈ s, ∀ i, HasDerivAt (fun t ↦ f (Function.update x i t)) (H x i) (x i)) :
    ∀ x ∈ s, HasFDerivAt f (partialDerivativeMap (H x)) x := by
  induction n with
  | zero =>
    intro x hx
    have he : f = fun _ ↦ f x := by
      funext y
      congr 1
      exact Subsingleton.elim y x
    rw [he]
    simpa [partialDerivativeMap] using (hasFDerivAt_const (f x) x)
  | succ n ih =>
    let e : (ℝ × (Fin n → ℝ)) ≃L[ℝ] (Fin (n+1) → ℝ) :=
      (Fin.consLinearEquiv ℝ (fun _ ↦ ℝ)).toContinuousLinearEquiv
    let g : ℝ → (Fin n → ℝ) → F := fun a b ↦ f (e (a,b))
    let A : ℝ → (Fin n → ℝ) → ℝ →L[ℝ] F :=
      fun a b ↦ (1 : ℝ →L[ℝ] ℝ).smulRight (H (e (a,b)) 0)
    let B : ℝ → (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] F :=
      fun a b ↦ partialDerivativeMap (fun i ↦ H (e (a,b)) i.succ)
    intro x hx
    have hx' : e.symm x ∈ e ⁻¹' s := by simpa using hx
    have hp1 : ∀ᶠ z in 𝓝 (e.symm x), HasFDerivAt (g · z.2) (A z.1 z.2) z.1 := by
      filter_upwards [(hs.preimage e.continuous).mem_nhds hx'] with z hz
      have hh := (hd (e z) hz 0).hasFDerivAt
      have heq : (fun t ↦ g t z.2) = (fun t ↦ f (Function.update (e z) 0 t)) := by
        funext t
        apply congrArg f
        ext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [e, Function.update]
      rw [heq]
      convert hh using 1
      · ext; simp [A]
      · simp [e]
    have hp2 : ∀ᶠ z in 𝓝 (e.symm x), HasFDerivAt (g z.1 ·) (B z.1 z.2) z.2 := by
      filter_upwards [(hs.preimage e.continuous).mem_nhds hx'] with z hz
      change HasFDerivAt (fun y ↦ f (e (z.1,y)))
        (partialDerivativeMap (fun i ↦ H (e (z.1,z.2)) i.succ)) z.2
      refine ih (f := fun y ↦ f (e (z.1,y)))
        (H := fun y i ↦ H (e (z.1,y)) i.succ)
        (hs.preimage (e.continuous.comp (continuous_const.prodMk continuous_id))) ?_ ?_ z.2 hz
      · intro i
        exact (hH i.succ).comp
          (e.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn (by
          intro y hy; exact hy)
      · intro y hy i
        convert hd (e (z.1,y)) hy i.succ using 1
        · funext t
          apply congrArg f
          ext j
          refine Fin.cases ?_ (fun k ↦ ?_) j <;>
            simp [e, Function.update, Ne.symm (Fin.succ_ne_zero _)]
        · simp [e]
    have hc1 : ContinuousAt (Function.uncurry A) (e.symm x) := by
      exact (ContinuousLinearMap.smulRightL ℝ ℝ F 1).continuous.continuousAt.comp
        ((show ContinuousAt (fun y ↦ H y 0) (e (e.symm x)) from by
          simpa using (hH 0).continuousAt (hs.mem_nhds hx)).comp e.continuous.continuousAt)
    have hc2 : ContinuousAt (Function.uncurry B) (e.symm x) := by
      change ContinuousAt (fun z ↦ ∑ i : Fin n,
        (ContinuousLinearMap.proj i).smulRight (H (e z) i.succ)) (e.symm x)
      apply tendsto_finsetSum
      intro i hi
      exact (ContinuousLinearMap.smulRightL ℝ (Fin n → ℝ) F
        (ContinuousLinearMap.proj i)).continuous.continuousAt.comp
        ((show ContinuousAt (fun y ↦ H y i.succ) (e (e.symm x)) from by
          simpa using (hH i.succ).continuousAt (hs.mem_nhds hx)).comp e.continuous.continuousAt)
    have hh := (hasStrictFDerivAt_uncurry_coprod
      (f := g) (f₁ := A) (f₂ := B) hp1 hp2 hc1 hc2).hasFDerivAt
    have hh' := hh.comp x e.symm.hasFDerivAt
    convert hh' using 1
    · funext y; change f y = f (e (e.symm y)); simp
    · ext y
      change (partialDerivativeMap (H x)) y =
        (A (e.symm x).1 (e.symm x).2) (e.symm y).1 +
        (B (e.symm x).1 (e.symm x).2) (e.symm y).2
      have hcons : (Fin.consLinearEquiv ℝ (fun _ : Fin (n+1) ↦ ℝ)) (x 0, Fin.tail x) = x := by
        ext i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
      simp [partialDerivativeMap, A, B, e, Fin.sum_univ_succ, hcons, Fin.tail]


end HolomorphicAnosov.Paper.Zhang
