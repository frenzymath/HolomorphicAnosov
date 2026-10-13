import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.Manifold.OneParameterSmoothGenerator
import HolomorphicAnosov.Geometry.Manifold.VectorActionSpatialDerivativesContinuous
import HolomorphicAnosov.Geometry.Biholomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold

universe u v
namespace HolomorphicAnosov.Paper.Zhang
open scoped ContDiff Topology _root_.Topology
open Set Filter

set_option backward.isDefEq.respectTransparency false in
/-- For an additive real action, the orbit velocity at any time is the generator field evaluated at
the orbit point. (Bochner–Montgomery, eqs. (26)–(27), pp. 691–692) -/
theorem shifted_generator_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    (a : ℝ → M → M)
    (hadd : ∀ s t x, a s (a t x) = a (s+t) x)
    (X : (x : M) → TangentSpace (modelWithCornersSelf ℝ E) x)
    (hX : ∀ x, ∃ L : TangentSpace (modelWithCornersSelf ℝ ℝ) 0 →L[ℝ]
          TangentSpace (modelWithCornersSelf ℝ E) (a 0 x),
      HasMFDerivAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E)
        (fun s ↦ a s x) 0 L ∧
      X x = tangentSpaceCast (modelWithCornersSelf ℝ E) (a 0 x) x
        (L ((tangentSpaceCastModel (modelWithCornersSelf ℝ ℝ) 0).symm 1)))
    (x : M) (t : ℝ) :
    HasMFDerivAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E)
      (fun s ↦ a s x) t ((1 : ℝ →L[ℝ] ℝ).smulRight (X (a t x))) := by
  obtain ⟨L,hL,hvalue⟩ := hX (a t x)
  have hsub := ((hasDerivAt_id t).sub_const t).hasFDerivAt.hasMFDerivAt
  have hL' : HasMFDerivAt (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ E)
      (fun s ↦ a s (a t x)) (t-t) L := by
    convert hL using 1
    first | rfl | simp
  have hcomp := hL'.comp t (f := fun s : ℝ ↦ s-t) hsub
  have heq : (fun s ↦ a (s-t) (a t x)) = (fun s ↦ a s x) := by
    funext s; rw [hadd]; congr 1; ring
  have hd := hcomp.congr_of_eventuallyEq_abuse
    (Filter.Eventually.of_forall (congrFun heq.symm))
  apply hd.congr_mfderiv
  apply ContinuousLinearMap.ext
  intro r
  change ℝ at r
  let ell : ℝ →L[ℝ] E :=
    (tangentSpaceCastModel (modelWithCornersSelf ℝ E) (a 0 (a t x))).toContinuousLinearMap ∘L
      L ∘L (tangentSpaceCastModel (modelWithCornersSelf ℝ ℝ) 0).symm.toContinuousLinearMap
  have hx : (X (a t x) : E) = ell 1 := hvalue
  have hleft : (L ((ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) r) : E) = ell r := by
    congr 1
    change r * 1 = r
    ring
  have hright : ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (X (a t x))) r : E) =
      r • (X (a t x) : E) := by
    rfl
  change (L ((ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) r) : E) =
    ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (X (a t x))) r : E)
  rw [hleft, hright, hx]
  simpa using ell.map_smul r (1 : ℝ)


end HolomorphicAnosov.Paper.Zhang
