import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov

/-- HPS pp.57–58: derivative of a continuous local preimage graph of an
affine receiving graph. Let L=(π₁−Pπ₂)F be the linearized graph equation,
J=L|X its invertible horizontal block and B=L|Y its vertical block.
The map z ↦ (G₁(z)−P(G₂(z)),z₂) has block derivative (J B;0 Id).
Its continuous linear left inverse is (u,v) ↦ (J⁻¹(u−Bv),v).
On the actual preimage graph the map equals y ↦ (0,y). The derivative
of a composition with an invertible outer derivative therefore identifies
the graph derivative, even though only its continuity was known beforehand.
Projection gives Ds=−J⁻¹B. No inverse of the lower block or return is used. -/
theorem parameter_graph_preimage_derivative
    {X Y U V : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : X × Y → U × V) (P : V →L[ℝ] U) (s : Y → X) (y : Y)
    (hs : ContinuousAt s y)
    (heq : ∀ᶠ v in 𝓝 y, (G (s v,v)).1 = P (G (s v,v)).2)
    (F : X × Y →L[ℝ] U × V) (hF : HasFDerivAt G F (s y,y))
    (J : X ≃L[ℝ] U)
    (hJ : ∀ x, J x = (F (x,0)).1 - P (F (x,0)).2) :
    HasFDerivAt s
      (-(J.symm.toContinuousLinearMap.comp
        (((ContinuousLinearMap.fst ℝ U V).comp F -
          P.comp ((ContinuousLinearMap.snd ℝ U V).comp F)).comp
            (ContinuousLinearMap.inr ℝ X Y)))) y := by
  let L : X × Y →L[ℝ] U :=
    (ContinuousLinearMap.fst ℝ U V).comp F - P.comp ((ContinuousLinearMap.snd ℝ U V).comp F)
  let B : Y →L[ℝ] U := L.comp (ContinuousLinearMap.inr ℝ X Y)
  let D : X × Y →L[ℝ] U × Y := L.prod (ContinuousLinearMap.snd ℝ X Y)
  let K : U × Y →L[ℝ] X × Y :=
    (J.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.fst ℝ U Y - B.comp (ContinuousLinearMap.snd ℝ U Y))).prod
      (ContinuousLinearMap.snd ℝ U Y)
  have hL (x : X) (v : Y) : L (x,v) = J x + B v := by
    have hsplit : (x,v) = (x,0) + (0,v) := by simp
    rw [hsplit, map_add]
    change L (x,0) + B v = J x + B v
    rw [hJ]
    rfl
  have hleft : Function.LeftInverse K D := by
    rintro ⟨x,v⟩
    change (J.symm (L (x,v) - B v),v) = (x,v)
    rw [hL, add_sub_cancel_right, J.symm_apply_apply]
  have hd : HasFDerivAt (fun z : X × Y ↦ ((G z).1 - P (G z).2,z.2)) D (s y,y) := by
    exact (hF.fst.sub (P.hasFDerivAt.comp (s y,y) hF.snd)).prodMk
      hasFDerivAt_snd
  have hcomp : (fun z : X × Y ↦ ((G z).1 - P (G z).2,z.2)) ∘
      (fun v ↦ (s v,v)) =ᶠ[𝓝 y] (fun v ↦ ((0 : U),v)) := by
    filter_upwards [heq] with v hv
    simp only [Function.comp_apply, hv, sub_self]
  have hg := HasFDerivAt.of_comp_of_leftInverse
    (hs.prodMk continuousAt_id) hd ((hasFDerivAt_const (0 : U) y).prodMk (hasFDerivAt_id y))
    hcomp hleft
  have hfst := hg.fst
  convert hfst using 1
  ext v
  change -(J.symm (B v)) = J.symm (0 - B v)
  simp

end HolomorphicAnosov
