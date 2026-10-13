import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Commuting a parameter derivative with spatial jets

This expands the mixed-derivative interchange in the fixed-support Taylor estimate
of Dyatlov, *Lecture notes for 18.155* (2026), Proposition 6.3, pp. 68–69.
The proof uses Mathlib's Schwarz theorem and the recursive definition of spatial jets.
-/

noncomputable section
open Set Filter
open scoped Topology _root_.Topology ContDiff
namespace HolomorphicAnosov.Analysis

/-- A parameter directional derivative commutes with every spatial jet when all
spatial jet fields are jointly smooth on the product of two open sets.

Induct on the spatial order. Order zero is evaluation on the zero-fold multilinear
space. At the successor step the induction hypothesis identifies the previous jet
near the spatial point. The product chain rule identifies the two partial derivatives
with the full derivative evaluated on the two product injections. Schwarz symmetry
interchanges these directions. Differentiating multilinear evaluation and the spatial
jet recursion give the desired successor identity. No compactness or nonemptiness
of either open set is needed. -/
theorem parameter_spatial_iteratedFDerivWithin_commute {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {F : E × X → Y} {P : Set E} {U : Set X}
    (hP : IsOpen P) (hU : IsOpen U)
    (hJ : ∀ i : ℕ, ContDiffOn ℝ ∞
      (fun z : E × X ↦ iteratedFDerivWithin ℝ i (fun y ↦ F (z.1,y)) U z.2) (P ×ˢ U))
    (v : E) (i : ℕ) (p : E) (hp : p ∈ P) (y : X) (hy : y ∈ U) :
    iteratedFDerivWithin ℝ i (fun z ↦ fderiv ℝ (fun q ↦ F (q,z)) p v) U y =
      fderiv ℝ (fun q ↦ iteratedFDerivWithin ℝ i (fun z ↦ F (q,z)) U y) p v := by
  let J (j : ℕ) (z : E × X) := iteratedFDerivWithin ℝ j (fun y ↦ F (z.1,y)) U z.2
  have hJs (j : ℕ) (q : E) (hq : q ∈ P) (z : X) (hz : z ∈ U) :
      ContDiffAt ℝ ∞ (J j) (q,z) :=
    (hJ j).contDiffAt ((hP.prod hU).mem_nhds ⟨hq,hz⟩)
  have hJp (j : ℕ) : DifferentiableAt ℝ (fun q ↦ J j (q,y)) p :=
    ((hJs j p hp y hy).comp p (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  induction i generalizing y with
  | zero =>
    ext a
    change fderiv ℝ (fun q ↦ F (q,y)) p v = (fderiv ℝ (fun q ↦ J 0 (q,y)) p v) a
    exact fderiv_continuousMultilinear_apply_const_apply (hJp 0) a v
  | succ i ih =>
    ext a
    rw [iteratedFDerivWithin_succ_apply_left, fderivWithin_of_isOpen hU hy]
    have heq : (iteratedFDerivWithin ℝ i
        (fun z ↦ fderiv ℝ (fun q ↦ F (q,z)) p v) U) =ᶠ[𝓝 y]
        (fun z ↦ fderiv ℝ (fun q ↦ J i (q,z)) p v) := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact ih z hz (fun j ↦ ((hJs j p hp z hz).comp p
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
    rw [heq.fderiv_eq]
    have hswap : fderiv ℝ (fun z ↦ fderiv ℝ (fun q ↦ J i (q,z)) p v) y (a 0) =
        fderiv ℝ (fun q ↦ fderiv ℝ (fun z ↦ J i (q,z)) y (a 0)) p v := by
      let G := J i
      have hG : ContDiffAt ℝ ∞ G (p,y) := hJs i p hp y hy
      have hs : ∀ᶠ z in 𝓝 (p,y), DifferentiableAt ℝ G z :=
        ((hG.of_le (show (2 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)).mono
          (fun _ hz ↦ hz.differentiableAt (by simp))
      have hl : (fun z ↦ fderiv ℝ (fun q ↦ G (q,z)) p v) =ᶠ[𝓝 y]
          (fun z ↦ fderiv ℝ G (p,z) (v,0)) := by
        filter_upwards [(show ContinuousAt (fun z : X ↦ (p,z)) y from continuousAt_const.prodMk continuousAt_id).tendsto.eventually hs] with z hz
        have h := (hz.hasFDerivAt.comp p (hasFDerivAt_prodMk_left (𝕜 := ℝ) p z)).fderiv
        exact congrArg (fun A : E →L[ℝ] (X [×i]→L[ℝ] Y) ↦ A v) h
      have hr : (fun q ↦ fderiv ℝ (fun z ↦ G (q,z)) y (a 0)) =ᶠ[𝓝 p]
          (fun q ↦ fderiv ℝ G (q,y) (0,(a 0))) := by
        filter_upwards [(show ContinuousAt (fun q : E ↦ (q,y)) p from continuousAt_id.prodMk continuousAt_const).tendsto.eventually hs] with q hq
        have h := (hq.hasFDerivAt.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) q y)).fderiv
        exact congrArg (fun A : X →L[ℝ] (X [×i]→L[ℝ] Y) ↦ A (a 0)) h
      rw [hl.fderiv_eq, hr.fderiv_eq]
      have hd : DifferentiableAt ℝ (fderiv ℝ G) (p,y) := (hG.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
      have hdl0 : HasFDerivAt (fun z : X ↦ fderiv ℝ G (p,z))
          ((fderiv ℝ (fderiv ℝ G) (p,y)).comp (ContinuousLinearMap.inr ℝ E X)) y := by
        simpa only [Function.comp_def] using HasFDerivAt.comp (g := fderiv ℝ G) (f := fun z : X ↦ (p,z)) y hd.hasFDerivAt (hasFDerivAt_prodMk_right (𝕜 := ℝ) p y)
      have hdr0 : HasFDerivAt (fun q : E ↦ fderiv ℝ G (q,y))
          ((fderiv ℝ (fderiv ℝ G) (p,y)).comp (ContinuousLinearMap.inl ℝ E X)) p := by
        simpa only [Function.comp_def] using HasFDerivAt.comp (g := fderiv ℝ G) (f := fun q : E ↦ (q,y)) p hd.hasFDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) p y)
      have hdl := (hdl0.clm_apply (hasFDerivAt_const (𝕜 := ℝ) (v,(0 : X)) y)).fderiv
      have hdr := (hdr0.clm_apply (hasFDerivAt_const (𝕜 := ℝ) ((0 : E),a 0) p)).fderiv
      rw [hdl, hdr]
      simpa using (hG.isSymmSndFDerivAt (by simp)).eq (0,(a 0)) (v,0)
    rw [hswap]
    have hB : DifferentiableAt ℝ (fun q ↦ fderiv ℝ (fun z ↦ J i (q,z)) y (a 0)) p := by
      have hf : ContDiffAt ℝ ∞ (Function.uncurry (fun q : E ↦ fun z : X ↦ J i (q,z))) (p,y) :=
        hJs i p hp y hy
      exact ((hf.fderiv (m := ∞) contDiffAt_const (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
    rw [← fderiv_continuousMultilinear_apply_const_apply hB (Fin.tail a) v,
      ← fderiv_continuousMultilinear_apply_const_apply (hJp (i+1)) a v]
    congr 2
    funext q
    symm
    change (iteratedFDerivWithin ℝ (i+1) (fun z ↦ F (q,z)) U y) a = _
    rw [iteratedFDerivWithin_succ_apply_left, fderivWithin_of_isOpen hU hy]

end HolomorphicAnosov.Analysis

