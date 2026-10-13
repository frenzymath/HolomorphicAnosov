import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Geometry.Riemannian.Gauss.RadialGeodesic
import HolomorphicAnosov.Geometry.Riemannian.Gauss.FibreSmooth
import HolomorphicAnosov.Geometry.Riemannian.Gauss.VariationPairingDerivative
import HolomorphicAnosov.Geometry.Riemannian.Gauss.RadialConstantSpeed
import HolomorphicAnosov.Geometry.Riemannian.Gauss.VariationEndpointVelocities
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Inv

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix
namespace HolomorphicAnosov

/-- The exponential differential at a nonzero vector `v` sends `v` and every vector orthogonal to
`v` to orthogonal tangent vectors. (Gallier–Quaintance, Prop. 16.8, pp.452–454; Andrews, Prop.
11.1.1, pp.101–102) -/
theorem gauss_radial_orthogonality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (v w : TangentSpace 𝓘(ℝ, E) p)
    (hv : (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g)
    (hv0 : v ≠ 0) (hw : g.inner p v w = 0) :
    letI : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
    g.inner (riemannianExponential g ⟨p, v⟩)
      (mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E)
        (fun u ↦ riemannianExponential g ⟨p, u⟩) v
        ((NormedSpace.fromTangentSpace v).symm v))
      (mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E)
        (fun u ↦ riemannianExponential g ⟨p, u⟩) v
        ((NormedSpace.fromTangentSpace v).symm w)) = 0 := by
  let : RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let a : ℝ → TangentSpace 𝓘(ℝ, E) p := fun s ↦
    (‖v‖ / ‖v + s • w‖) • (v + s • w)
  let A : Set ℝ := {s | v + s • w ≠ 0}
  have hA : IsOpen A :=
    isOpen_ne_fun (continuous_const.add (continuous_id.smul continuous_const)) continuous_const
  have hA0 : (0 : ℝ) ∈ A := by simpa [A] using hv0
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
  have ha0 : a 0 = v := by simp [a, hn]
  have ha : ContDiffOn ℝ ∞ a A := by
    have hf : ContDiff ℝ ∞ (fun s : ℝ ↦ v + s • w) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    exact (contDiffOn_const.div (hf.contDiffOn.norm ℝ fun _ hs ↦ hs)
      (fun s hs ↦ norm_ne_zero_iff.mpr hs)).smul hf.contDiffOn
  have had : HasDerivAt a w 0 := by
    have hcurve : HasDerivAt (fun s : ℝ ↦ v + s • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
    have hs := hcurve.norm_sq.sqrt (by simpa using pow_ne_zero 2 hn)
    have hnorm : HasDerivAt (fun s : ℝ ↦ ‖v + s • w‖) 0 0 := by
      change inner ℝ v w = 0 at hw
      simpa only [Real.sqrt_sq (norm_nonneg _), zero_smul, add_zero, hw,
        mul_zero, zero_div] using hs
    have hdiv := (hasDerivAt_const (0 : ℝ) ‖v‖).div hnorm (by simpa using hn)
    have h := hdiv.smul hcurve
    change HasDerivAt a _ 0 at h
    simpa only [Pi.div_apply, zero_smul, add_zero, mul_zero, zero_mul, sub_self, zero_div,
      div_self hn, one_smul, zero_add] using h
  have hanorm (s : ℝ) (hs : s ∈ A) : g.inner p (a s) (a s) = g.inner p v v := by
    change inner ℝ (a s) (a s) = inner ℝ v v
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    dsimp only [a]
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hs)]
  let e : TangentSpace 𝓘(ℝ, E) p → M := fun u ↦ riemannianExponential g ⟨p, u⟩
  let D := riemannianExponentialDomain g
  obtain ⟨hD, _, he, hbase, _⟩ := riemannian_exponential_local_addition g
  let V : ℝ × ℝ → TangentSpace 𝓘(ℝ, E) p := fun z ↦ z.1 • a z.2
  let Ψ : ℝ × ℝ → TangentBundle 𝓘(ℝ, E) M := fun z ↦ ⟨p, V z⟩
  let W : Set (ℝ × ℝ) := Prod.snd ⁻¹' A
  have hW : IsOpen W := hA.preimage continuous_snd
  have hV : ContDiffOn ℝ ∞ V W :=
    contDiffOn_fst.smul (ha.comp contDiffOn_snd fun _ hz ↦ hz)
  have hΨ : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, E)).tangent ∞ Ψ W := by
    have hcoord := ((tangentSpaceCastModel 𝓘(ℝ, E) p).contDiff.comp_contDiffOn hV).contMDiffOn
    convert (tangentBundle_fixed_fibre_contMDiff p).comp_contMDiffOn hcoord using 1
    funext z
    simp only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  let U := W ∩ Ψ ⁻¹' D
  have hU : IsOpen U := hΨ.continuousOn.isOpen_inter_preimage hW hD
  let F : ℝ × ℝ → M := fun z ↦ e (z.1 • a z.2)
  have hF : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F U :=
    he.comp (hΨ.mono inter_subset_left) fun _ hz ↦ hz.2
  have hΨ0 : ContinuousAt (fun s : ℝ ↦ (⟨p, a s⟩ : TangentBundle 𝓘(ℝ, E) M)) 0 := by
    have h := hΨ.continuousOn.continuousAt
      (hW.mem_nhds (show ((1 : ℝ), (0 : ℝ)) ∈ W from hA0))
    have hh := h.comp (continuousAt_const.prodMk continuousAt_id)
    change ContinuousAt (fun s : ℝ ↦ (⟨p, (1 : ℝ) • a s⟩ : TangentBundle 𝓘(ℝ, E) M)) 0 at hh
    simpa only [one_smul] using hh
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), s ∈ A ∧
      (⟨p, a s⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ D :=
    Filter.Eventually.and (hA.mem_nhds hA0) (hΨ0.eventually (hD.mem_nhds (by simpa [ha0] using hv)))
  obtain ⟨J, hJ, hconn, hseg, hγ, hdom, _⟩ := gauss_radial_geodesic g p v hv
  have hsegment (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (t, 0) ∈ U := by
    exact ⟨hA0, by simpa [Ψ, V, ha0] using hdom t (hseg ht)⟩
  let T : (z : ℝ × ℝ) → TangentSpace 𝓘(ℝ, E) (F z) :=
    fun z ↦ curveVelocity (fun r ↦ F (r, z.2)) z.1
  let S : (z : ℝ × ℝ) → TangentSpace 𝓘(ℝ, E) (F z) :=
    fun z ↦ curveVelocity (fun q ↦ F (z.1, q)) z.2
  let f : ℝ → ℝ := fun t ↦ g.inner (F (t, 0)) (T (t, 0)) (S (t, 0))
  have hnonneg (q : M) (u : TangentSpace 𝓘(ℝ, E) q) : 0 ≤ g.inner q u u := by
    by_cases hu : u = 0
    · subst u; simp
    · exact (g.pos q u hu).le
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt f 0 t := by
    have hg : covariantDerivativeAlongCurve (riemannianConnection g)
        (fun r ↦ F (r, 0)) (curveVelocity (fun r ↦ F (r, 0))) t = 0 := by
      change covariantDerivativeAlongCurve (riemannianConnection g)
        (fun r ↦ e (r • a 0)) (curveVelocity (fun r ↦ e (r • a 0))) t = 0
      rw [ha0]
      exact hγ.2 t (hseg ht)
    have h := gauss_variation_pairing_derivative g F U hU hF t 0 (hsegment t ht) hg
    have heq : (fun s ↦ g.inner (F (t, s)) (T (t, s)) (T (t, s))) =ᶠ[𝓝 0]
        (fun _ ↦ g.inner p v v) := by
      filter_upwards [hsmall] with s hs
      have hv' := gauss_radial_constant_speed g p (a s) hs.2 t ht
      have heq' := (Real.sqrt_inj (hnonneg _ _) (hnonneg _ _)).mp hv'
      exact heq'.trans (hanorm s hs.1)
    have hz := (hasDerivAt_const (0 : ℝ) (g.inner p v v)).congr_of_eventuallyEq heq
    change HasDerivAt f ((1 / 2 : ℝ) * deriv
      (fun s ↦ g.inner (F (t, s)) (T (t, s)) (T (t, s))) 0) t at h
    simpa only [hz.deriv, mul_zero] using h
  have hfzero : f 0 = 0 := by
    have hconst : (fun q ↦ F (0, q)) = fun _ ↦ p := by
      funext q
      simp only [F, zero_smul]
      exact hbase p
    change g.inner (F (0, 0)) (T (0, 0))
      (curveVelocity (fun q ↦ F (0, q)) 0) = 0
    rw [hconst]
    simp only [curveVelocity, mfderiv_const, zero_apply]
    exact map_zero _
  have hfend : f 1 = 0 := by
    have h := constant_of_has_deriv_right_zero
      (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hd t (mem_Icc_of_Ico ht)).hasDerivWithinAt)
      1 (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    exact h.trans hfzero
  have hediff : MDifferentiableAt 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E) e v :=
    (gauss_fibre_smooth g p v hv).mdifferentiableAt (by simp)
  have hsvel : curveVelocity (fun s ↦ e (a s)) 0 =
      mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E) e v
        ((NormedSpace.fromTangentSpace v).symm w) := by
    have h := mfderiv_comp_apply_of_eq (I := 𝓘(ℝ, ℝ))
      (I' := 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p)) (I'' := 𝓘(ℝ, E)) (x := 0)
      hediff had.differentiableAt.mdifferentiableAt ha0
      ((NormedSpace.fromTangentSpace (0 : ℝ)).symm 1)
    rw [mfderiv_eq_fderiv, had.hasFDerivAt.fderiv] at h
    change curveVelocity (fun s ↦ e (a s)) 0 =
      mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E) e v ((1 : ℝ) • w) at h
    change curveVelocity (fun s ↦ e (a s)) 0 =
      mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) p) 𝓘(ℝ, E) e v w
    simpa only [one_smul] using h
  have htvel := (gauss_variation_endpoint_velocities g p v w hv).1
  change g.inner (e ((1 : ℝ) • a 0))
    (curveVelocity (fun r ↦ e (r • a 0)) 1)
    (curveVelocity (fun s ↦ e ((1 : ℝ) • a s)) 0) = 0 at hfend
  erw [ha0] at hfend
  erw [one_smul] at hfend
  have hunit : (fun s : ℝ ↦ e ((1 : ℝ) • a s)) = fun s ↦ e (a s) := by
    funext s
    rw [one_smul]
  rw [hunit] at hfend
  erw [one_smul] at htvel
  rw [htvel, hsvel] at hfend
  exact hfend


end HolomorphicAnosov
