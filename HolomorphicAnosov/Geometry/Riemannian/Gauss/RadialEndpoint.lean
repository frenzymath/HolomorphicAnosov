import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology Matrix

namespace HolomorphicAnosov

/-- For `v` in the time-one exponential domain, there is a geodesic with initial vector `v` on an
open interval containing `[0, 1]`; at every time `t` in that interval, `t • v` lies in the
exponential domain and the geodesic equals `exp_p(t • v)`. (Andrews, Prop. 8.11.4;
Gallier–Quaintance, Prop. 16.8) -/
theorem gauss_radial_endpoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (v : TangentSpace 𝓘(ℝ, E) p)
    (hv : (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g) :
    ∃ (J : Set ℝ) (γ : ℝ → M), IsOpen J ∧ OrdConnected J ∧ Icc (0 : ℝ) 1 ⊆ J ∧
      IsConnectionGeodesicOn (riemannianConnection g) γ J ∧
      curveTangentLift γ 0 = (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∧
      ∀ t ∈ J, (⟨p, t • v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈
        riemannianExponentialDomain g ∧ riemannianExponential g ⟨p, t • v⟩ = γ t := by
  obtain ⟨q, J, γ, hJ, hconn, hseg, hγ, hinit, hq⟩ := hv
  refine ⟨J, γ, hJ, hconn, hseg, hγ, hinit, ?_⟩
  intro t ht
  have h0 : (0 : ℝ) ∈ J := hseg (by simp)
  let K : Set ℝ := {s | t * s ∈ J}
  have hK : IsOpen K := hJ.preimage (continuous_const.mul continuous_id)
  have hKconn : OrdConnected K := by
    rcases le_total 0 t with ht0 | ht0
    · exact hconn.preimage_mono (fun a b hab ↦ mul_le_mul_of_nonneg_left hab ht0)
    · exact hconn.preimage_anti (fun a b hab ↦ mul_le_mul_of_nonpos_left hab ht0)
  have hKseg : Icc (0 : ℝ) 1 ⊆ K := by
    intro s hs
    rcases le_total 0 t with ht0 | ht0
    · exact hconn.out h0 ht ⟨mul_nonneg ht0 hs.1, by nlinarith [hs.2]⟩
    · exact hconn.out ht h0 ⟨by nlinarith [hs.2], mul_nonpos_of_nonpos_of_nonneg ht0 hs.1⟩
  obtain ⟨hr, hd⟩ := connectionGeodesic_rescale (riemannianConnection g) γ J hJ hconn hγ t
  have hscaled : curveTangentLift (fun s ↦ γ (t * s)) 0 =
      (⟨p, t • v⟩ : TangentBundle 𝓘(ℝ, E) M) := by
    have hstate := congrArg (fun z : TangentBundle 𝓘(ℝ, E) M ↦
      (⟨z.proj, t • z.snd⟩ : TangentBundle 𝓘(ℝ, E) M)) hinit
    have hh : curveTangentLift (fun s ↦ γ (t * s)) 0 =
        (⟨γ 0, t • curveVelocity γ 0⟩ : TangentBundle 𝓘(ℝ, E) M) := by
      apply TotalSpace.ext (hd h0).1
      exact heq_of_eq (hd h0).2
    exact hh.trans hstate
  have hend : IsGeodesicTimeOneEndpoint (riemannianConnection g)
      (⟨p, t • v⟩ : TangentBundle 𝓘(ℝ, E) M) (γ t) :=
    ⟨K, (fun s ↦ γ (t * s)), hK, hKconn, hKseg, hr, hscaled, by simp⟩
  have hdom : (⟨p, t • v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈
      riemannianExponentialDomain g := ⟨γ t, hend⟩
  refine ⟨hdom, ?_⟩
  rw [riemannianExponential, dite_eq_left hdom]
  exact geodesicTimeOneEndpoint_unique _ _ (Classical.choose_spec hdom) hend

end HolomorphicAnosov

