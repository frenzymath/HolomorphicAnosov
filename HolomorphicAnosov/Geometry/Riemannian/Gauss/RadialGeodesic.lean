import HolomorphicAnosov.Geometry.Riemannian.Gauss.RadialEndpoint
import HolomorphicAnosov.Geometry.Riemannian.Gauss.GeodesicCongr

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

/-- The radial exponential curve is a geodesic on an open interval containing `[0, 1]`, with the
prescribed initial tangent vector. (Gallier–Quaintance, §16.2, pp.447–448; Andrews, Prop. 8.11.4) -/
theorem gauss_radial_geodesic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (g : ContMDiffRiemannianMetric 𝓘(ℝ, E) ∞ E
      (TangentSpace 𝓘(ℝ, E) : M → Type _))
    (p : M) (v : TangentSpace 𝓘(ℝ, E) p)
    (hv : (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈ riemannianExponentialDomain g) :
    ∃ J : Set ℝ, IsOpen J ∧ OrdConnected J ∧ Icc (0 : ℝ) 1 ⊆ J ∧
      IsConnectionGeodesicOn (riemannianConnection g)
        (fun t ↦ riemannianExponential g ⟨p, t • v⟩) J ∧
      (∀ t ∈ J, (⟨p, t • v⟩ : TangentBundle 𝓘(ℝ, E) M) ∈
        riemannianExponentialDomain g) ∧
      curveTangentLift (fun t ↦ riemannianExponential g ⟨p, t • v⟩) 0 =
        (⟨p, v⟩ : TangentBundle 𝓘(ℝ, E) M) := by
  obtain ⟨J, γ, hJ, hconn, hseg, hγ, hinit, hrad⟩ := gauss_radial_endpoint g p v hv
  have he : EqOn (fun t ↦ riemannianExponential g ⟨p, t • v⟩) γ J :=
    fun t ht ↦ (hrad t ht).2
  refine ⟨J, hJ, hconn, hseg,
    isConnectionGeodesicOn_congr (riemannianConnection g) hJ he.symm hγ,
    fun t ht ↦ (hrad t ht).1, ?_⟩
  have h0 : (0 : ℝ) ∈ J := hseg (by simp)
  have hnear := Filter.eventuallyEq_of_mem (hJ.mem_nhds h0) he
  have hvel : curveVelocity (E := E) (fun t ↦ riemannianExponential g ⟨p, t • v⟩) 0 =
      curveVelocity γ 0 := by
    unfold curveVelocity
    rw [hnear.mfderiv_eq]
    rfl
  apply Eq.trans _ hinit
  apply TotalSpace.ext (he h0)
  exact heq_of_eq hvel

end HolomorphicAnosov
