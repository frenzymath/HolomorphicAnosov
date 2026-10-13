import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Basic

/-! The connection geodesic property is local with respect to equality of curves on open time
domains. (Andrews, Lecture 8, Prop. 8.4.1, pp.74–75; §8.11, pp.83–86; Gallier–Quaintance, §16.2,
pp.447–448) -/

open scoped Manifold ContDiff

namespace HolomorphicAnosov

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- If two curves agree on an open time domain and one is a connection geodesic there, so is the
other. (Andrews, Lecture 8, Prop. 8.4.1, pp.74–75; §8.11, pp.83–86; Gallier–Quaintance, §16.2,
pp.447–448) -/
theorem isConnectionGeodesicOn_congr (nabla : SmoothAffineConnection E M)
    {γ η : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hγη : Set.EqOn γ η J)
    (hγ : IsConnectionGeodesicOn nabla γ J) : IsConnectionGeodesicOn nabla η J := by
  refine ⟨hγ.1.congr_mono (fun t ht ↦ (hγη ht).symm) Set.Subset.rfl, ?_⟩
  have hv (u : ℝ) (hu : u ∈ J) :
      (curveVelocity η u : E) = curveVelocity γ u := by
    have he : η =ᶠ[nhds u] γ :=
      Filter.eventuallyEq_of_mem (hJ.mem_nhds hu) (fun v hv ↦ (hγη hv).symm)
    unfold curveVelocity
    rw [he.mfderiv_eq]
    rfl
  have hc (c : OpenPartialHomeomorph (ConnectionWhole M) E) (u : ℝ) (hu : u ∈ J) :
      alongCurveCoordinate c η (curveVelocity η) u =
        alongCurveCoordinate c γ (curveVelocity γ) u := by
    unfold alongCurveCoordinate
    rw [hv u hu, hγη hu]
  intro t ht
  have hp : η t = γ t := (hγη ht).symm
  have hacc : (covariantDerivativeAlongCurve nabla η (curveVelocity η) t : E) =
      covariantDerivativeAlongCurve nabla γ (curveVelocity γ) t := by
    have hd (c : OpenPartialHomeomorph (ConnectionWhole M) E) :
        deriv (alongCurveCoordinate c η (curveVelocity η)) t =
          deriv (alongCurveCoordinate c γ (curveVelocity γ)) t :=
      (Filter.eventuallyEq_of_mem (hJ.mem_nhds ht) (fun u hu ↦ hc c u hu)).deriv_eq
    have hx (c : OpenPartialHomeomorph (ConnectionWhole M) E) :
        deriv (connectionChartMap c ∘ η) t = deriv (connectionChartMap c ∘ γ) t :=
      (Filter.eventuallyEq_of_mem (hJ.mem_nhds ht)
        (fun u hu ↦ congrArg (connectionChartMap c) (hγη hu).symm)).deriv_eq
    unfold covariantDerivativeAlongCurve covariantDerivativeCoordinate
    change (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (connectionChartInverse (chartAt E (⟨η t, Set.mem_univ _⟩ : ConnectionWhole M)))
      (connectionChartMap (chartAt E (⟨η t, Set.mem_univ _⟩ : ConnectionWhole M)) (η t))) _ =
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E)
      (connectionChartInverse (chartAt E (⟨γ t, Set.mem_univ _⟩ : ConnectionWhole M)))
      (connectionChartMap (chartAt E (⟨γ t, Set.mem_univ _⟩ : ConnectionWhole M)) (γ t))) _
    simp only [hp, hd, hx, hc _ t ht]
    congr 1
    ext v
    exact congrArg (fun p : M ↦
      let c := chartAt E (⟨p, Set.mem_univ p⟩ : ConnectionWhole M)
      let x := connectionChartMap c p
      tangentSpaceCastModel 𝓘(ℝ, E) (connectionChartInverse c x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (connectionChartInverse c) x
          ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm v))) hp
  exact hacc.trans (hγ.2 t ht)

end HolomorphicAnosov

