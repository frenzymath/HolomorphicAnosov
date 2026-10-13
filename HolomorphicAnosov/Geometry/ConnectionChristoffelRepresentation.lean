import HolomorphicAnosov.Geometry.SmoothAffineConnection
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.CoordinateRestriction
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.RestrictFieldLaw
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray.Basic
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.MaximalAtlasRestriction
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.ChartSource
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.Coefficients
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.ExtendedCoefficients
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.WholeChart
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.WholeChartAtlas
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.RestrictField

open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
open ConnectionChristoffelLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The Christoffel coefficients express the covariant derivative of smooth vector fields on the
chart source as the directional derivative of their coefficients plus the Christoffel term.
(Andrews, Prop. 8.3.1, p.74) -/
theorem connectionChristoffel_representation (nabla : SmoothAffineConnection E M)
    {n : ℕ} (b : Basis (Fin n) ℝ E)
    (c : OpenPartialHomeomorph (ConnectionWhole M) E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ (ConnectionWhole M))
    (X Y : LocalSmoothVectorField E M ⊤) (p : ConnectionWhole M)
    (hp : p ∈ c.source) (k : Fin n) :
    (nabla.cov ⊤ X Y).tangentCoefficient b c p k =
      (∑ i, X.tangentCoefficient b c p i *
        fderiv ℝ (Y.coordinateCoefficient b c k) (c p) (b i)) +
      ∑ i, ∑ j, X.tangentCoefficient b c p i *
        Y.tangentCoefficient b c p j * connectionChristoffel nabla b c hc i j k p := by
  let C := wholeChart c
  have hC := wholeChart_mem_maximalAtlas c hc
  let V := chartSource C
  let pV : V := ⟨p.1, mem_univ _, hp⟩
  have hV : Nonempty V := ⟨pV⟩
  have htop : Nonempty (⊤ : Opens M) := ⟨p⟩
  let cV := C.subtypeRestr hV
  have hpV : pV ∈ cV.source := by
    change pV ∈ (C.subtypeRestr hV).source
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    exact pV.property
  have hvector (Z : LocalSmoothVectorField E M ⊤) (q : V) :
      mvfderiv 𝓘(ℝ, E) cV q (restrictField (show V ≤ ⊤ from le_top) Z q) =
        mvfderiv 𝓘(ℝ, E) c (Opens.inclusion le_top q) (Z (Opens.inclusion le_top q)) := by
    exact chartVector_isRestriction le_top hV htop C hC Z (restrictField le_top Z)
      (restrictField_isRestriction le_top Z) q q.property
  have hderiv : (restrictField (show V ≤ ⊤ from le_top) Y).coordinateCoefficient b cV k
      =ᶠ[𝓝 (c p)] Y.coordinateCoefficient b c k := by
    filter_upwards [cV.open_target.mem_nhds (cV.map_source hpV)] with z hz
    have hq : Opens.inclusion (show V ≤ ⊤ from le_top) (cV.symm z) = c.symm z := by
      apply Subtype.ext
      exact C.subtypeRestr_symm_apply hV hz
    change b.repr (mvfderiv 𝓘(ℝ, E) cV (cV.symm z)
      (restrictField le_top Y (cV.symm z))) k = _
    rw [hvector, hq]
    rfl
  have hΓ := (Classical.choose_spec
    (((isSmoothAffineConnectionOperator_iff_christoffel nabla.cov).mp nabla.laws).2
      V n b cV (HolomorphicAnosov.maximalAtlas_subtypeRestr C hC V hV))).2
  have heq := hΓ (restrictField le_top X) (restrictField le_top Y) pV hpV k
  have hcov := chartVector_isRestriction le_top hV htop C hC (nabla.cov ⊤ X Y)
    (nabla.cov V (restrictField le_top X) (restrictField le_top Y))
    (nabla.laws.restriction le_top X Y (restrictField le_top X) (restrictField le_top Y)
      (restrictField_isRestriction le_top X) (restrictField_isRestriction le_top Y))
    pV pV.property
  have hcoeff (i j : Fin n) : connectionChristoffel nabla b c hc i j k p =
      localChristoffel nabla b C hC hV i j k pV := by
    unfold connectionChristoffel extendedLocalChristoffel
    split
    · rfl
    · rename_i hn
      exact (hn pV.property).elim
  simp only [LocalSmoothVectorField.tangentCoefficient] at heq ⊢
  change b.repr (mvfderiv 𝓘(ℝ, E) cV pV
    (nabla.cov V (restrictField le_top X) (restrictField le_top Y) pV)) k = _ at heq
  rw [hcov] at heq
  simp only [hvector] at heq
  have hd : fderiv ℝ ((restrictField (show V ≤ ⊤ from le_top) Y).coordinateCoefficient b cV k)
      (cV pV) = fderiv ℝ (Y.coordinateCoefficient b c k) (c p) := hderiv.fderiv_eq
  rw [hd] at heq
  simp only [hcoeff]
  exact heq

end
end HolomorphicAnosov
