import HolomorphicAnosov.Topology.Franks.OriginalCoverNativePlaques
import HolomorphicAnosov.Topology.Franks.OriginalCoverPlaqueProduct
import HolomorphicAnosov.Topology.Franks.UniformLeafDecay
import HolomorphicAnosov.Dynamics.Anosov.SelectedPartitionProducts
import HolomorphicAnosov.Dynamics.SmaleOriginalAnosovCyclicShadowingSource
import HolomorphicAnosov.Topology.Franks.NativeSpectralPeriodicDensity
import HolomorphicAnosov.Topology.Franks.PeriodicFixedBijection
import HolomorphicAnosov.Topology.Franks.SpectralPeriodicDensity
import HolomorphicAnosov.Topology.Franks.OriginalCoverGlobalProduct
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundleFinrank
import HolomorphicAnosov.Dynamics.Anosov.NativeLeafRank
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeAsymptoticDatumOfLeaf
import HolomorphicAnosov.Paper.Zhang.StableFoliationsGlobalCompletion
import HolomorphicAnosov.Dynamics.Anosov.TheoremASupport.inverseSplitting
import HolomorphicAnosov.Topology.Franks.LefschetzCoverCount
import HolomorphicAnosov.Topology.TorusWindingOfLift
import HolomorphicAnosov.Topology.Franks.LocalLinearization
import HolomorphicAnosov.Topology.Franks.PositiveEigenvectorUniqueness
import HolomorphicAnosov.Topology.Franks.CorrectionTraceLimit
import HolomorphicAnosov.Topology.Franks.TriangularTraceLimit
import HolomorphicAnosov.Topology.Franks.NormalizedCountSum
import HolomorphicAnosov.Topology.Franks.HyperbolicityOfPower
import HolomorphicAnosov.Topology.Franks.BoundedLiftSurjective
import HolomorphicAnosov.Topology.Franks.ExpandingLeafInjectivity
import HolomorphicAnosov.Topology.Franks.GlobalProductInjectivity
import HolomorphicAnosov.Topology.Franks.WindingMatrixHomotopy
import HolomorphicAnosov.Topology.Franks.WindingMatrixRecentering
import HolomorphicAnosov.Topology.Franks.OriginalBasedMatrix
import HolomorphicAnosov.Topology.Franks.NativePointedSemiconjugacy
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding
import HolomorphicAnosov.Dynamics.ManeLinearToralErgodicityTransitivityG1
import HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7
import HolomorphicAnosov.Dynamics.SmaleSpectralBasins
import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray
import HolomorphicAnosov.Geometry.Riemannian.GallierQuaintanceGaussLemma
import HolomorphicAnosov.Geometry.RiemannianExponentialLocalAddition
import HolomorphicAnosov.Geometry.SmoothLeviCivitaConnection
import HolomorphicAnosov.Geometry.SmoothLocalFlow
import HolomorphicAnosov.Linear.HyperbolicDecayComplement
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import HolomorphicAnosov.Topology.BasedHomotopyUniqueness
import HolomorphicAnosov.Topology.CompactENRLefschetzLocalIndexSum
import HolomorphicAnosov.Topology.EuclideanFixedPointIndex
import HolomorphicAnosov.Topology.Franks.IntrinsicLeafMetricBounds
import HolomorphicAnosov.Topology.Franks.PointedLiftIntertwining
import HolomorphicAnosov.Topology.Franks.OriginalLiftUniqueFixedPoint
import HolomorphicAnosov.Topology.FranksPiOneSemiconjugacy
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker
import HolomorphicAnosov.Topology.InvertibleLinearLocalDegree
import HolomorphicAnosov.Topology.ManningOriginalSmoothPeriodicFibre
import HolomorphicAnosov.Topology.OriginalTorusLefschetzDeterminant
import HolomorphicAnosov.Topology.OriginalTorusLiftFixedPointExistence
import HolomorphicAnosov.Topology.RealTorusCoordinateCWStructure
import HolomorphicAnosov.Topology.CWComplexHomeomorph
import HolomorphicAnosov.Topology.Franks.PullbackLiftCoordinates
import HolomorphicAnosov.Topology.RealVectorBundleOrientationMonodromy
import HolomorphicAnosov.Topology.RelativeSingularHomotopyInvariance
import HolomorphicAnosov.Topology.TorusH1Pi1Naturality
import HolomorphicAnosov.Topology.TorusStandardWinding
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Diffeomorph
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import HolomorphicAnosov.Paper.Zhang.HyperbolicRealToralConjugacy
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeFromLamination

/-!
# Franks–Manning classification on the original smooth manifold

Source: Franks, *Anosov diffeomorphisms on tori* (1969), pp.117–124;
Franks, *Anosov Diffeomorphisms* (1970), Proposition (2.1), pp.70–71 and
Theorem (2.2), pp.71–74; Manning, *There are no new Anosov diffeomorphisms
on tori* (1974), pp.422–429. The statement is the original-smooth-manifold
application of these arguments recorded in `topo.franks_manning`, also used
by Zhang, Proposition 2.9, p.10. The published standard-smooth torus or
infranilmanifold theorem is not applied by identifying smooth structures.
-/

namespace HolomorphicAnosov.FranksFibreInjectivity

/-- Equality in the actual coordinate quotient is exactly an integral displacement.
Source: Franks (1969), §1.8, pp.122–123; Step22's final downstairs argument.
This is proved in the literal UnitAddCircle model, including the empty product. -/
theorem integer_displacement_of_coordinate_quotient_eq {n : ℕ}
    (v w : Fin n → ℝ)
    (h : (fun i ↦ (v i : UnitAddCircle)) = (fun i ↦ (w i : UnitAddCircle))) :
    ∃ z : Fin n → ℤ, v = w + (fun i ↦ (z i : ℝ)) := by
  have hz (i : Fin n) : ∃ z : ℤ, (z : ℝ) = v i - w i := by
    have he : ((v i - w i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, congrFun h i, sub_self]
    obtain ⟨z, hz⟩ := AddCircle.coe_eq_zero_iff (1 : ℝ) |>.mp he
    exact ⟨z, by simpa only [zsmul_eq_mul, mul_one] using hz⟩
  choose z hz using hz
  refine ⟨z, ?_⟩
  funext i
  change v i = w i + (z i : ℝ)
  rw [hz]
  ring

/-- Lift injectivity descends through the original covering using ONE actual deck
translate. The source projection is surjective and deck invariant, and the target
projection is the actual coordinate quotient; no degree argument or smooth
identification with a standard torus is used. Franks (1969), §1.8, pp.122–123,
expanded in Step22 of the current source proof. -/
theorem downstairs_injective_of_equivariant_lift
    {n : ℕ} {P X : Type*} (p : P → X) (hp : Function.Surjective p)
    (H : P → (Fin n → ℝ)) (h : X → UnitAddTorus (Fin n))
    (deck : (Fin n → ℤ) → P → P)
    (hdeck : ∀ z x, p (deck z x) = p x)
    (hequiv : ∀ z x, H (deck z x) = H x + (fun i ↦ (z i : ℝ)))
    (hcompat : ∀ x i, h (p x) i = (H x i : UnitAddCircle))
    (hinj : Function.Injective H) : Function.Injective h := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := hp x
  obtain ⟨b, rfl⟩ := hp y
  have he : (fun i ↦ (H a i : UnitAddCircle)) =
      (fun i ↦ (H b i : UnitAddCircle)) := by
    funext i
    rw [← hcompat, ← hcompat, hxy]
  obtain ⟨z, hz⟩ := integer_displacement_of_coordinate_quotient_eq (H a) (H b) he
  have hab : a = deck z b := hinj (hz.trans (hequiv z b).symm)
  rw [hab, hdeck]

end HolomorphicAnosov.FranksFibreInjectivity


namespace HolomorphicAnosov

universe u

open scoped Bundle ContDiff

/- The extended Riemannian distance is finite on a preconnected component. This
metric finiteness adapter is used when installing the manifold metric in the main
Franks--Manning argument. -/
theorem franks_manning_edist_ne_top
    {X : Type*} [EMetricSpace X] [PreconnectedSpace X] (x y : X) : edist x y ≠ ⊤ := by
  let S : Set X := {z | edist z x < ⊤}
  have hS : IsOpen S := EMetric.isOpen_iff.mpr (by
    intro z hz
    refine ⟨1, by simp, ?_⟩
    intro w hw
    exact lt_of_le_of_lt (edist_triangle w z x)
      (ENNReal.add_lt_top.mpr ⟨hw.trans (by simp), hz⟩))
  have hSc : IsOpen Sᶜ := EMetric.isOpen_iff.mpr (by
    intro z hz
    refine ⟨1, by simp, ?_⟩
    intro w hw hws
    apply hz
    exact lt_of_le_of_lt (edist_triangle z w x)
      (ENNReal.add_lt_top.mpr ⟨by
        have hw' : edist w z < 1 := hw
        simpa only [edist_comm] using hw'.trans (show (1 : ENNReal) < ⊤ by simp), hws⟩))
  have hfull : S = Set.univ := (show IsClopen S from
      ⟨isOpen_compl_iff.mp hSc, hS⟩).eq_univ ⟨x, by simp [S]⟩
  have hy : y ∈ S := hfull ▸ Set.mem_univ y
  have hxy : edist x y < ⊤ := by
    simpa only [S, Set.mem_ofPred_eq, edist_comm] using hy
  exact ne_of_lt hxy

namespace FranksManningTarget

/-- The integer inverse acts as the inverse of the same row-coordinate toral map.
Source: Ha–Kim–Lee (2010), Lemma 2.2, pp.2–3, specialized to determinant ±1.
Expand the two finite sums and collect the integer matrix product. -/
private theorem map_comp {n : ℕ} (A B : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (x : UnitAddTorus (Fin n)) :
    integralToralMap A (integralToralMap B x) = integralToralMap (A * B) x := by
  classical
  funext i
  change (∑ j : Fin n, A i j • ∑ k : Fin n, B j k • x k) =
    ∑ k : Fin n, (∑ j : Fin n, A i j * B j k) • x k
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

private theorem map_injective {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    Function.Injective (integralToralMap A) := by
  have hone : ∀ x : UnitAddTorus (Fin n), integralToralMap 1 x = x := by
    intro x
    ext i
    simp [integralToralMap, Matrix.one_apply]
  intro x y hxy
  simpa only [map_comp, inv_mul_cancel, hone] using congrArg (integralToralMap A⁻¹) hxy

/-- A finite-order torus point is periodic under an invertible integral matrix.
Source: Ha–Kim–Lee (2010), Lemma 2.2, pp.2–3. The positive common denominator
defines a finite grid, preserved by the integer row action. Its restriction is
injective by the integral inverse and therefore every grid point is periodic.
This proof also applies to the singleton zero-dimensional torus. -/
theorem torsion_periodic {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (x : UnitAddTorus (Fin n)) (hx : IsOfFinAddOrder x) :
    x ∈ Function.periodicPts (integralToralMap A) := by
  classical
  obtain ⟨q, hq, hxq⟩ := hx.exists_nsmul_eq_zero
  let T := {z : UnitAddCircle // q • z = 0}
  have : Finite T := (AddCircle.finite_torsion (1 : ℝ) hq).to_subtype
  let Grid := Fin n → T
  let embed : Grid → UnitAddTorus (Fin n) := fun z i ↦ (z i).val
  have hembed : Function.Injective embed := by
    intro z w h
    funext i
    exact Subtype.ext (congrFun h i)
  have hpres : ∀ z : Grid, ∀ i, q • integralToralMap A (embed z) i = 0 := by
    intro z i
    simp only [integralToralMap, Finset.smul_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [smul_comm, (z j).property, smul_zero]
  let F : Grid → Grid := fun z i ↦ ⟨integralToralMap A (embed z) i, hpres z i⟩
  have hsem : Function.Semiconj embed F (integralToralMap A) := fun _ ↦ rfl
  have hF : Function.Injective F := by
    intro z w h
    apply hembed
    apply map_injective A
    exact congrArg embed h
  let z : Grid := fun i ↦ ⟨x i, congrFun hxq i⟩
  obtain ⟨m, hm, hzm⟩ := hF.mem_periodicPts z
  exact ⟨m, hm, hzm.map hsem⟩

/-- Periodic points of the literal integral toral map are dense.
Source: Ha–Kim–Lee (2010), Lemma 2.2 and Corollary 2.3, pp.2–3; this is the
automorphism case of Step19 of the current `franks_manning` docstring. Rational real coordinates
have finite additive order after quotienting by the integer lattice. A finite
tuple of them has finite order, so the finite-grid argument makes it periodic.
Rational coordinates are dense in the real product; the coordinate quotient is
continuous and surjective, hence their toral images are dense. No hyperbolicity,
positive-dimensional hypothesis or smooth torus identification is required. -/
theorem dense_periodicPts {n : ℕ} (A : Matrix.GeneralLinearGroup (Fin n) ℤ) :
    Dense (Function.periodicPts (integralToralMap A)) := by
  have hcircle : DenseRange (fun r : ℚ ↦ ((r : ℝ) : UnitAddCircle)) := by
    exact (QuotientAddGroup.mk_surjective :
      Function.Surjective (fun r : ℝ ↦ (r : UnitAddCircle))).denseRange.comp
      Rat.denseRange_cast continuous_quot_mk
  have hrat : DenseRange (fun r : Fin n → ℚ ↦ fun i ↦ ((r i : ℝ) : UnitAddCircle)) :=
    DenseRange.piMap fun _ ↦ hcircle
  apply hrat.mono
  rintro x ⟨r, rfl⟩
  apply torsion_periodic A
  apply IsOfFinAddOrder.pi
  intro i
  exact AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div.mpr ⟨r i, by simp⟩

end FranksManningTarget


/-- Step23 of the Franks–Manning source plan: dimension zero is independent of
the hyperbolic estimates. Choose the identity empty matrix and the supplied
homeomorphism. The zero vector space has no eigenvectors and the torus has only
one point, so the eigenvalue and conjugacy conditions follow. -/
theorem hyperbolicRealToralConjugacy_zero {X : Type*} [TopologicalSpace X]
    (f : X → X) (h : Nonempty (X ≃ₜ UnitAddTorus (Fin 0))) :
    HyperbolicRealToralConjugacy 0 X f := by
  obtain ⟨h⟩ := h
  refine ⟨1, h, ?_, fun _ ↦ Subsingleton.elim _ _⟩
  intro μ hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  exact (hv.2 (Subsingleton.elim _ _)).elim


/-- The final compact-to-Hausdorff packaging used in Franks--Manning Step23.
Given the induced integer matrix, a continuous bijective semiconjugacy from the
compact original manifold to the Hausdorff canonical torus is automatically a
homeomorphism. This packages exactly the locked `HyperbolicRealToralConjugacy`
interface and does not infer surjectivity or injectivity from semiconjugacy. -/
theorem package_hyperbolicRealToralConjugacy
    {n : ℕ} {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (f : X → X) (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hA : ∀ μ : ℂ,
      Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1)
    (h : X → UnitAddTorus (Fin n)) (hcont : Continuous h)
    (hbij : Function.Bijective h)
    (hsemiconj : ∀ x, h (f x) = integralToralMap A (h x)) :
    HyperbolicRealToralConjugacy n X f := by
  let e : X ≃ UnitAddTorus (Fin n) := Equiv.ofBijective h hbij
  let home : X ≃ₜ UnitAddTorus (Fin n) :=
    Continuous.homeoOfEquivCompactToT2 (f := e) hcont
  refine ⟨A, home, hA, ?_⟩
  intro x
  exact hsemiconj x


namespace FranksFibreInjectivity

/-! A compact equal-fibre relation has a uniform bound whenever the selected
distance is continuous on that relation. This is the compactness step used
after deck normalization; it leaves the global-product and leaf-construction
inputs explicit to their callers. -/

theorem compact_relation_distance_bound {P : Type*}
    [TopologicalSpace P] (R : Set (P × P)) (d : P → P → ℝ)
    (hR : IsCompact R)
    (hd : ContinuousOn (fun z : P × P ↦ d z.1 z.2) R) :
    ∃ B : ℝ, ∀ x y, (x, y) ∈ R → d x y ≤ B := by
  obtain ⟨B, hB⟩ := hR.bddAbove_image hd
  refine ⟨B, ?_⟩
  intro x y hxy
  exact hB ⟨(x, y), hxy, rfl⟩

end FranksFibreInjectivity


/--
Transport the explicit finite torus CW structure to a manifold homeomorphic to the
torus.  This is the interface used when applying the CW based Franks semiconjugacy
to the topological manifold in the lift-data theorem.
-/
theorem franks_cw_complex_transport {n : ℕ} {M : Type u} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) :
    Nonempty (Topology.CWComplex (Set.univ : Set M)) := by
  rcases real_torus_coordinate_cw_structure n with ⟨_, ⟨cw, _⟩⟩
  let : Topology.CWComplex (Set.univ : Set (UnitAddTorus (Fin n))) := cw
  exact cwComplex_homeomorph M (UnitAddTorus (Fin n)) q

open HolomorphicAnosov.Topology
/-
The native pointed Franks semiconjugacy can be applied on a manifold merely
homeomorphic to the canonical torus: the required CW instance is transported
from the explicit torus structure through the given homeomorphism.  This adapter
is the source-boundary interface used by `franks_manning_lift_data`; it adds no
smooth or standard-torus hypothesis.
-/
theorem native_pointed_semiconjugacy_of_homeomorph
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ConnectedSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (u0 : OriginalTorusPullback q)
    (g : M ≃ₜ M)
    (F : C(OriginalTorusPullback q, OriginalTorusPullback q))
    (hF : ∀ x, (F x).val.1 = g x.val.1) (hF0 : F u0 = u0)
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (hA : ∀ μ : ℂ, Module.End.HasEigenvalue
      (Matrix.mulVecLin (fun i j : Fin n ↦ (A i j : ℂ))) μ → ‖μ‖ ≠ 1) :
    let h0 : C(M, UnitAddTorus (Fin n)) :=
      ⟨fun x ↦ q x - q u0.val.1, q.continuous.sub continuous_const⟩
    let hh0 : h0 u0.val.1 = 0 := sub_self _
    let hg : g u0.val.1 = u0.val.1 := (hF u0).symm.trans
      (congrArg (fun x : OriginalTorusPullback q ↦ x.val.1) hF0)
    (FundamentalGroup.mapOfEq h0 hh0).comp
        (FundamentalGroup.mapOfEq (⟨g, g.continuous⟩ : C(M, M)) hg) =
      (FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap A)
        (by classical ext i; simp [franksIntegralToralContinuousMap, ContinuousMap.pi])).comp
        (FundamentalGroup.mapOfEq h0 hh0) →
    ∃ k : C(M, UnitAddTorus (Fin n)), k u0.val.1 = 0 ∧ k.Homotopic h0 ∧
      (∀ x, k (g x) = integralToralMap A (k x)) ∧
      ∃ H : C(OriginalTorusPullback q, Fin n → ℝ), H u0 = 0 ∧
        (∀ x, coordinateProjection n (H x) = k x.val.1) ∧
        (∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖(x.val.2 - u0.val.2) - H x‖ ≤ B) ∧
        (∀ (d : deck (fun x : OriginalTorusPullback q ↦ x.val.1)) x,
          ((d • x).val.2 - u0.val.2) - H (d • x) = (x.val.2 - u0.val.2) - H x) ∧
        Function.Semiconj H F (FranksMatrix.realAction A) ∧
        ∀ r : ℕ, ∀ x, H (F^[r] x) = (FranksMatrix.realAction A)^[r] (H x) := by
  rcases franks_cw_complex_transport q with ⟨cw⟩
  let : Topology.CWComplex (Set.univ : Set M) := cw
  exact native_pointed_semiconjugacy q u0 g F hF hF0 A hA


noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Specialize the based matrix square to a pointed torus homeomorphism. -/
theorem pointed_torus_integral_matrix {n : ℕ}
    (v : UnitAddTorus (Fin n) ≃ₜ UnitAddTorus (Fin n)) (hv : v 0 = 0) :
    ∃ B : Matrix.GeneralLinearGroup (Fin n) ℤ,
      FundamentalGroup.mapOfEq (⟨v,v.continuous⟩ : C(_, _)) hv =
      FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap B)
        (by classical ext i; simp [franksIntegralToralContinuousMap, ContinuousMap.pi]) := by
  classical
  obtain ⟨B,hB⟩ := original_based_integral_matrix (Homeomorph.refl _) 0 v hv
  refine ⟨B,?_⟩
  let h0 : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ x - 0, continuous_id.sub continuous_const⟩
  have he : h0 = ContinuousMap.id _ := ContinuousMap.ext (fun x ↦ sub_zero x)
  have hid : FundamentalGroup.mapOfEq h0 (sub_self 0) = MonoidHom.id _ := by
    rw [FranksCoverWinding.mapOfEq_congr (sub_self 0) rfl he]
    ext γ
    rw [FundamentalGroup.mapOfEq_apply]
    change (Path.Homotopic.Quotient.map γ (ContinuousMap.id _)).cast rfl rfl = γ
    rw [Path.Homotopic.Quotient.cast_rfl_rfl]
    induction γ using Quotient.inductionOn with
    | h p => rfl
  change (FundamentalGroup.mapOfEq h0 _).comp (FundamentalGroup.mapOfEq (⟨v,v.continuous⟩ : C(_, _)) hv) =
    (FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap B) _).comp (FundamentalGroup.mapOfEq h0 _) at hB
  simpa only [hid,MonoidHom.id_comp,MonoidHom.comp_id] using hB

/-- The straight-loop normalization is equivalent to the endpoint normalization. -/
theorem straight_winding_normalized {n : ℕ}
    (w : FundamentalGroup (UnitAddTorus (Fin n)) 0 ≃* Multiplicative (Fin n → ℤ))
    (hnorm : ∀ z : Fin n → ℤ, ∃ p : Path (0 : UnitAddTorus (Fin n)) 0,
      (∀ (t : unitInterval) (j : Fin n), p t j = (((t : ℝ) * (z j : ℝ) : ℝ) : UnitAddCircle)) ∧
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z) :
    ∀ (p : Path (0 : UnitAddTorus (Fin n)) 0) (z : Fin n → ℤ),
      w (FundamentalGroup.fromPath ⟦p⟧) = Multiplicative.ofAdd z ↔
        ∃ l : Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)), ∀ t i, (l t i : UnitAddCircle) = p t i := by
  intro p z
  constructor
  · intro h
    obtain ⟨z',l,hl⟩ := torus_loop_integer_endpoint_lift n p
    have hz : z' = z := Multiplicative.ofAdd.injective
      ((winding_of_integer_endpoint_lift n w hnorm p z' l hl).symm.trans h)
    subst z'
    exact ⟨l,hl⟩
  · rintro ⟨l,hl⟩
    exact winding_of_integer_endpoint_lift n w hnorm p z l hl

/-- The original Anosov map has a fixed point and a hyperbolic integral
matrix satisfying the exact based fundamental-group square. -/
theorem franks_manning_fixed_spectral_data {n : ℕ} {M : Type*}
    [MetricSpace M] [ConnectedSpace M] [CompactSpace M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    [IsRiemannianManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M]
    [IsContMDiffRiemannianBundle (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n)) (fun x : M ↦ TangentSpace
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    (q : M ≃ₜ UnitAddTorus (Fin n))
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (S : InvariantRealTangentSplitting f) (hb : BundleAnosovBounds f S)
 :
    ∃ b : M, f b = b ∧ ∃ B : Matrix.GeneralLinearGroup (Fin n) ℤ,
      (∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (B i j : ℂ))) μ → ‖μ‖ ≠ 1) ∧
      (∀ m : ℕ, 0 < m → {x | realIterate _ f m x = x}.Finite) ∧
      (∀ m : ℕ, 0 < m →
        (Nat.card {x // realIterate _ f m x = x} : ℚ) =
          |Matrix.det (1 - ((B : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℚ))^m)|) ∧
      (∀ m : ℕ, 0 < m →
        Nat.card {x // realIterate _ f m x = x} =
          (Matrix.det (1 - (B : Matrix (Fin n) (Fin n) ℤ)^m)).natAbs) ∧
      let h0 : C(M, UnitAddTorus (Fin n)) :=
        ⟨fun x ↦ q x - q b, q.continuous.sub continuous_const⟩
      ∃ hb : f b = b,
        (FundamentalGroup.mapOfEq h0 (sub_self _)).comp
          (FundamentalGroup.mapOfEq (⟨f,f.continuous⟩ : C(M,M)) hb) =
        (FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap B)
          (by classical ext i; simp [franksIntegralToralContinuousMap, ContinuousMap.pi])).comp
          (FundamentalGroup.mapOfEq h0 (sub_self _)) := by
  classical
  obtain ⟨w,hstraight,_,hwB⟩ := torus_pi1_standard_winding n
  have hw := straight_winding_normalized w hstraight
  let v : C(UnitAddTorus (Fin n),UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ q (f (q.symm x)),q.continuous.comp (f.continuous.comp q.symm.continuous)⟩
  obtain ⟨A,hA,_⟩ := torus_selfmap_winding_matrix n v w
  have hhyper := FranksLefschetzCoverCount.hyperbolic_of_bundle_anosov q f S hb w hw A hA
  obtain ⟨hf,_⟩ := FranksLefschetzCoverCount.periodic_growth_of_bundle_anosov q f S hb
  obtain ⟨b,hbfix⟩ := FranksLefschetzCoverCount.fixed_point_of_hyperbolic_winding q f S hb
    (hf 1 (by omega)) w hw A hA hhyper
  let Q := q.trans (Homeomorph.subRight (q b))
  have hQ : Q b = 0 := sub_self _
  let V := (Q.symm.trans f.toHomeomorph).trans Q
  have hV : V 0 = 0 := by
    change Q (f (Q.symm 0)) = 0
    rw [← hQ,Q.symm_apply_apply,hbfix]
  obtain ⟨B,hB⟩ := pointed_torus_integral_matrix V hV
  obtain ⟨FB,hFB,hFB0,hwFB⟩ := hwB B
  have heFB : FB = franksIntegralToralContinuousMap B := by
    apply ContinuousMap.ext
    intro x
    rw [hFB x]
    ext i
    simp [franksIntegralToralContinuousMap,integralToralMap,ContinuousMap.pi]
  subst FB
  have hmat : ∀ (δ : Path (V 0) (0 : UnitAddTorus (Fin n))) γ,
      (w (FundamentalGroup.fundamentalGroupMulEquivOfPath δ
        (FundamentalGroup.map (⟨V,V.continuous⟩ : C(_, _)) 0 γ))).toAdd =
          (B : Matrix (Fin n) (Fin n) ℤ).mulVec (w γ).toAdd := by
    intro δ γ
    have ht := FranksCoverWinding.transport_eq_mapOfEq (⟨V,V.continuous⟩ : C(_, _)) hV w δ γ
    exact (congrArg (fun z ↦ (w z).toAdd) ht).trans
      ((congrArg (fun z ↦ (w z).toAdd) (DFunLike.congr_fun hB γ)).trans (hwFB γ))
  have hBhyper := FranksLefschetzCoverCount.hyperbolic_of_bundle_anosov Q f S hb w hw
    (B : Matrix (Fin n) (Fin n) ℤ) hmat
  have hcountB := fun m hm ↦ FranksLefschetzCoverCount.original_periodic_count_powers
    Q f S hb w hw (B : Matrix (Fin n) (Fin n) ℤ) hmat m hm (hf m hm)
  have hcountNat (m : ℕ) (hm : 0 < m) :
      Nat.card {x // realIterate _ f m x = x} =
        (Matrix.det (1 - (B : Matrix (Fin n) (Fin n) ℤ)^m)).natAbs := by
    let : Finite {x // realIterate _ f m x = x} := (hf m hm).to_subtype
    apply FranksLefschetzCoverCount.nat_card_eq_natAbs_of_rat_count
    simpa only [Matrix.map_pow] using hcountB m hm
  refine ⟨b,hbfix,B,hBhyper,hf,hcountB,hcountNat,hbfix,?_⟩
  change (FundamentalGroup.mapOfEq (⟨Q,Q.continuous⟩ : C(M,_)) hQ).comp
      (FundamentalGroup.mapOfEq (⟨f,f.continuous⟩ : C(M,M)) hbfix) =
    (FundamentalGroup.mapOfEq (franksIntegralToralContinuousMap B) _).comp
      (FundamentalGroup.mapOfEq (⟨Q,Q.continuous⟩ : C(M,_)) hQ)
  rw [← hB,FranksPointedTransport.mapOfEq_comp,FranksPointedTransport.mapOfEq_comp]
  congr 1
  apply ContinuousMap.ext
  intro x
  change Q (f x) = Q (f (Q.symm (Q x)))
  rw [Q.symm_apply_apply]

open HolomorphicAnosov.Topology

/-- Lift the original map through the coordinate covering, fixing a chosen lift
of its fixed point. -/
theorem franks_pointed_original_lift {n : ℕ} {M : Type*} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (f : M ≃ₜ M) (b : M) (hb : f b = b) :
    ∃ u0 : OriginalTorusPullback q, u0.val.1 = b ∧
      ∃ F : OriginalTorusPullback q ≃ₜ OriginalTorusPullback q,
        (∀ x, (F x).val.1 = f x.val.1) ∧ F u0 = u0 := by
  let p := originalTorusProjection n
  have hp : IsCoveringMap p := (coordinateProjection_cover n).isCoveringMap
  obtain ⟨v0,hv0⟩ := (coordinateProjection_cover n).toIsQuotientMap.surjective (q b)
  have hv0' : p v0 = q b := hv0
  let G : C((Fin n → ℝ),UnitAddTorus (Fin n)) :=
    ⟨fun v ↦ q (f (q.symm (p v))),
      q.continuous.comp (f.continuous.comp (q.symm.continuous.comp p.continuous))⟩
  have hbase : p v0 = G v0 := by
    change p v0 = q (f (q.symm (p v0)))
    rw [hv0',q.symm_apply_apply,hb]
  obtain ⟨H,hH,_⟩ := hp.existsUnique_continuousMap_lifts G v0 v0 hbase
  let Gi : C((Fin n → ℝ),UnitAddTorus (Fin n)) :=
    ⟨fun v ↦ q (f.symm (q.symm (p v))),
      q.continuous.comp (f.symm.continuous.comp (q.symm.continuous.comp p.continuous))⟩
  have hbi : f.symm b = b := by
    exact (congrArg f.symm hb).symm.trans (f.symm_apply_apply b)
  have hbasei : p v0 = Gi v0 := by
    change p v0 = q (f.symm (q.symm (p v0)))
    rw [hv0',q.symm_apply_apply,hbi]
  obtain ⟨Hi,hHi,_⟩ := hp.existsUnique_continuousMap_lifts Gi v0 v0 hbasei
  have hpH (v) : p (H v) = G v := congrFun hH.2 v
  have hpHi (v) : p (Hi v) = Gi v := congrFun hHi.2 v
  have hHiH : ∀ v, Hi (H v) = v := by
    apply congrFun (hp.eq_of_comp_eq (Hi.continuous.comp H.continuous) continuous_id ?_ v0 ?_)
    · funext v
      change p (Hi (H v)) = p v
      rw [hpHi]
      change q (f.symm (q.symm (p (H v)))) = p v
      rw [hpH]
      change q (f.symm (q.symm (q (f (q.symm (p v)))))) = p v
      rw [q.symm_apply_apply,f.symm_apply_apply,q.apply_symm_apply]
    · change Hi (H v0) = v0
      rw [hH.1,hHi.1]
  have hHHi : ∀ v, H (Hi v) = v := by
    apply congrFun (hp.eq_of_comp_eq (H.continuous.comp Hi.continuous) continuous_id ?_ v0 ?_)
    · funext v
      change p (H (Hi v)) = p v
      rw [hpH]
      change q (f (q.symm (p (Hi v)))) = p v
      rw [hpHi]
      change q (f (q.symm (q (f.symm (q.symm (p v)))))) = p v
      rw [q.symm_apply_apply,f.apply_symm_apply,q.apply_symm_apply]
    · change H (Hi v0) = v0
      rw [hHi.1,hH.1]
  let u0 : OriginalTorusPullback q := ⟨(b,v0),hv0.symm⟩
  have hproj (x : OriginalTorusPullback q) : q (f x.val.1) = p (H x.val.2) := by
    have hx : p (H x.val.2) = G x.val.2 := congrFun hH.2 x.val.2
    rw [hx]
    change q (f x.val.1) = q (f (q.symm (p x.val.2)))
    rw [← x.property,q.symm_apply_apply]
  let F : C(OriginalTorusPullback q,OriginalTorusPullback q) :=
    ⟨fun x ↦ ⟨(f x.val.1,H x.val.2),hproj x⟩,
      ((f.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
        (H.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _⟩
  have hproji (x : OriginalTorusPullback q) : q (f.symm x.val.1) = p (Hi x.val.2) := by
    rw [hpHi]
    change q (f.symm x.val.1) = q (f.symm (q.symm (p x.val.2)))
    rw [← x.property,q.symm_apply_apply]
  let Fi : C(OriginalTorusPullback q,OriginalTorusPullback q) :=
    ⟨fun x ↦ ⟨(f.symm x.val.1,Hi x.val.2),hproji x⟩,
      ((f.symm.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
        (Hi.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _⟩
  have hleft (x : OriginalTorusPullback q) : Fi (F x) = x := by
    apply Subtype.ext
    exact Prod.ext (f.symm_apply_apply _) (hHiH _)
  have hright (x : OriginalTorusPullback q) : F (Fi x) = x := by
    apply Subtype.ext
    exact Prod.ext (f.apply_symm_apply _) (hHHi _)
  let Fe : OriginalTorusPullback q ≃ₜ OriginalTorusPullback q :=
    ⟨⟨F,Fi,hleft,hright⟩,F.continuous,Fi.continuous⟩
  refine ⟨u0,rfl,Fe,fun _ ↦ rfl,?_⟩
  apply Subtype.ext
  exact Prod.ext hb hH.1

end

noncomputable section
/-- A homeomorphic lift is a diffeomorphism in the actual atlas pulled back
from the original manifold through local covering sheets. -/
def franks_liftDiffeomorph {n : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    (p : P → M) (hp : IsLocalHomeomorph p)
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (F : P ≃ₜ P) (hF : ∀ x, p (F x) = f (p x)) :
    letI := AbstractCoverPullback.charts (E := EuclideanSpace ℝ (Fin n)) p hp
    Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) P P ∞ := by
  letI := AbstractCoverPullback.charts (E := EuclideanSpace ℝ (Fin n)) p hp
  have hFi (x : P) : p (F.symm x) = f.symm (p x) := by
    apply f.injective
    change f (p (F.symm x)) = f (f.symm (p x))
    rw [f.apply_symm_apply,← hF,F.apply_symm_apply]
  exact {
    toEquiv := F.toEquiv
    contMDiff_toFun := AbstractCoverPullback.liftSmooth p hp f f.contMDiff_toFun F F.continuous hF
    contMDiff_invFun := AbstractCoverPullback.liftSmooth p hp f.symm f.symm.contMDiff_toFun
      F.symm F.symm.continuous hFi }

/-- The original pullback projection is the original covering, with its existing
topology; its coordinate graph identifies it with the real universal cover. -/
theorem franks_original_projection_cover {n : ℕ} {M : Type*} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) :
    IsCoveringMap (fun x : OriginalTorusPullback q ↦ x.val.1) ∧
      Function.Surjective (fun x : OriginalTorusPullback q ↦ x.val.1) ∧
      SimplyConnectedSpace (OriginalTorusPullback q) := by
  let Q : OriginalTorusPullback q ≃ₜ (Fin n → ℝ) := {
    toFun := fun x ↦ x.val.2
    invFun := fun v ↦ ⟨(q.symm (originalTorusProjection n v),v),q.apply_symm_apply _⟩
    left_inv := fun x ↦ by
      apply Subtype.ext
      exact Prod.ext ((congrArg q.symm x.property).symm.trans (q.symm_apply_apply _)) rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := continuous_snd.comp continuous_subtype_val
    continuous_invFun := ((q.symm.continuous.comp (originalTorusProjection n).continuous).prodMk
      continuous_id).subtype_mk _ }
  have he : (fun x : OriginalTorusPullback q ↦ x.val.1) =
      q.symm ∘ coordinateProjection n ∘ Q := by
    funext x
    exact ((congrArg q.symm x.property).symm.trans (q.symm_apply_apply _)).symm
  refine ⟨?_,?_,Q.toHomotopyEquiv.simplyConnectedSpace⟩
  · rw [he]
    exact ((coordinateProjection_cover n).isCoveringMap.comp_homeomorph Q).homeomorph_comp q.symm
  · rw [he]
    exact q.symm.surjective.comp
      ((coordinateProjection_cover n).toIsQuotientMap.surjective.comp Q.surjective)
end

noncomputable section
/-- The literal integer translation is a deck transformation of the original
coordinate pullback. -/
def franksIntegerDeck {n : ℕ} {M : Type*} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (z : Fin n → ℤ) :
    _root_.deck (fun x : OriginalTorusPullback q ↦ x.val.1) := by
  let v : Fin n → ℝ := fun i ↦ (z i : ℝ)
  have hv : coordinateProjection n v = 0 := by
    ext i
    exact (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z i,by simp [v]⟩
  let t (x : OriginalTorusPullback q) : OriginalTorusPullback q :=
    ⟨(x.val.1,x.val.2+v),by
      change q x.val.1 = coordinateProjection n (x.val.2+v)
      rw [map_add,hv,add_zero]
      exact x.property⟩
  let ti (x : OriginalTorusPullback q) : OriginalTorusPullback q :=
    ⟨(x.val.1,x.val.2-v),by
      change q x.val.1 = coordinateProjection n (x.val.2-v)
      rw [map_sub,hv,sub_zero]
      exact x.property⟩
  let T : OriginalTorusPullback q ≃ₜ OriginalTorusPullback q := {
    toFun := t
    invFun := ti
    left_inv := fun x ↦ by apply Subtype.ext; exact Prod.ext rfl (add_sub_cancel_right _ _)
    right_inv := fun x ↦ by apply Subtype.ext; exact Prod.ext rfl (sub_add_cancel _ _)
    continuous_toFun := ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).add continuous_const)).subtype_mk _
    continuous_invFun := ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).sub continuous_const)).subtype_mk _ }
  exact ⟨T,rfl⟩

/-- The actual pullback and native deck-invariant correction descend lift
injectivity to the original semiconjugacy. -/
theorem franks_native_downstairs_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (u0 : OriginalTorusPullback q)
    (k : M → UnitAddTorus (Fin n)) (H : OriginalTorusPullback q → Fin n → ℝ)
    (hproj : ∀ x, coordinateProjection n (H x) = k x.val.1)
    (hdeck : ∀ (d : _root_.deck (fun x : OriginalTorusPullback q ↦ x.val.1)) x,
      ((d • x).val.2 - u0.val.2) - H (d • x) = (x.val.2-u0.val.2)-H x)
    (hinj : Function.Injective H) : Function.Injective k := by
  have hp : Function.Surjective (fun x : OriginalTorusPullback q ↦ x.val.1) := by
    intro x
    obtain ⟨v,hv⟩ := (coordinateProjection_cover n).toIsQuotientMap.surjective (q x)
    exact ⟨⟨(x,v),hv.symm⟩,rfl⟩
  apply FranksFibreInjectivity.downstairs_injective_of_equivariant_lift _ hp H k
    (fun z x ↦ franksIntegerDeck q z • x) (fun _ _ ↦ rfl) _ _ hinj
  · intro z x
    funext i
    have h := congrFun (hdeck (franksIntegerDeck q z) x) i
    change (x.val.2 i + (z i : ℝ) - u0.val.2 i) - H (franksIntegerDeck q z • x) i =
      (x.val.2 i-u0.val.2 i)-H x i at h
    change H (franksIntegerDeck q z • x) i = H x i + (z i : ℝ)
    linarith
  · intro x i
    exact (congrFun (hproj x) i).symm
end

/-- Express the bounded-lift fixed-preimage theorem in the actual original
pullback coordinates. The coordinate parametrization and integer deck action
are literal, so this transports no smooth structure. -/
theorem franks_pullback_fixed_preimage {n : ℕ} {M : Type*} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (u0 : OriginalTorusPullback q)
    (f : M → M) (a : UnitAddTorus (Fin n) → UnitAddTorus (Fin n))
    (F : C(OriginalTorusPullback q, OriginalTorusPullback q))
    (hF : ∀ x, (F x).val.1 = f x.val.1)
    (k : C(M, UnitAddTorus (Fin n))) (H : C(OriginalTorusPullback q, Fin n → ℝ))
    (hproj : ∀ x, coordinateProjection n (H x) = k x.val.1)
    (hbound : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, ‖(x.val.2 - u0.val.2) - H x‖ ≤ K)
    (hdeck : ∀ (d : _root_.deck (fun x : OriginalTorusPullback q ↦ x.val.1)) x,
      ((d • x).val.2 - u0.val.2) - H (d • x) = (x.val.2 - u0.val.2) - H x)
    (B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hL : ∀ v, L v = v - B v)
    (hprojB : ∀ v, coordinateProjection n (B v) = a (coordinateProjection n v))
    (hsem : Function.Semiconj H F B)
    (y : UnitAddTorus (Fin n)) (hy : a y = y) :
    ∃ x, f x = x ∧ k x = y := by
  let P : C((Fin n → ℝ), OriginalTorusPullback q) :=
    ⟨fun v ↦ ⟨(q.symm (originalTorusProjection n v), v), q.apply_symm_apply _⟩,
      ((q.symm.continuous.comp (originalTorusProjection n).continuous).prodMk
        continuous_id).subtype_mk _⟩
  have hP (x : OriginalTorusPullback q) : P x.val.2 = x := by
    apply Subtype.ext
    exact Prod.ext ((congrArg q.symm x.property).symm.trans (q.symm_apply_apply _)) rfl
  let G : C((Fin n → ℝ), Fin n → ℝ) :=
    ⟨fun v ↦ (F (P v)).val.2,
      continuous_snd.comp (continuous_subtype_val.comp (F.continuous.comp P.continuous))⟩
  let J := H.comp P
  have hG (v) : coordinateProjection n (G v) =
      q (f (q.symm (coordinateProjection n v))) := by
    change originalTorusProjection n (F (P v)).val.2 = _
    rw [← (F (P v)).property, hF]
    rfl
  have hJsem : Function.Semiconj J G B := by
    intro v
    change H (P (F (P v)).val.2) = B (H (P v))
    rw [hP, hsem]
  have hJdeck (v) (z : Fin n → ℤ) :
      J (v + fun i ↦ (z i : ℝ)) = J v + fun i ↦ (z i : ℝ) := by
    have he : P (v + fun i ↦ (z i : ℝ)) = franksIntegerDeck q z • P v := by
      apply Subtype.ext
      apply Prod.ext
      · apply q.injective
        exact ((P (v + fun i ↦ (z i : ℝ))).property).trans
          (franksIntegerDeck q z • P v).property.symm
      · rfl
    change H (P (v + fun i ↦ (z i : ℝ))) = _
    rw [he]
    ext i
    have hi := congrFun (hdeck (franksIntegerDeck q z) (P v)) i
    change (v i + (z i : ℝ) - u0.val.2 i) - H (franksIntegerDeck q z • P v) i =
      (v i - u0.val.2 i) - H (P v) i at hi
    change H (franksIntegerDeck q z • P v) i = H (P v) i + (z i : ℝ)
    linarith
  obtain ⟨K, hK, hb⟩ := hbound
  have hJbound (v) : ‖v - J v‖ ≤ K + ‖u0.val.2‖ := by
    have he : v - J v = ((v - u0.val.2) - H (P v)) + u0.val.2 := by
      change v - H (P v) = _
      abel
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (hb (P v)) le_rfl)
  obtain ⟨x,hx,hkx⟩ := FranksOriginalLift.fixed_preimage
    (fun x ↦ q (f (q.symm x))) a (fun x ↦ k (q.symm x)) G J B L hL hG
    (fun v ↦ hproj (P v)) hprojB hJsem hJdeck
    (K + ‖u0.val.2‖) (add_nonneg hK (norm_nonneg _)) hJbound y hy
  refine ⟨q.symm x, ?_, hkx⟩
  apply q.injective
  simpa only [q.apply_symm_apply] using hx

open scoped Manifold _root_.Topology

/-- The selected stable asymptotic carrier has a full intrinsic Euclidean model.
On the connected original manifold, subbundle rank is constant. Normalize the
selected native partition to that rank, apply the existing real HPS global leaf
completion, then transport along the point-preserving G15 carrier diffeomorphism.
This is only a composition of those provider interfaces; its coordinate map is
not asserted to be the corrected Franks map H. HPS (1977), §§6B–7, pp.111–116
and 127–129. The global lamination provider retains its admitted proof. -/
theorem franks_native_stable_euclidean
    {n : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [T2Space M] [SecondCountableTopology M]
    [Bundle.RiemannianBundle
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    [IsRiemannianManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M]
    [IsContMDiffRiemannianBundle (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (S : InvariantRealTangentSplitting f)
    (hBounds : BundleAnosovBounds f S)
    (x : M) :
    ∃ N : NativeAsymptoticLeafDatum 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      f.toHomeomorph S.stable.toDistribution x,
      let := N.topology
      Nonempty ((Fin N.rank → ℝ) ≃ₜ StableAsymptoticLeaf f.toHomeomorph x) := by
  let : EMetricSpace M := MetricSpace.toEMetricSpace
  obtain ⟨hs, _⟩ := HPS.anosov_global_lamination_distance M f S hBounds
  obtain ⟨ι, L, r, top, charts, smooth, F, ⟨β, d, T, topT, ⟨boxes⟩⟩,
    _, families, coherent, hextra⟩ := hs
  let := top
  let := charts
  let := smooth
  let := topT
  let k := Module.finrank ℝ (S.stable.toDistribution x)
  have hr (i : ι) : r i = k := by
    let := (F.leaf i).connected
    obtain ⟨z⟩ := (inferInstance : Nonempty (L i))
    exact ((F.leaf i).finrank_tangent z).symm.trans (S.stable.finrank_eq _ x)
  have hrfun : r = fun _ ↦ k := funext hr
  cases hrfun
  obtain ⟨_, _, _, _, ⟨identification, _⟩, _, _⟩ := hextra
  obtain ⟨i, a, ha⟩ := F.cover x
  obtain ⟨e⟩ := HPS.native_stable_euclidean_from_anosov M f S hBounds F boxes identification i
  have hrange : Set.range (F.leaf i).inclusion =
      {y | ForwardAsymptotic f.toHomeomorph x y} := by
    simpa only [ha, Diffeomorph.coe_toHomeomorph] using identification.range_eq_forwardAsymptotic i a
  obtain ⟨N, hN, c, hc⟩ := native_asymptotic_datum_of_leaf_g15 S.stable.toDistribution
    (F.leaf i) f.toHomeomorph x hrange
  refine ⟨N, ?_⟩
  let := N.topology
  let := N.charts
  have heq : Nonempty ((Fin N.rank → ℝ) ≃ₜ (Fin k → ℝ)) := by
    rw [hN]
    exact ⟨Homeomorph.refl _⟩
  exact ⟨heq.some.trans (e.toHomeomorph.trans c.toHomeomorph)⟩
/-- Apply the same intrinsic Euclidean-carrier construction to the inverse map,
with the two original invariant subbundles and their estimates exchanged.
Source: HPS (1977), §§6B–7, pp.111–116 and 127–129. -/
theorem franks_native_unstable_euclidean
    {n : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [T2Space M] [SecondCountableTopology M]
    [Bundle.RiemannianBundle
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    [IsRiemannianManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M]
    [IsContMDiffRiemannianBundle (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (S : InvariantRealTangentSplitting f)
    (hBounds : BundleAnosovBounds f S)
    (x : M) :
    ∃ N : NativeAsymptoticLeafDatum 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      f.symm.toHomeomorph S.unstable.toDistribution x,
      let := N.topology
      Nonempty ((Fin N.rank → ℝ) ≃ₜ StableAsymptoticLeaf f.symm.toHomeomorph x) := by
  let Sinv := TheoremAProof.inverseSplitting f S
  have hb : BundleAnosovBounds f.symm Sinv := by
    obtain ⟨C, r, hC, hr, hr1, hs, hu⟩ := hBounds
    exact ⟨C, r, hC, hr, hr1, hu, hs⟩
  exact franks_native_stable_euclidean f.symm Sinv hb x

/-- The nonzero-dimensional Franks--Manning lift-and-injectivity package.

Source: Franks, *Anosov Diffeomorphisms* (1970), Proposition (2.1), pp.70--71,
Theorem (2.2), pp.71--74 and Lemma 3.4, pp.75--76; Manning, *There are no new
Anosov diffeomorphisms on tori* (1974), pp.424--429. The theorem records the
remaining source construction after the original smooth metric and invariant
splitting have been installed: an integral matrix with no unit-modulus complex
eigenvalue, an injective toral semiconjugacy, and a bounded real lift. The
covering, global-product, intrinsic-leaf and index arguments are intentionally
kept as this named source-backed boundary, rather than hidden in the parent
classification theorem.
-/
theorem franks_manning_lift_data
    {n : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [T2Space M] [SecondCountableTopology M]
    [Bundle.RiemannianBundle
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    [IsRiemannianManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M]
    [IsContMDiffRiemannianBundle (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x)]
    (_hn : n ≠ 0)
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (S : InvariantRealTangentSplitting f)
    (hBounds : BundleAnosovBounds f S)
    (q : M ≃ₜ UnitAddTorus (Fin n)) :
    ∃ B : Matrix.GeneralLinearGroup (Fin n) ℤ,
      (∀ μ : ℂ, Module.End.HasEigenvalue
        (Matrix.mulVecLin (fun i j : Fin n ↦ (B i j : ℂ))) μ → ‖μ‖ ≠ 1) ∧
      ∃ h : C(M, UnitAddTorus (Fin n)), Function.Injective h ∧
        (∀ y, h (f y) = integralToralMap B (h y)) ∧
        ∃ H : C((Fin n → ℝ), (Fin n → ℝ)),
          (∃ K : ℝ, 0 ≤ K ∧ ∀ v, ‖v - H v‖ ≤ K) ∧
          (∀ v, Topology.coordinateProjection n (H v) =
            h (q.symm (Topology.coordinateProjection n v))) := by
  obtain ⟨b,hbfix,B,hB,hfinite,hcount,hcountNat,hbfix',hsquare⟩ := franks_manning_fixed_spectral_data q f S hBounds
  obtain ⟨u0,hu0,F,hF,hF0⟩ := franks_pointed_original_lift q f.toHomeomorph b hbfix
  subst b
  have hdata := native_pointed_semiconjugacy_of_homeomorph q u0 f.toHomeomorph
    (⟨F,F.continuous⟩ : C(_, _)) hF hF0 B hB
  obtain ⟨k,hk0,hkhomotopy,hksem,H,hH0,hHproj,hHbound,hHdeck,hHsem,hHiter⟩ :=
    hdata (by simpa only [Diffeomorph.coe_toHomeomorph] using hsquare)
  have periodicFixedOnto (m : ℕ) (hm : 0 < m) (y : UnitAddTorus (Fin n))
      (hy : (integralToralMap B)^[m] y = y) :
      ∃ x, (f : M → M)^[m] x = x ∧ k x = y := by
    let R := ((B : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℝ)).mulVecLin
    obtain ⟨L, hL⟩ := real_displacement_equivalence n B m
      (hyperbolic_power_not_one n _ hB m hm)
    apply franks_pullback_fixed_preimage q u0 ((f : M → M)^[m])
      ((integralToralMap B)^[m])
      ⟨(F : OriginalTorusPullback q → OriginalTorusPullback q)^[m], F.continuous.iterate m⟩
      ((show Function.Semiconj (fun x : OriginalTorusPullback q ↦ x.val.1)
        F (f : M → M) from hF).iterate_right m)
      k H hHproj hHbound hHdeck (R^m).toContinuousLinearMap L hL
      (FranksOriginalLift.toral_iterate_projection B m) ?_ y hy
    intro x
    change H ((F : OriginalTorusPullback q → OriginalTorusPullback q)^[m] x) = (R^m) (H x)
    rw [Module.End.pow_apply]
    exact hHiter m x
  have periodicFixedInj (m : ℕ) (hm : 0 < m) :
      ∀ x y, (f : M → M)^[m] x = x → (f : M → M)^[m] y = y → k x = k y → x = y := by
    apply FranksOriginalLift.fixed_map_injective_of_card ((f : M → M)^[m])
      ((integralToralMap B)^[m]) k
      ((show Function.Semiconj k (f : M → M) (integralToralMap B) from hksem).iterate_right m)
      (hfinite m hm)
      ((hcountNat m hm).trans (FranksOriginalLift.toral_iterate_fixed_card B hB m hm).symm)
      (periodicFixedOnto m hm)
  have periodicInj := FranksOriginalLift.injOn_periodicPts_of_fixed_injective
    (f : M → M) k periodicFixedInj
  have periodicOnto := FranksOriginalLift.surjOn_periodicPts_of_fixed_preimage
    (f : M → M) (integralToralMap B) k periodicFixedOnto
  have originalPeriodicDense := franks_original_periodic_density f S hBounds q B hB
    (FranksManningTarget.dense_periodicPts B) k hksem periodicInj periodicOnto
  let : Nonempty M := ⟨q.symm 0⟩
  let g : UnitAddTorus (Fin n) ≃ₜ UnitAddTorus (Fin n) := {
    toFun := integralToralMap B
    invFun := integralToralMap B⁻¹
    left_inv := fun x ↦ by
      rw [integral_toral_map_comp, inv_mul_cancel]
      ext i
      simp [integralToralMap, Matrix.one_apply]
    right_inv := fun x ↦ by
      rw [integral_toral_map_comp, mul_inv_cancel]
      ext i
      simp [integralToralMap, Matrix.one_apply]
    continuous_toFun := Dynamics.integralToralMap_continuous B
    continuous_invFun := Dynamics.integralToralMap_continuous B⁻¹ }
  obtain ⟨ε, hε, hexp⟩ := integral_toral_biinfinite_expansivity B hB
  have hexp' : ∀ x y : UnitAddTorus (Fin n),
      (∀ t : ℤ, dist ((g.toEquiv ^ t) x) ((g.toEquiv ^ t) y) ≤ ε) → x = y := by
    intro x y hdist
    have hrec (x : UnitAddTorus (Fin n)) (t : ℤ) :
        (g.toEquiv ^ (t+1)) x = integralToralMap B ((g.toEquiv ^ t) x) := by
      rw [add_comm t 1, zpow_add, zpow_one]
      rfl
    simpa only [zpow_zero, Equiv.Perm.one_apply] using
      hexp (fun t ↦ (g.toEquiv ^ t) x) (fun t ↦ (g.toEquiv ^ t) y)
        (hrec x) (hrec y) hdist
  have hcyclic : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ r : ℕ, 0 < r → ∀ v : Fin r → M,
      (∀ i, dist (f (v i)) (v (finRotate r i)) < δ) →
      ∃ l : Fin r → M, Function.Semiconj l (finRotate r) f.toHomeomorph ∧
        ∀ i, dist (l i) (v i) < η := by
    obtain ⟨C,lam,hC,hlam,hlam1,hs,hu⟩ := hBounds
    have hR : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M := inferInstance
    have hsource := smale_original_anosov_cyclic_shadowing_source f S.stable S.unstable
      (FranksLefschetzCoverCount.suppliedSmoothMetric (n := n) (M := M)) C lam
      hR hC hlam hlam1 S.isCompl S.stable_map S.unstable_map
      (fun x j v hv ↦ hs j x v hv) (fun x j v hv ↦ hu j x v hv)
    intro η hη
    obtain ⟨δ,hδ,hshadow⟩ := hsource (η/2) (half_pos hη)
    refine ⟨δ,hδ,?_⟩
    intro r hr v hv
    obtain ⟨l,hl,hld⟩ := hshadow r hr v hv
    exact ⟨l,hl,fun i ↦ (hld i).trans_lt (half_lt_self hη)⟩
  have homoclinicRigidity : ∀ x y : M, k x = k y →
      ForwardAsymptotic f.toHomeomorph x y → ForwardAsymptotic f.toHomeomorph.symm x y →
      x = y :=
    FranksOriginalCover.eq_of_homoclinic_of_same_image f.toHomeomorph g k hksem ε hε
      hexp' periodicFixedInj originalPeriodicDense hcyclic
  let : EMetricSpace M := MetricSpace.toEMetricSpace
  obtain ⟨hsNative, huNative⟩ :=
    HPS.anosov_global_lamination_distance M f S hBounds
  have nativeStable :=
    covering_conjugacy_native_from_lamination_g15
      S.stable.toDistribution f f hsNative
  have nativeUnstable :=
    covering_conjugacy_native_from_lamination_g15
      S.unstable.toDistribution f f.symm huNative
  obtain ⟨ιs, Ls, rs, topS, chartsS, smoothS, selectedStable,
    ⟨βs, dims, Ts, topTs, ⟨boxesS⟩⟩, ⟨invarianceS⟩, familiesS, coherentS, extraS⟩ := hsNative
  let := topS
  let := chartsS
  let := smoothS
  let := topTs
  obtain ⟨ιu, Lu, ru, topU, chartsU, smoothU, selectedUnstable,
    ⟨βu, dimu, Tu, topTu, ⟨boxesU⟩⟩, ⟨invarianceU⟩, familiesU, coherentU, extraU⟩ := huNative
  let := topU
  let := chartsU
  let := smoothU
  let := topTu
  let stableRank := Module.finrank ℝ (S.stable.toDistribution u0.val.1)
  have hrS (i : ιs) : rs i = stableRank := by
    let := (selectedStable.leaf i).connected
    obtain ⟨z⟩ := (inferInstance : Nonempty (Ls i))
    exact ((selectedStable.leaf i).finrank_tangent z).symm.trans
      (S.stable.finrank_eq _ u0.val.1)
  have hrSfun : rs = fun _ ↦ stableRank := funext hrS
  cases hrSfun
  let unstableRank := Module.finrank ℝ (S.unstable.toDistribution u0.val.1)
  have hrU (i : ιu) : ru i = unstableRank := by
    let := (selectedUnstable.leaf i).connected
    obtain ⟨z⟩ := (inferInstance : Nonempty (Lu i))
    exact ((selectedUnstable.leaf i).finrank_tangent z).symm.trans
      (S.unstable.finrank_eq _ u0.val.1)
  have hrUfun : ru = fun _ ↦ unstableRank := funext hrU
  cases hrUfun
  obtain ⟨_, _, _, _, ⟨identificationS, _⟩, _, _⟩ := extraS
  obtain ⟨_, _, _, _, ⟨identificationU, _⟩, _, _⟩ := extraU
  have selectedStableComplete (i : ιs) : Nonempty ((Fin stableRank → ℝ) ≃ₜ Ls i) := by
    obtain ⟨e⟩ := HPS.native_stable_euclidean_from_anosov M f S hBounds
      selectedStable boxesS identificationS i
    exact ⟨e.toHomeomorph⟩
  let Sinv := TheoremAProof.inverseSplitting f S
  have hBoundsInv : BundleAnosovBounds f.symm Sinv := by
    obtain ⟨C,r,hC,hr,hr1,hs,hu⟩ := hBounds
    exact ⟨C,r,hC,hr,hr1,hu,hs⟩
  have selectedUnstableComplete (i : ιu) : Nonempty ((Fin unstableRank → ℝ) ≃ₜ Lu i) := by
    obtain ⟨e⟩ := HPS.native_stable_euclidean_from_anosov M f.symm Sinv hBoundsInv
      selectedUnstable boxesU identificationU i
    exact ⟨e.toHomeomorph⟩
  obtain ⟨Cselected,τselected,hCselected,hτselected,hτselected1,hsselected,huselected⟩ := (show BundleAnosovBounds f S from hBounds)
  let metricSelected := FranksLefschetzCoverCount.suppliedSmoothMetric (n := n) (M := M)
  have hscaleSelected (r : ℕ) (x : M)
      (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
      Cselected*τselected^r*‖v‖ ≤ max 1 Cselected*τselected^r*‖v‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right 1 Cselected)
      (pow_nonneg hτselected.le _)) (norm_nonneg _)
  let originalMetric : MetricSpace M := inferInstance
  obtain ⟨metricProduct, βProduct, γProduct, εProduct, hγProduct, hβProduct, hεProduct,
    htopProduct, adaptedStable, adaptedUnstable, bracketProduct, hbracketContinuous,
    hbracketUnique, localProducts⟩ :=
    Ghys.selectedPartitionProducts f S metricSelected (max 1 Cselected) τselected
      (le_max_left _ _) hτselected hτselected1
      (fun x r v hv ↦ (hsselected r x v hv).trans (hscaleSelected r x v))
      (fun x r v hv ↦ (huselected r x v hv).trans (hscaleSelected r x v))
      selectedStable selectedUnstable invarianceS invarianceU
  let : MetricSpace M := originalMetric
  have hksemInv (x : M) : k (f.symm.toHomeomorph x) = integralToralMap B⁻¹ (k x) := by
    have hone (z : UnitAddTorus (Fin n)) : integralToralMap 1 z = z := by
      ext i
      simp [integralToralMap, Matrix.one_apply]
    have hi := congrArg (integralToralMap B⁻¹) (hksem (f.symm x))
    simpa only [Diffeomorph.coe_toHomeomorph, f.apply_symm_apply,
      FranksManningTarget.map_comp, inv_mul_cancel, hone] using hi.symm
  let nativeSelectedStable := nativeInvariantLeafSystemOfPartition
    S.stable.toDistribution f selectedStable invarianceS
  let nativeSelectedUnstable := nativeInvariantLeafSystemInverse S.unstable.toDistribution f
    (nativeInvariantLeafSystemOfPartition S.unstable.toDistribution f selectedUnstable invarianceU)
  let selectedProduct := fun x : M ↦ (localProducts x).some
  have nativeStableLPC (x : M) :
      LocallyPathConnectedSpace (nativeSelectedStable.leaf x).Carrier := by
    change LocallyPathConnectedSpace (Ls (Classical.choose (selectedStable.cover x)))
    exact (selectedStableComplete _).some.locallyPathConnectedSpace
  have nativeUnstableLPC (x : M) :
      LocallyPathConnectedSpace (nativeSelectedUnstable.leaf x).Carrier := by
    change LocallyPathConnectedSpace (Lu (Classical.choose (selectedUnstable.cover x)))
    exact (selectedUnstableComplete _).some.locallyPathConnectedSpace
  have liftedBoxExistence (x : OriginalTorusPullback q) := by
    letI := nativeStableLPC x.val.1
    letI := nativeUnstableLPC x.val.1
    letI := (selectedProduct x.val.1).stable_open.locallyPathConnectedSpace
    letI := (selectedProduct x.val.1).unstable_open.locallyPathConnectedSpace
    let W := {z : OriginalTorusPullback q | metricProduct.dist z.val.1 x.val.1 < γProduct / 3}
    have hW : IsOpen W := by
      let : MetricSpace M := metricProduct.replaceTopology htopProduct.symm
      exact isOpen_lt ((continuous_subtype_val.fst).dist continuous_const) continuous_const
    exact FranksOriginalCover.covering_lift_pathConnected_box_within
      (fun z : OriginalTorusPullback q ↦ z.val.1) (franks_original_projection_cover q).1
      ⟨(selectedProduct x.val.1).neighborhood, (selectedProduct x.val.1).neighborhood_open⟩
      (selectedProduct x.val.1).product x (selectedProduct x.val.1).neighborhood_center
      W hW (by change metricProduct.dist x.val.1 x.val.1 < γProduct / 3
               rw [metricProduct.dist_self]; positivity)
  choose liftedStableDomain liftedUnstableDomain liftedBox liftedStableConnected
    liftedUnstableConnected liftedBoxEmbedding liftedBoxCenter liftedBoxSmall liftedBoxProjection
    using liftedBoxExistence
  have selectedStableLiftData (i : ιs) (a : Ls i) (x : OriginalTorusPullback q)
      (hx : x.val.1 = (selectedStable.leaf i).inclusion a) :
      ∃ l : C(Ls i, OriginalTorusPullback q), Function.Injective l ∧ l a = x ∧
        (∀ b, (l b).val.1 = (selectedStable.leaf i).inclusion b) ∧
        Set.range l = liftedIntrinsicLeafRange (fun z : OriginalTorusPullback q ↦ z.val.1)
          (selectedStable.leaf i).inclusion a x ∧
        ∀ b, H (l b) - H x ∈
          fullDecaySubmodule (FranksMatrix.realAction B).toContinuousLinearEquiv := by
    obtain ⟨e⟩ := selectedStableComplete i
    let : PathConnectedSpace (Ls i) := e.pathConnectedSpace
    let j : C(Ls i,M) := ⟨(selectedStable.leaf i).inclusion,
      (selectedStable.leaf i).immersion.contMDiff.continuous⟩
    obtain ⟨l,hli,hla,hlp,hlrange⟩ := FranksOriginalCover.euclidean_leaf_lift_with_range e
      (fun z : OriginalTorusPullback q ↦ z.val.1) (franks_original_projection_cover q).1
      j (selectedStable.leaf i).injective a x hx
    refine ⟨l,hli,hla,hlp,hlrange,?_⟩
    intro b
    have hcarrier (v : Ls i) : ForwardAsymptotic f.toHomeomorph x.val.1 (j v) := by
      rw [hx]
      change (selectedStable.leaf i).inclusion v ∈
        {y | ForwardAsymptotic f ((selectedStable.leaf i).inclusion a) y}
      rw [← identificationS.range_eq_forwardAsymptotic i a]
      exact Set.mem_range_self v
    have himage := FranksOriginalCover.unit_forward_affine_leaf_image B f.toHomeomorph k hksem
      (fun z : OriginalTorusPullback q ↦ z.val.1) (franks_original_projection_cover q).1
      H hHproj x j j.continuous a hx.symm hcarrier
    obtain ⟨v,hv,he⟩ := himage ⟨l b, hlrange ▸ Set.mem_range_self b, rfl⟩
    have he' : H (l b) - H x = v := by rw [← he]; exact add_sub_cancel_left _ _
    rwa [he']
  have selectedUnstableLiftData (i : ιu) (a : Lu i) (x : OriginalTorusPullback q)
      (hx : x.val.1 = (selectedUnstable.leaf i).inclusion a) :
      ∃ l : C(Lu i, OriginalTorusPullback q), Function.Injective l ∧ l a = x ∧
        (∀ b, (l b).val.1 = (selectedUnstable.leaf i).inclusion b) ∧
        Set.range l = liftedIntrinsicLeafRange (fun z : OriginalTorusPullback q ↦ z.val.1)
          (selectedUnstable.leaf i).inclusion a x ∧
        ∀ b, H (l b) - H x ∈
          fullDecaySubmodule (FranksMatrix.realAction B⁻¹).toContinuousLinearEquiv := by
    obtain ⟨e⟩ := selectedUnstableComplete i
    let : PathConnectedSpace (Lu i) := e.pathConnectedSpace
    let j : C(Lu i,M) := ⟨(selectedUnstable.leaf i).inclusion,
      (selectedUnstable.leaf i).immersion.contMDiff.continuous⟩
    obtain ⟨l,hli,hla,hlp,hlrange⟩ := FranksOriginalCover.euclidean_leaf_lift_with_range e
      (fun z : OriginalTorusPullback q ↦ z.val.1) (franks_original_projection_cover q).1
      j (selectedUnstable.leaf i).injective a x hx
    refine ⟨l,hli,hla,hlp,hlrange,?_⟩
    intro b
    have hcarrier (v : Lu i) : ForwardAsymptotic f.symm.toHomeomorph x.val.1 (j v) := by
      rw [hx]
      change (selectedUnstable.leaf i).inclusion v ∈
        {y | ForwardAsymptotic f.symm ((selectedUnstable.leaf i).inclusion a) y}
      rw [← identificationU.range_eq_forwardAsymptotic i a]
      exact Set.mem_range_self v
    have himage := FranksOriginalCover.unit_forward_affine_leaf_image B⁻¹ f.symm.toHomeomorph k hksemInv
      (fun z : OriginalTorusPullback q ↦ z.val.1) (franks_original_projection_cover q).1
      H hHproj x j j.continuous a hx.symm hcarrier
    obtain ⟨v,hv,he⟩ := himage ⟨l b, hlrange ▸ Set.mem_range_self b, rfl⟩
    have he' : H (l b) - H x = v := by rw [← he]; exact add_sub_cancel_left _ _
    rwa [he']
  let projectionOriginal := fun z : OriginalTorusPullback q ↦ z.val.1
  let inclusionsStable := fun i ↦ (selectedStable.leaf i).inclusion
  let inclusionsUnstable := fun i ↦ (selectedUnstable.leaf i).inclusion
  let stableRelation := FranksOriginalCover.intrinsicLiftedPathSetoid
    projectionOriginal inclusionsStable (fun i ↦ (selectedStable.leaf i).injective)
    selectedStable.cover selectedStable.disjoint
  let unstableRelation := FranksOriginalCover.intrinsicLiftedPathSetoid
    projectionOriginal inclusionsUnstable (fun i ↦ (selectedUnstable.leaf i).injective)
    selectedUnstable.cover selectedUnstable.disjoint
  have stableProjectionInj (x : OriginalTorusPullback q) :
      Set.InjOn projectionOriginal {z | stableRelation x z} := by
    obtain ⟨i,a,ha⟩ := selectedStable.cover x.val.1
    obtain ⟨l,hli,hla,hlp,hlrange,himage⟩ := selectedStableLiftData i a x ha.symm
    intro y hy z hz he
    have hy' := (FranksOriginalCover.intrinsicLiftedPathRel_iff_range projectionOriginal
      inclusionsStable (fun i ↦ (selectedStable.leaf i).injective)
      selectedStable.disjoint i a x y ha).mp hy
    have hz' := (FranksOriginalCover.intrinsicLiftedPathRel_iff_range projectionOriginal
      inclusionsStable (fun i ↦ (selectedStable.leaf i).injective)
      selectedStable.disjoint i a x z ha).mp hz
    rw [← hlrange] at hy' hz'
    obtain ⟨b,rfl⟩ := hy'
    obtain ⟨c,rfl⟩ := hz'
    apply congrArg l
    apply (selectedStable.leaf i).injective
    exact (hlp b).symm.trans (he.trans (hlp c))
  have unstableProjectionInj (x : OriginalTorusPullback q) :
      Set.InjOn projectionOriginal {z | unstableRelation x z} := by
    obtain ⟨i,a,ha⟩ := selectedUnstable.cover x.val.1
    obtain ⟨l,hli,hla,hlp,hlrange,himage⟩ := selectedUnstableLiftData i a x ha.symm
    intro y hy z hz he
    have hy' := (FranksOriginalCover.intrinsicLiftedPathRel_iff_range projectionOriginal
      inclusionsUnstable (fun i ↦ (selectedUnstable.leaf i).injective)
      selectedUnstable.disjoint i a x y ha).mp hy
    have hz' := (FranksOriginalCover.intrinsicLiftedPathRel_iff_range projectionOriginal
      inclusionsUnstable (fun i ↦ (selectedUnstable.leaf i).injective)
      selectedUnstable.disjoint i a x z ha).mp hz
    rw [← hlrange] at hy' hz'
    obtain ⟨b,rfl⟩ := hy'
    obtain ⟨c,rfl⟩ := hz'
    apply congrArg l
    apply (selectedUnstable.leaf i).injective
    exact (hlp b).symm.trans (he.trans (hlp c))
  have stableRelationImage (x y : OriginalTorusPullback q) (hxy : stableRelation x y) :
      H y - H x ∈ fullDecaySubmodule (FranksMatrix.realAction B).toContinuousLinearEquiv ∧
      ForwardAsymptotic f.toHomeomorph x.val.1 y.val.1 := by
    obtain ⟨i,a,ha,hy⟩ := hxy
    obtain ⟨l,hli,hla,hlp,hlrange,himage⟩ := selectedStableLiftData i a x ha.symm
    rw [← hlrange] at hy
    obtain ⟨b,rfl⟩ := hy
    refine ⟨himage b,?_⟩
    change _ = x.val.1 at ha
    rw [hlp, ← ha]
    change (selectedStable.leaf i).inclusion b ∈
      {y | ForwardAsymptotic f ((selectedStable.leaf i).inclusion a) y}
    rw [← identificationS.range_eq_forwardAsymptotic i a]
    exact Set.mem_range_self b
  have unstableRelationImage (x y : OriginalTorusPullback q) (hxy : unstableRelation x y) :
      H y - H x ∈ fullDecaySubmodule (FranksMatrix.realAction B⁻¹).toContinuousLinearEquiv ∧
      ForwardAsymptotic f.symm.toHomeomorph x.val.1 y.val.1 := by
    obtain ⟨i,a,ha,hy⟩ := hxy
    obtain ⟨l,hli,hla,hlp,hlrange,himage⟩ := selectedUnstableLiftData i a x ha.symm
    rw [← hlrange] at hy
    obtain ⟨b,rfl⟩ := hy
    refine ⟨himage b,?_⟩
    change _ = x.val.1 at ha
    rw [hlp, ← ha]
    change (selectedUnstable.leaf i).inclusion b ∈
      {y | ForwardAsymptotic f.symm ((selectedUnstable.leaf i).inclusion a) y}
    rw [← identificationU.range_eq_forwardAsymptotic i a]
    exact Set.mem_range_self b
  have hrealInverse : (FranksMatrix.realAction B⁻¹).toContinuousLinearEquiv =
      (FranksMatrix.realAction B).toContinuousLinearEquiv.symm := by
    ext v i
    rfl
  have decayComplement : IsCompl
      (fullDecaySubmodule (FranksMatrix.realAction B).toContinuousLinearEquiv)
      (fullDecaySubmodule (FranksMatrix.realAction B⁻¹).toContinuousLinearEquiv) := by
    rw [hrealInverse]
    exact FranksOriginalCover.full_decay_submodule_isCompl_of_hyperbolic
      (FranksMatrix.realAction B).toContinuousLinearEquiv
      (FranksMatrix.complexification_hyperbolic B hB)
  have nativeIntersectionUnique (a b z z' : OriginalTorusPullback q)
      (hu : unstableRelation a z) (hs : stableRelation b z)
      (hu' : unstableRelation a z') (hs' : stableRelation b z') : z = z' := by
    have hrs := stableRelation.trans (stableRelation.symm hs) hs'
    have hru := unstableRelation.trans (unstableRelation.symm hu) hu'
    have himages := stableRelationImage z z' hrs
    have himageu := unstableRelationImage z z' hru
    have hH : H z' = H z := sub_eq_zero.mp
      (Submodule.disjoint_def.mp decayComplement.disjoint _ himages.1 himageu.1)
    have hp : z.val.1 = z'.val.1 := homoclinicRigidity _ _
      ((hHproj z).symm.trans ((congrArg (coordinateProjection n) hH.symm).trans (hHproj z')))
      himages.2 himageu.2
    exact stableProjectionInj z (stableRelation.refl z) hrs hp
  have boxRowNative (x : OriginalTorusPullback q)
      (u u' : liftedStableDomain x) (v : liftedUnstableDomain x) :
      stableRelation (liftedBox x (u,v)) (liftedBox x (u',v)) := by
    let := (isPathConnected_iff_pathConnectedSpace.mp (liftedStableConnected x))
    apply FranksOriginalCover.lifted_box_row_native projectionOriginal inclusionsStable
      (liftedBox x) (liftedBoxEmbedding x).continuous ?_ u u' v
    intro v
    obtain ⟨j,hj,hji,hjp⟩ := Ghys.adaptedProduct_unstable_lift f.symm
      S.unstable.toDistribution S.stable.toDistribution metricProduct
      nativeSelectedUnstable nativeSelectedStable
      (Ghys.reverseNativeBracket metricProduct bracketProduct)
      (Ghys.reverseNativeBracket_intersection f metricProduct bracketProduct hbracketUnique)
      adaptedStable.some x.val.1
      (Ghys.reverseNativeProduct f S.stable.toDistribution S.unstable.toDistribution
        metricProduct nativeSelectedStable nativeSelectedUnstable bracketProduct x.val.1
        (selectedProduct x.val.1)) v.val
    let b := (nativeSelectedUnstable.leaf x.val.1).inclusion v.val.val
    refine ⟨Classical.choose (selectedStable.cover b),
      ⟨fun u ↦ j u.val, hj.comp continuous_subtype_val⟩, ?_⟩
    intro u
    exact (liftedBoxProjection x (u,v)).trans (hjp u.val).symm
  have boxColumnNative (x : OriginalTorusPullback q)
      (u : liftedStableDomain x) (v v' : liftedUnstableDomain x) :
      unstableRelation (liftedBox x (u,v)) (liftedBox x (u,v')) := by
    let := (isPathConnected_iff_pathConnectedSpace.mp (liftedUnstableConnected x))
    apply FranksOriginalCover.lifted_box_row_native projectionOriginal inclusionsUnstable
      (fun w ↦ liftedBox x (w.2,w.1)) ((liftedBoxEmbedding x).continuous.comp continuous_swap)
      ?_ v v' u
    intro u
    obtain ⟨j,hj,hji,hjp⟩ := Ghys.adaptedProduct_unstable_lift f
      S.stable.toDistribution S.unstable.toDistribution metricProduct
      nativeSelectedStable nativeSelectedUnstable bracketProduct hbracketUnique
      adaptedUnstable.some x.val.1 (selectedProduct x.val.1) u.val
    let b := (nativeSelectedStable.leaf x.val.1).inclusion u.val.val
    refine ⟨Classical.choose (selectedUnstable.cover b),
      ⟨fun v ↦ j v.val, hj.comp continuous_subtype_val⟩, ?_⟩
    intro v
    exact (liftedBoxProjection x (u,v)).trans (hjp v.val).symm
  let originalCoordinates : OriginalTorusPullback q ≃ₜ (Fin n → ℝ) := {
    toFun := fun x ↦ x.val.2
    invFun := fun v ↦ ⟨(q.symm (originalTorusProjection n v),v),q.apply_symm_apply _⟩
    left_inv := fun x ↦ by
      apply Subtype.ext
      exact Prod.ext ((congrArg q.symm x.property).symm.trans (q.symm_apply_apply _)) rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := continuous_snd.comp continuous_subtype_val
    continuous_invFun := ((q.symm.continuous.comp (originalTorusProjection n).continuous).prodMk
      continuous_id).subtype_mk _ }
  let : PathConnectedSpace (OriginalTorusPullback q) := originalCoordinates.symm.pathConnectedSpace
  have hproperH : IsProperMap H := by
    obtain ⟨K,hK,hb⟩ := hHbound
    exact FranksOriginalCover.proper_of_bounded_coordinate_correction_g2
      originalCoordinates H u0.val.2 K hb
  let : ∀ x, PathConnectedSpace (liftedStableDomain x) :=
    fun x ↦ isPathConnected_iff_pathConnectedSpace.mp (liftedStableConnected x)
  let : ∀ x, PathConnectedSpace (liftedUnstableDomain x) :=
    fun x ↦ isPathConnected_iff_pathConnectedSpace.mp (liftedUnstableConnected x)
  let stableGenerated := Relation.EqvGen.setoid
    (FranksOriginalCover.rectangularPlaqueRel liftedBox)
  let unstableGenerated := Relation.EqvGen.setoid
    (FranksOriginalCover.rectangularPlaqueRel (fun i w ↦ liftedBox i (w.2,w.1)))
  have generatedStableNative {x y : OriginalTorusPullback q} (hxy : stableGenerated x y) :
      stableRelation x y := FranksOriginalCover.rectangularPlaque_eqvGen_subrelation
        liftedBox stableRelation boxRowNative hxy
  have generatedUnstableNative {x y : OriginalTorusPullback q} (hxy : unstableGenerated x y) :
      unstableRelation x y := FranksOriginalCover.rectangularPlaque_eqvGen_subrelation
        (fun i w ↦ liftedBox i (w.2,w.1)) unstableRelation
        (fun i v v' u ↦ boxColumnNative i u v v') hxy
  have generatedIntersectionUnique (a b z z' : OriginalTorusPullback q)
      (hu : unstableGenerated a z) (hs : stableGenerated b z)
      (hu' : unstableGenerated a z') (hs' : stableGenerated b z') : z = z' :=
    nativeIntersectionUnique a b z z' (generatedUnstableNative hu) (generatedStableNative hs)
      (generatedUnstableNative hu') (generatedStableNative hs')
  have globalProduct : ∀ a b : OriginalTorusPullback q, ∃ z,
      unstableGenerated a z ∧ stableGenerated b z :=
    FranksOriginalCover.global_product_of_native_rectangular_plaques
      liftedBox liftedBoxEmbedding (fun x ↦ ⟨x,liftedBoxCenter x⟩)
      H hproperH _ _ decayComplement
      (fun i u u' v ↦ (stableRelationImage _ _ (boxRowNative i u u' v)).1)
      (fun i u v v' ↦ (unstableRelationImage _ _ (boxColumnNative i u v v')).1)
      generatedIntersectionUnique
  obtain ⟨generatedUnstableEq,generatedStableEq⟩ :=
    FranksOriginalCover.refining_leaf_relations_eq_of_global_product
      unstableGenerated stableGenerated unstableRelation stableRelation
      (fun _ _ h ↦ generatedUnstableNative h) (fun _ _ h ↦ generatedStableNative h)
      nativeIntersectionUnique globalProduct
  obtain ⟨⟨crossing,hcrossing⟩,closedUnstable,closedStable⟩ :=
    FranksOriginalCover.continuous_rectangularPlaque_product liftedBox liftedBoxEmbedding
      (fun x ↦ ⟨x,liftedBoxCenter x⟩) generatedIntersectionUnique globalProduct
  have hFback (x : OriginalTorusPullback q) :
      projectionOriginal (F.symm x) = f.symm (projectionOriginal x) := by
    apply f.injective
    change f ((F.symm x).val.1) = f (f.symm x.val.1)
    rw [f.apply_symm_apply]
    exact (hF (F.symm x)).symm.trans
      (congrArg (fun z : OriginalTorusPullback q ↦ z.val.1) (F.apply_symm_apply x))
  have stableBackward (x y : OriginalTorusPullback q) (hxy : stableGenerated x y) :
      stableGenerated (F.symm x) (F.symm y) := by
    apply (generatedStableEq _ _).mpr
    apply FranksOriginalCover.intrinsicLiftedPathRel_map projectionOriginal inclusionsStable
      ⟨F.symm,F.symm.continuous⟩ f.symm hFback ?_ ((generatedStableEq _ _).mp hxy)
    intro i
    obtain ⟨j,rfl⟩ := invarianceS.permutation.surjective i
    refine ⟨j,⟨(invarianceS.transport j).symm,
      (invarianceS.transport j).symm.continuous⟩,?_⟩
    intro a
    apply f.injective
    change f ((selectedStable.leaf j).inclusion ((invarianceS.transport j).symm a)) =
      f (f.symm ((selectedStable.leaf (invarianceS.permutation j)).inclusion a))
    rw [f.apply_symm_apply, ← invarianceS.intertwining j]
    exact congrArg (selectedStable.leaf (invarianceS.permutation j)).inclusion
      ((invarianceS.transport j).apply_symm_apply a)
  have unstableForward (x y : OriginalTorusPullback q) (hxy : unstableGenerated x y) :
      unstableGenerated (F x) (F y) := by
    apply (generatedUnstableEq _ _).mpr
    exact FranksOriginalCover.intrinsicLiftedPathRel_map projectionOriginal inclusionsUnstable
      ⟨F,F.continuous⟩ f hF
      (fun i ↦ ⟨invarianceU.permutation i,
        ⟨invarianceU.transport i,(invarianceU.transport i).continuous⟩,
        invarianceU.intertwining i⟩) ((generatedUnstableEq _ _).mp hxy)
  let integerDeck := fun z : Fin n → ℤ ↦ fun x : OriginalTorusPullback q ↦ franksIntegerDeck q z • x
  have integerDeckContinuous (z : Fin n → ℤ) : Continuous (integerDeck z) :=
    (franksIntegerDeck q z).val.continuous
  have integerDeckProjection (z : Fin n → ℤ) (x : OriginalTorusPullback q) :
      projectionOriginal (integerDeck z x) = projectionOriginal x := rfl
  have integerDeckImage (z : Fin n → ℤ) (x : OriginalTorusPullback q) :
      H (integerDeck z x) = H x + fun i ↦ (z i : ℝ) := by
    funext i
    have h := congrFun (hHdeck (franksIntegerDeck q z) x) i
    change (x.val.2 i + (z i : ℝ) - u0.val.2 i) - H (integerDeck z x) i =
      (x.val.2 i-u0.val.2 i)-H x i at h
    change H (integerDeck z x) i = H x i + (z i : ℝ)
    linarith
  have stableDeck (z : Fin n → ℤ) (x y : OriginalTorusPullback q)
      (hxy : stableGenerated x y) : stableGenerated (integerDeck z x) (integerDeck z y) := by
    apply (generatedStableEq _ _).mpr
    exact FranksOriginalCover.intrinsicLiftedPathRel_deck projectionOriginal inclusionsStable
      ⟨integerDeck z,integerDeckContinuous z⟩ (integerDeckProjection z)
      ((generatedStableEq _ _).mp hxy)
  have unstableDeck (z : Fin n → ℤ) (x y : OriginalTorusPullback q)
      (hxy : unstableGenerated x y) : unstableGenerated (integerDeck z x) (integerDeck z y) := by
    apply (generatedUnstableEq _ _).mpr
    exact FranksOriginalCover.intrinsicLiftedPathRel_deck projectionOriginal inclusionsUnstable
      ⟨integerDeck z,integerDeckContinuous z⟩ (integerDeckProjection z)
      ((generatedUnstableEq _ _).mp hxy)
  have boxDiameter (x : OriginalTorusPullback q)
      (w w' : liftedStableDomain x × liftedUnstableDomain x) :
      metricProduct.dist (projectionOriginal (liftedBox x w'))
        (projectionOriginal (liftedBox x w)) ≤ γProduct := by
    have h1 := liftedBoxSmall x (Set.mem_range_self w)
    have h2 := liftedBoxSmall x (Set.mem_range_self w')
    change metricProduct.dist (liftedBox x w).val.1 x.val.1 < γProduct/3 at h1
    change metricProduct.dist (liftedBox x w').val.1 x.val.1 < γProduct/3 at h2
    have ht := metricProduct.dist_triangle (liftedBox x w').val.1 x.val.1 (liftedBox x w).val.1
    rw [metricProduct.dist_comm x.val.1] at ht
    change metricProduct.dist (liftedBox x w').val.1 (liftedBox x w).val.1 ≤ γProduct
    linarith
  have rowUniformDecay (x : OriginalTorusPullback q) (r : ℝ) (hr : 0 < r) :
      ∃ N : ℕ, ∀ u u' v, ∀ m ≥ N,
        metricProduct.dist ((f : M → M)^[m] (projectionOriginal (liftedBox x (u,v))))
          ((f : M → M)^[m] (projectionOriginal (liftedBox x (u',v)))) < r := by
    obtain ⟨N,hN⟩ := FranksOriginalCover.native_core_uniform_tail f metricProduct
      hγProduct hεProduct htopProduct bracketProduct hbracketUnique r hr
    refine ⟨N,fun u u' v m hm ↦ hN _ _ ?_ m hm⟩
    dsimp only [projectionOriginal]
    rw [liftedBoxProjection, liftedBoxProjection]
    apply FranksOriginalCover.native_product_row_core f S.stable.toDistribution
      S.unstable.toDistribution metricProduct nativeSelectedStable nativeSelectedUnstable
      adaptedStable.some hβProduct bracketProduct hbracketUnique
      x.val.1 (selectedProduct x.val.1) u.val u'.val v.val
    simpa only [projectionOriginal, liftedBoxProjection] using boxDiameter x (u,v) (u',v)
  have columnUniformDecay (x : OriginalTorusPullback q) (r : ℝ) (hr : 0 < r) :
      ∃ N : ℕ, ∀ v v' u, ∀ m ≥ N,
        metricProduct.dist ((f.symm : M → M)^[m] (projectionOriginal (liftedBox x (u,v))))
          ((f.symm : M → M)^[m] (projectionOriginal (liftedBox x (u,v')))) < r := by
    obtain ⟨N,hN⟩ := FranksOriginalCover.native_core_uniform_tail f.symm metricProduct
      hγProduct hεProduct htopProduct (Ghys.reverseNativeBracket metricProduct bracketProduct)
      (Ghys.reverseNativeBracket_intersection f metricProduct bracketProduct hbracketUnique) r hr
    refine ⟨N,fun v v' u m hm ↦ hN _ _ ?_ m hm⟩
    dsimp only [projectionOriginal]
    rw [liftedBoxProjection, liftedBoxProjection]
    apply FranksOriginalCover.native_product_column_core f S.stable.toDistribution
      S.unstable.toDistribution metricProduct nativeSelectedStable nativeSelectedUnstable
      adaptedUnstable.some hβProduct bracketProduct hbracketUnique
      x.val.1 (selectedProduct x.val.1) u.val v.val v'.val
    simpa only [projectionOriginal, liftedBoxProjection] using boxDiameter x (u,v) (u,v')
  have hHsemExplicit (x : OriginalTorusPullback q) :
      H (F x) = FranksMatrix.realAction B (H x) := hHsem x
  have backwardEqualImage (x y : OriginalTorusPullback q) (hxy : H x = H y) :
      H (F.symm x) = H (F.symm y) := by
    apply (FranksMatrix.realAction B).injective
    rw [← hHsemExplicit, ← hHsemExplicit, F.apply_symm_apply, F.apply_symm_apply]
    exact hxy
  have forwardEqualImage (x y : OriginalTorusPullback q) (hxy : H x = H y) :
      H (F x) = H (F y) := by
    rw [hHsemExplicit, hHsemExplicit, hxy]
  let : MetricSpace M := metricProduct.replaceTopology htopProduct.symm
  obtain ⟨stableDiagonalDecay,stableGeneratorDecay⟩ :=
    FranksOriginalCover.rectangularPlaque_local_uniform_generators
      liftedBox liftedBoxEmbedding (fun x ↦ ⟨x,liftedBoxCenter x⟩)
      (fun m x y ↦ metricProduct.dist ((f : M → M)^[m] (projectionOriginal x))
        ((f : M → M)^[m] (projectionOriginal y))) rowUniformDecay generatedIntersectionUnique
  obtain ⟨unstableDiagonalDecay,unstableGeneratorDecay⟩ :=
    FranksOriginalCover.rectangularPlaque_local_uniform_generators
      (fun i w ↦ liftedBox i (w.2,w.1))
      (fun i ↦ (liftedBoxEmbedding i).comp (Homeomorph.prodComm _ _).isOpenEmbedding)
      (fun x ↦ ⟨x,by obtain ⟨w,hw⟩ := liftedBoxCenter x; exact ⟨(w.2,w.1),hw⟩⟩)
      (fun m x y ↦ metricProduct.dist ((f.symm : M → M)^[m] (projectionOriginal x))
        ((f.symm : M → M)^[m] (projectionOriginal y))) columnUniformDecay
      (fun a b z z' hs hu hs' hu' ↦ generatedIntersectionUnique b a z z' hu hs hu' hs')
  have stableLeafInjective (x y : OriginalTorusPullback q)
      (hxy : stableGenerated x y) (he : H x = H y) : x = y := by
    apply FranksOriginalCover.eq_of_proper_equivariant_leaf_decay
      (FranksOriginalCover.rectangularPlaqueRel liftedBox) closedStable H hproperH
      projectionOriginal integerDeck integerDeckImage integerDeckProjection stableDeck
      (fun z ↦ crossing (z.2,z.1)) (crossing.continuous.comp continuous_swap)
      (fun a b ↦ (hcrossing b a).2) ?_
      F.symm f.toHomeomorph.toEquiv hFback stableBackward backwardEqualImage
      stableDiagonalDecay stableGeneratorDecay ?_ hxy he
    · intro a b hab
      exact generatedIntersectionUnique b a _ b (hcrossing b a).1 (hcrossing b a).2
        (unstableGenerated.refl b) hab
    · intro a b hab hp
      exact stableProjectionInj a (stableRelation.refl a) (generatedStableNative hab) hp
  have unstableLeafInjective (x y : OriginalTorusPullback q)
      (hxy : unstableGenerated x y) (he : H x = H y) : x = y := by
    apply FranksOriginalCover.eq_of_proper_equivariant_leaf_decay
      (FranksOriginalCover.rectangularPlaqueRel (fun i w ↦ liftedBox i (w.2,w.1)))
      closedUnstable H hproperH projectionOriginal integerDeck integerDeckImage
      integerDeckProjection unstableDeck crossing crossing.continuous
      (fun a b ↦ (hcrossing a b).1) ?_
      F f.symm.toHomeomorph.toEquiv hF unstableForward forwardEqualImage
      unstableDiagonalDecay unstableGeneratorDecay ?_ hxy he
    · intro a b hab
      exact generatedIntersectionUnique a b _ b (hcrossing a b).1 (hcrossing a b).2
        hab (stableGenerated.refl b)
    · intro a b hab hp
      exact unstableProjectionInj a (unstableRelation.refl a) (generatedUnstableNative hab) hp
  have hHinjective : Function.Injective H :=
    FranksOriginalCover.injective_of_global_product_and_leaf_injectivity
      unstableGenerated stableGenerated H globalProduct _ _ decayComplement.disjoint.symm
      (fun x y h ↦ (unstableRelationImage x y (generatedUnstableNative h)).1)
      (fun x y h ↦ (stableRelationImage x y (generatedStableNative h)).1)
      unstableLeafInjective stableLeafInjective
  refine ⟨B,hB,k,?_,hksem,?_⟩
  · apply franks_native_downstairs_injective q u0 k H hHproj hHdeck
    exact hHinjective
  · exact bounded_coordinate_lift_of_pullback q u0 k H hHproj hHbound

/-- Franks–Manning conjugacy for a smooth manifold merely homeomorphic to a torus.

The atlas, diffeomorphism, tangent subbundles and smooth Riemannian tensor
belong to the original manifold `M`. The homeomorphism to the torus is only
topological. All derivative norms below use the one supplied tensor through
its `RiemannianBundle` instance; there is no model-space norm substituted on
an actual tangent fibre. Stable and unstable fibres may have rank zero.
The whole real model is boundaryless. Compactness, Hausdorffness and second
countability are the closed smooth manifold convention. No transitivity,
orientation, standard smooth structure, or smooth torus identification is
assumed. The conclusion uses the existing native `HyperbolicRealToralConjugacy`:
one matrix unit over `ℤ`, its actual complex eigenvalues, its coordinate action
on `UnitAddTorus (Fin n)`, and a genuine homeomorphism intertwining `f`.

Sources: Franks1969 §§1–2, pp.118–124; Franks1970 Proposition (2.1), pp.70–71,
Theorem (2.2), pp.71–74 and Lemma3.4, pp.75–76; Manning1974 Theorems A–C,
pp.423–429. The following is the complete natural-language proof relative to
its named lower providers in the DAG, retaining the original-cover application
rather than adding an infranil smooth structure to the hypotheses.

1. Canonical product covering and its integer deck lattice
Write E=Fin n→R and T^n=Fin n→UnitAddCircle exactly as in topo.def_real_torus, and let p0(v)(i) be
the quotient class of v(i) modulo zmultiples(1). Use discreteness of zmultiples(1) and
AddCircle.isAddQuotientCoveringMap_coe for each coordinate; independently the quotient projection is
an open quotient map, and IsOpenQuotientMap.piMap gives this for p0. Let D=Fin n→zmultiples(1),
acting by coordinate translation on E. Its translations are continuous; coordinate fibre equality is
exactly membership in the same D-orbit. At each v choose the coordinate disjoint-translate
neighborhoods U_i provided by the circle covering. The finite product U is a neighborhood of v; if
(g+U)∩U is nonempty, every coordinate disjointness property gives g_i=0, hence g=0. These are
precisely the quotient-map, continuous-translation, orbit-fibre and disjoint-neighborhood fields of
IsAddQuotientCoveringMap p0 D. Apply its isCoveringMap theorem. Coordinate membership in
zmultiples(1) supplies an integer z_i, and Int.cast_injective supplies uniqueness; thus D is exactly
the faithful Z^n translation lattice, not an assumed quotient identification. In n=0 all products
are singletons, U is the singleton and D is trivial, so the same construction applies.

2. Actual pullback universal cover with its existing topology
Choose the given topological homeomorphism q:M→T^n. Give P={(x,v)∈M×E:q(x)=p0(v)} the
product-subtype topology; set p(x,v)=x and Q(x,v)=v. The continuous inverse v↦(q^−1(p0(v)),v) proves
Q:P≅E topologically, directly using the defining equality. If p0^−1(O) is the disjoint union of open
sheets W_α with inverse branches s_α:O→W_α, then p^−1(q^−1(O)) is the disjoint union of the open
subsets P_α={(x,v)∈P:v∈W_α}. On each P_α, p is a homeomorphism to q^−1(O), with continuous inverse
x↦(x,s_α(q(x))). These formulas, their inverse identities and the disjoint covering of each fibre
construct IsCoveringMap p on the existing topology; surjectivity follows from that of p0. No generic
pullback-cover theorem or identification with an unconstructed lattice quotient is assumed. Real
vector-space contractibility, simply-connectedness and local path-connectedness transfer through Q
to P. For z∈Z^n, δ_z(x,v)=(x,v+z) is a continuous deck homeomorphism with inverse δ_−z. Every
continuous deck transformation equals exactly one δ_z: choose u0, identify its image in the fibre by
the preceding integer-lattice calculation, and apply pointed continuous-lift uniqueness on connected
P. Q also supplies Hausdorffness and second countability from E, but supplies no differentiability.

3. Original real pullback atlas and its guarded smooth transitions
Follow the written covering-chart construction of Lee2003 Proposition2.12, printed pp42–43, on the
actual topological covering p:P→M. The base M is connected by hypothesis and the total space P is
connected, Hausdorff and second countable through the already constructed topological Q:P≅E; thus
the source's connected-cover setting is satisfied without repeating its countable-fibre argument or
putting a new topology on P. Given u∈P, choose an evenly covered neighborhood O of p(u) and its
sheet W containing u, and shrink O inside an original real chart domain O_φ. In unrestricted atlas
notation this is the restriction W∩p⁻¹(O_φ), with chart c=φ∘p, open target φ(O∩O_φ) and inverse
s_W∘φ⁻¹. These are Lee's sheet charts. The actual OpenPartialHomeomorph.trans fields retain both
these restrictions and their inverse identities. Take all such sheet charts as the atlas and at each
u choose one containing u; atlas, chartAt, mem_chart_source and chart_mem_atlas thereby define
ChartedSpace on the existing product-subtype topology. Lee's printed transition calculation now
applies on c_i(W_i∩W_j): c_j∘c_i⁻¹=(φ_j∘p)∘(p|_(W_i∩W_j))⁻¹∘φ_i⁻¹=φ_j∘φ_i⁻¹ on that guarded overlap.
The original smooth atlas of M makes both ordered restricted transitions C∞. With
I=modelWithCornersSelf R E, its model maps are identities and range I=E, so isManifold_of_contDiffOn
applies on exactly those open transition sources and gives IsManifold I ∞ P. In matching sheet/base
coordinates p and s_W have identity coordinate expression. Their already proved intrinsic continuity
and the maximal-atlas point test, with source membership for both charts, therefore make them smooth
local inverses. This establishes the covering smooth structure by the source's sheet-chart and
transition-cancellation proof, with the existing Mathlib guard packaging explicit. The source
expressly leaves uniqueness to Problem2-7; uniqueness is not proved by this step. q and Q are used
only topologically, including in dimension0 where the charts and covering are singleton charts.

4. Uniqueness of the maximal original covering atlas
Follow the actual real-atlas proof of Lee2003 Lemma1.10(a), printed p14/PDF30. Let A be all the
original covering-sheet charts constructed in Step3 on the existing topology of P, and define Abar
to be all real n-dimensional topological charts smoothly compatible with every chart in A. The Step3
transitions make A a smooth atlas, so A is contained in Abar and its domains cover P. To prove Abar
itself is smooth, take charts (U,phi),(V,psi) in Abar and a point u in U∩V. Choose (W,theta) in A
with u in W. On the actual open neighborhood phi(U∩V∩W) of phi(u), the transition factors as
psi∘phi⁻¹=(psi∘theta⁻¹)∘(theta∘phi⁻¹). The first factor is smooth on theta(V∩W), the second on
phi(U∩W), and on this smaller neighborhood the second sends into theta(V∩W). These are exactly the
source's triple-chart overlap guards; compatibility with theta proves both factors smooth, and
guarded composition proves the transition smooth near phi(u). Interchanging phi and psi supplies its
smooth inverse. Empty overlaps require no test. Thus all ordered transitions are smooth pointwise on
their open domains, as in Lee's written proof, and Abar is a smooth atlas. A chart compatible with
every chart of Abar is in particular compatible with every chart of A, hence is already in Abar;
this proves maximality by the source's argument. Now let B be any other maximal real smooth atlas on
the SAME topology of P for which p:P→M is a local diffeomorphism to the ORIGINAL smooth M. For a
sheet chart c=φ∘p on W, p and the original φ are locally smooth in B. At each u in W, shrink its
local-diffeomorphism neighborhood inside W and shrink its base neighborhood inside the original φ
domain and p(W). The resulting smooth local inverse of p equals the previously constructed sheet
inverse s_W there, because both are inverses of the injective restriction p|W. Consequently c and
c⁻¹=s_W∘φ⁻¹ are locally smooth on exactly their original chart source and target, with these
receiving-domain restrictions; the maximal-atlas point test and ContMDiffOn.comp give their
ContMDiffOn certificates on those sets. OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn then
puts c in B. Hence A⊆B. The final paragraph of Lemma1.10(a)'s written proof now applies literally:
every chart of B is compatible with A, so B⊆Abar; since Abar is a smooth atlas and B is maximal,
B=Abar. This proves uniqueness of the maximal original covering atlas. It asserts equality of
maximal atlases, not equality of selected chartAt data. Dimension0 uses the same
singleton-coordinate transition argument. Only Lemma1.10(a) is used: part(b) is Exercise1.4 and the
covering-uniqueness Problem2-7 is not used as a proof. Neither q nor Q is differentiated, and no
standard smooth E atlas is transported to P.

5. Paired continuous lifts give original smooth dynamics and smooth decks
Use the continuous lifting theorem already named here to choose F lifting f∘p with F(u0)=v0 over
f(p(u0)), and G lifting f⁻¹∘p with G(v0)=u0. The connected simply connected locally path-connected P
and the actual covering p meet that theorem's hypotheses. GF and id are continuous lifts of p
agreeing at u0, and FG and id agree at v0; its pointed uniqueness gives GF=FG=id. Thus F is a
homeomorphism with inverse G. For smoothness follow the local-section argument actually written in
Lee2003 Lemma2.10 pp41–42 and the proof of Theorem2.13 p44: the inverse of an evenly covered smooth
sheet is a smooth local section, and a continuous lift is locally that section composed with its
smooth base map. Specifically, choose the target sheet W containing F(u), with projection onto O,
and its smooth local section s_W:O→W from the preceding sheet-chart step. Continuity of F supplies
an open source neighborhood V of u with F(V)⊆W. On V the covering identity and the sheet inverse
give F=s_W∘f∘p, and f∘p sends V into O. ContMDiffOn.comp applies with exactly that receiving-domain
guard; local-to-global smoothness proves F smooth. Apply the same written mechanism to G, which is
already its continuous inverse, giving a smooth diffeomorphism. Any lift of a positive iterate has
the same paired-inverse construction and local-section proof. For each continuous deck homeomorphism
δ and δ⁻¹ use receiving sheets and continuity in the same way: locally δ=s_W∘p and δ⁻¹=s_W′∘p, so
both are smooth. Only after this regularity argument differentiate the smooth projection identities.
Lee Theorem2.13 is a theorem about the universal covering of a Lie group; only its printed
local-section composition argument is specialized here, and neither M nor P is asserted to be a Lie
group. Proposition2.11 is an out-of-base smoothness criterion and is not cited as a generic lifting
theorem. No equality of discontinuous lifts and no differentiation of QFQ⁻¹ is used; the singleton
case has the same local identities.

6. Pullback tangent tensor and lifted Anosov estimates
Follow Gallier–Quaintance, author revision October9,2025, Proposition18.5 and its written proof
printed pp534–535. For the smooth covering p:P→M and the original Riemannian metric g, define its
pullback by gtilde_u(v,w)=g_(p(u))(Dp_u v,Dp_u w). In the notation J_u=Dp_u, the smooth inverse
sheet and mfderiv_comp/id make J_u a continuous linear equivalence, with inverse the derivative of
that sheet. As in the printed proof, the pullback is an inner product because J_u is a linear
isomorphism: the form is continuous bilinear and symmetric, and positivity follows for each nonzero
v from J_u v≠0. The formula makes Dp_u isometric, hence p a Riemannian local isometry. The source's
uniqueness calculation is also explicit: any metric making p a local isometry must evaluate on v,w
by exactly this displayed formula, so must equal gtilde. Retain the actual Mathlib metric structure
guards: the gtilde-unit ball is J_u⁻¹ applied to the original g-unit ball, which is von Neumann
bounded by the given Riemannian data; the continuous linear inverse preserves boundedness. This
supplies compatibility with the original tangent-fibre topology. In matching covering/base tangent
trivializations, p has coordinate identity, so gtilde's bilinear-section coefficients are the
original smooth coefficients of g composed with that local identity. This supplies the smooth
section field of Bundle.ContMDiffRiemannianMetric on its actual source guards. These are structure
bindings for the printed tensor construction, not an existence theorem for arbitrary metrics.
Preserve separately the existing Anosov transport calculation: define the lifted stable and unstable
subbundles by J_u⁻¹(E^s_(p(u))) and J_u⁻¹(E^u_(p(u))); these are continuous and complementary.
Differentiating pF^k=f^k p gives J_(F^k u)D(F^k)_u=D(f^k)_(p(u))J_u, so invariance and the exact
original Cλ^k estimates follow in the gtilde norms, including inverse time. For a deck δ,
differentiating pδ=p gives J_(δu)Dδ_u=J_u, and therefore gtilde_(δu)(Dδ v,Dδ w)=gtilde_u(v,w). These
chain-rule Anosov/deck calculations are retained guarded supplements, rather than a claim that
Proposition18.5 prints an Anosov transport theorem. Rank0 has the unique bilinear form and the same
inverse-sheet identities.

7. Genuine lifted path distance and deck isometries
Select Petersen third-edition author text §5.3 p146's distance FROM THE OUTSET, on the original
smooth M with its given tensor g and the original covering-sheet smooth P with the pullback tensor
gtilde of unchanged Step6. For endpoints a,b, W_(a,b) consists of continuous curves on [0,1] with a
finite subdivision into smooth segments and these endpoints. Set L_g(c)=Σ∫||c′||_g over the pieces
and d_g(a,b)=inf{L_g(c):c∈W_(a,b)}, and similarly d_gtilde. Smooth segments have the usual
open-interval extensions in their original charts. This is the SOURCE piecewise-smooth metric from
the SAME tensor, not a norm transported through topological q/Q or the old ambient C1
Riemannian-EDist instance. No equality of those infima is asserted or needed.

Use the FULL written reachability proof of Lee2003 Lemma6.17 pp139–140 for finite admissible paths.
For a fixed a, the set E of points reached by finite piecewise-smooth paths contains a. At b∈E
append straight coordinate segments in a smooth coordinate ball, making E open. At b in its closure
choose a point of E in that coordinate ball and append the segment to b; hence E is closed.
Connectedness gives E the whole original M or P. Each smooth segment has bounded continuous speed on
its compact interval, so its length and the finite sum are finite. Constants, reversal and finite
concatenation give zero diagonal, symmetry and the triangle inequality for the source infimum, as in
Petersen p146 and Lee11.20. In dimension0 the connected carriers are singletons and only the
constant-path case is needed.

Retain G2's independently reviewed LOCAL Lee11.19/11.20 mathematical mechanism, now with its final
distance bound coming from the source definition:
Work separately on M with g and on P with the original gtilde, in one ORIGINAL smooth chart χ:O→V⊂ℝⁿ
centered at a point p with χ(p)=0. Shrink a Euclidean coordinate ball so the compact
K=closedBall(0,r), r>0, is strictly contained in the OPEN original chart image V. The pulled-back
coordinate metric defines N(z,v)=||Dχ⁻¹_z(v)||_g (respectively with gtilde). Its continuity and norm
homogeneity come from that same tensor and smooth inverse chart; agreement with the norms of the
ORIGINAL smooth tensor remains the explicit tangent-coordinate realization guard; the source length
below is defined from these very norms.
For n>0 follow the upper-bound part of the literal Lemma11.19 proof: under the canonical
tangent-coordinate identification the unit-vector locus is K×Sⁿ⁻¹, compact by the existing Euclidean
finite-dimensional properness, closed-ball/product compactness and mathlib.isCompact_sphere. The
continuous real function N is bounded above there by mathlib.isCompact_bddAbove_image; enlarge its
finite bound to C>0. For any nonzero v, v/|v| is on the Euclidean unit sphere, so homogeneity gives
N(z,v)=|v|N(z,v/|v|)≤C|v| for every z∈K. The same bound holds directly for v=0. Only this upper half
of Lee's two-sided norm estimate is needed for local finiteness; no lower norm or global metric
comparison is inferred.
For q with a=χ(q) and |a|<r/2 take the literal affine coordinate segment α(t)=(1−t)0+t a, 0≤t≤1. The
existing mathlib.affine_lineMap_contDiff over ℝ supplies its all-order smoothness; the SAME formula
extends to the open interval (−1/2,3/2), whose image remains in K⊂V because |t a|<3r/4 there.
Composition with χ⁻¹ through the existing contMDiffOn_comp therefore makes γ(t)=χ⁻¹(α(t)) an actual
smooth curve on an open interval containing [0,1], hence an admissible smooth segment for the SOURCE
piecewise-C∞ length definition (and a C¹ segment for the retained length-integral API), with γ(0)=p
and γ(1)=q. The existing mathlib.affine_lineMap_hasDerivAt gives α′(t)=a, and mfderiv_comp gives
γ′(t)=Dχ⁻¹_(t a)(a). Consequently the SOURCE norm-integral integrand, also represented by
pathELength_eq_lintegral_mfderiv_Ioo on each smooth segment with these same installed norms, is N(t
a,a)≤C|a|. Lee's written straight-segment integral calculation yields L_g(γ)≤C|a|<∞, with the same
norm-integral on each smooth segment; the DEFINITION of the selected piecewise-smooth distance gives
d(p,q)≤L_g(γ)<∞. This last inequality is a source infimum inequality, not an assertion about Mathlib
riemannianEDist. This uses ≤C|χ(q)−χ(p)|, not the printed final Cε equality. If n=0 the Euclidean
unit sphere is empty, so no sphere bound or normalization is applied: the original coordinate
neighborhood is a singleton and its constant smooth path has derivative and length0.

For separation/topology write Petersen5.3.8 pp148–150 and the full Lee11.19/11.20
coordinate/first-exit proof. Choose an original coordinate ball with a protected closed larger ball
strictly inside its chart. On this compact core×Euclidean unit sphere the SAME positive norm N has a
positive minimum and finite maximum, giving 0<c≤C and c|v|≤N(z,v)≤C|v| by homogeneity. The upper
half is the retained G2 component; positivity and the compact-minimum leaf give the lower half.
Rank0 uses singleton charts, not an empty unit sphere. For b in the smaller coordinate ball the
straight segment gives d_g(a,b)≤C|χ(b)−χ(a)|. A piecewise-smooth competitor staying in the protected
ball has length at least c times its Euclidean endpoint displacement; a competitor leaving it has a
first exit on its radius-r boundary and prefix length at least cr. These follow by integrating the
SAME norm inequality on each smooth piece and summing. Thus d_g(a,b)≥c|χ(b)−χ(a)| on the smaller
ball and d_g(a,b)≥cr for endpoints outside the protected ball. Separation follows; the latter bound
puts sufficiently small d_g balls in any prescribed original neighborhood, while the
straight-segment upper bound gives the reverse topology inclusion. This constructs a finite ordinary
metric with EXACTLY the preexisting topology, independently on M, P and the smooth finite cover of
Step10. It does not obtain a lower bound from an unbound C1 ambient EDist.

Package precisely these two real distances into native metric instances by the literal existing
mathlib.metric_space_of_dist_topology_g10, MetricSpace.ofDistTopology at the pinned Mathlib
MetricSpace/Defs.lean83–89. The carriers are the ORIGINAL M and P with their GIVEN
smooth-manifold/covering-sheet topologies; dist is respectively the already defined d_g and
d_gtilde. Feed the zero-diagonal, symmetry, triangle and zero-distance separation laws just proved
from their nonempty finite piecewise-smooth path families. Bind the constructor's exact H for EVERY
S in each carrier: if S is original-open and x∈S, choose the protected original coordinate ball
centered at x with its closed larger chart ball contained in S. The preceding first-exit lower bound
c r>0 shows that d(x,y)<c r forces y∈S. Conversely, suppose every x∈S has ε>0 with d(x,y)<ε implying
y∈S. At this fixed x use the preceding radial upper bound C>0 and choose a positive coordinate
radius δ<min(r/2,ε/C). Its ORIGINAL-open inverse-chart neighborhood consists of y with
d(x,y)≤C|χ(y)−χ(x)|<ε, hence is contained in S. Thus S is original-open by the open-set neighborhood
definition. This proves the literal open/positive-distance-ball equivalence without presupposing
metric openness. In dimension0 the connected carriers are singletons; the constant distance and
singleton original topology satisfy H and separation directly, without a unit sphere. The written
constructor stores dist:=d and replaces its derived uniform-space topology by this exact GIVEN
topology using H; its separation field yields the MetricSpace. The distance and original topology
are definitionally unchanged. Its uniformity and Bornology are the ones DERIVED from this d, not a
claim that arbitrary former uniform/bornological structures are preserved. This application supplies
metric-instance packaging for d_g and d_gtilde only; it neither identifies a C1/EDist path infimum
nor closes their separate tensor/norm/integral realization guards.

Projection/deck laws use Petersen5.6.1 p163's printed local-isometry mechanism on these SOURCE
paths. Step6's derivative identity makes L_g(p∘c)=L_gtilde(c) on every finite smooth family, so
infima give d_g(pu,pv)≤d_gtilde(u,v). Smooth decks and their smooth inverses from Step5 preserve the
SAME pullback tensor. They biject these ambient piecewise-smooth path families without changing
lengths, hence d_gtilde(δu,δv)=d_gtilde(u,v). This is the bijective local-isometry case of the
source proof; no properness or finite-sheet hypothesis is used. The retained pathELength
norm-integral and additivity leaves represent lengths on genuinely smooth, thus C1, segments only;
they do not identify ambient infimum metrics. Intrinsic piecewise-C1 d_L remains the separate object
of topo.franks_intrinsic_leaf_metric_bounds_g8. Neither its completeness nor a different path-class
equality is inferred. Exact tensor/norm/integral realization remains later formalization work; the
just-bound metric constructor packages only the SAME source distance and GIVEN topology and gives no
permission to instantiate a theorem for a different distance.

8. Completeness of the source-selected original lifted Riemannian metric
Use ONLY the SOURCE piecewise-smooth metrics d_g,d_gtilde just selected, their original topologies,
and the unchanged Step6 smooth pullback tensor/local isometry. Write the actual Petersen
geodesic/Hopf–Rinow route; the old C1 short-path/single-sheet Cauchy proof is superseded. Dimension0
gives singleton connected M,P and immediate zero-distance completeness. Below assume positive
dimension.

Geodesic IVP/escape (Petersen5.2 pp141–142). The named SAME-g Levi-Civita, spray and local-flow
providers give unique smooth geodesics and locally uniform time intervals. Local addition gives the
genuine smooth exponential and its zero differential, without prescribing a metric distance.
Equal-data geodesics agree on overlapping intervals: the equal-data locus is closed by continuity
and open by local IVP uniqueness. Their union gives the maximal interval. Finitely many local-flow
neighborhoods on a compact tangent-state set give a common positive existence time. Metric
compatibility yields constant speed by d/dt g(c′,c′)=2g(∇_t c′,c′)=0. If a maximal c:(a,b)→M with b
finite returned at t_j→b to compact K, its tangent states would stay in a compact subset of TM:
cover K by finitely many original tangent trivializations on compact base cores; the SAME tensor
coordinate lower bounds of Lee11.19 bound coordinate velocities by the constant speed. Finite unions
of compact base-core×closed-velocity-ball images give the required compact tangent set. The common
existence time extends c from a sufficiently late t_j beyond b, contradicting maximality. This is
Petersen's WRITTEN compact-tangent escape proof, on the original smooth tensor/bundle.

Local minimizing segments (Petersen5.5.4–5.5.5 pp158–159 and5.5.6 p160). Use the named
metric-agnostic exponential/local-addition and SAME-g Gauss lemma. Shrink a smooth normal chart;
EVERY protected closed tangent ball used below has radius strictly smaller than its open chart
radius. Its exponential image is compact/closed, with boundary identified by the inverse chart, so a
leaving curve has a first exit on its radius boundary. The radial path exp_p(tv) has constant speed
||v||_g. At positive inverse radius r the Gauss identity gives dr(w)=g(∂r,w), ||∂r||=1, so
|dr(c′)|≤||c′||_g. Integrate on every smooth competing piece and sum to bound length below by radial
change. At center visits use a positive-radius subinterval and pass to its endpoint limit instead of
applying polar coordinates at0. A curve exiting the protected radius-R ball has a prefix of
length≥R; the radial curve to r<R has length r. Hence on each strictly smaller normal ball SOURCE
distance equals inverse radial norm and exponential images equal open/closed SOURCE metric balls.
Equality forces positive radial motion, making the short radial segment unique up to
reparametrization. This is the source radial/escaping-path proof for piecewise-smooth competitors,
not the C1-EDist Andrews normal-ball theorem. The compact normal spheres/balls below always lie
STRICTLY inside the original normal chart.

No corners (Petersen5.4.2–5.4.4 pp152–154). For a finite smooth variation differentiate
E=(1/2)Σ∫g(c′,c′). Metric compatibility and torsion freeness give the integrand g(∇_t V,c′).
Integration by parts on the pieces gives −∫g(V,∇_t c′), the two endpoint terms, and Σg(c′_−−c′_+,V)
at break times. Realize V by the local exponential along the compact finite curve; finitely many
source domains give a common small variation time. With fixed endpoints this is a proper variation.
A constant-speed length-minimizing segment minimizes energy by L²≤2TE and therefore has vanishing
first variation. The printed choice of V as a positive cutoff times ∇_t c′, zero at
endpoints/breaks, forces acceleration0 on each piece. Next choose V at each break equal to
c′_−−c′_+; the corner formula forces Σ||c′_−−c′_+||²=0. Thus velocities match, and IVP uniqueness
makes the broken geodesic one smooth geodesic. In the Hopf–Rinow application the pieces are already
geodesics, so only this explicit corner sum is needed. This writes the human
first-variation/no-corner argument, rather than assuming a minimizing concatenation is smooth.

Compact base → metric complete → geodesic complete (Petersen5.3.9 p150 and5.7.1 direction(4)→(1),
p177). Step7 gives the original compact topology for this VERY metric uniformity; the existing
compact-uniform completeness leaf makes the base metric complete. If a maximal base geodesic ended
at finite b, the source distance between c(s),c(t) would be at most its smooth subsegment length
||c′||·|t−s|. Thus t_j→b gives a Cauchy sequence converging by completeness. The same inequality
makes the whole tail converge to that limit. It eventually lies in a relatively compact original
chart neighborhood; adjoining a preceding compact curve segment confines the finite-endpoint tail to
a compact base set. The written compact-tangent escape argument above contradicts maximality.
Reverse time excludes finite a. All base geodesics therefore exist on R. No C1 ambient-distance
equality is used.

All-time covering lift (Petersen5.6.1 p163 and FULL5.6.3 proof p164). For upstairs data(u,w), take
the all-time base geodesic with data(pu,Dp_u w). Lift it on ALL R through the actual covering p with
value u at0. The existing pointed covering-lift theorem applies because R is contractible/simply
connected and locally path connected. On each receiving sheet the lift is the smooth inverse local
isometry composed with the base geodesic, as in the source and unchanged Step5 local-section
mechanism. Local isometries preserve geodesics because their matching coordinate metric coefficients
and first derivatives, hence the geodesic equations, coincide. The lift has initial derivative w
since the inverse-sheet derivative is inverse to Dp_u. IVP uniqueness identifies this all-time lift
with the maximal upstairs geodesic of those data. Thus P is geodesically complete; no properness,
finite-sheet or standard smooth-torus assumption enters.

Geodesic complete → Heine–Borel (actual5.7.1 direction(2)→(3), pp177–178). Fix p∈P. The case q=p
uses the constant segment. For q≠p let d=d_gtilde(p,q)>0 and choose 0<ε<d STRICTLY below a normal
chart radius (and shrink with an outer protected-radius buffer). The SOURCE closed ε-ball and
ε-sphere are compact exponential images of closed tangent balls/spheres inside that chart. Choose p0
on the sphere minimizing distance to q. Then d=ε+d(p0,q): triangle gives ≥d; if ε+d(p0,q)>d, a
regular unit-speed SOURCE curve with length below that sum first crosses the ε-sphere, contradicting
p0's minimality. The needed strict-slack regular competitor is Petersen5.3.10 p150's written
coordinate-polygonal proof: cover the original finite curve by finitely many sufficiently small
original coordinate cores where cL_E≤L_g≤CL_E and C/c<1+η. Approximate each portion by a regular
coordinate polygonal curve with no greater Euclidean length and sum to get L_g(new)≤(1+η)L_g(old);
use a sufficiently small η relative to the strict slack. Reparametrize by accumulated positive
length for unit speed. This stays within finite piecewise-SMOOTH curves and says nothing about
arbitrary C1 paths.

Extend the unit-speed radial geodesic from p through p0 to c:[0,∞)→P and set
A={t∈[0,d]:d=t+d(c(t),q)}. It contains0 andε and is closed by metric continuity. For a∈A, the
triangle inequalities and geodesic subsegment lengths show d(p,c(a))=a and [0,a]⊂A. For the
continuation argument restrict to a∈A with ε≤a<d, so the incoming c|[0,a] has positive length;
choose 0<δ<d−a STRICTLY inside a protected normal chart at c(a); choose q0 nearest q on its compact
δ-sphere. The same strict-slack competitor/first-crossing argument gives d(c(a),q)=δ+d(q0,q).
Consequently d=a+δ+d(q0,q)≤d(p,q0)+d(q0,q)≤a+δ+d(q0,q)=d. The concatenation of c|[0,a] and the short
radial segment c(a)→q0 has length a+δ=d(p,q0), so it is minimizing. The written no-corner argument
makes it one geodesic, and IVP uniqueness gives q0=c(a+δ). Thus a+δ∈A. Since ε∈A, sup A≥ε>0;
closedness puts sup A in A. If sup A<d, the continuation rule just proved for ε≤a<d extends beyond
that supremum, a contradiction. Thus the closed initial interval is A=[0,d] and c(d)=q. Every q is
reached by a minimizing geodesic.

For R≥0, closedBall_d(p,R)=exp_p(closedBall_gtilde(0,R)): radial paths give one inclusion and
minimizing segments the other, with initial vector norm equal to length. Geodesic completeness
defines exp_p on the whole tangent space; its smoothness near each finite trajectory follows from
smooth local flow dependence and finite subdivision into guarded local domains. Finite-dimensional
properness makes its closed tangent norm balls compact, so their exponential images are compact.
Every closed bounded set lies in such a compact ball and is closed there, hence compact.

Heine–Borel → metric complete (source direction(3)→(4)). A Cauchy sequence has bounded range: put a
tail within radius1 of one term and enlarge the radius for its finitely many preceding terms. The
compact closed ball just proved contains the sequence. The named compact subsequence theorem gives a
convergent subsequence; the Cauchy ε/2 estimate together with one sufficiently late subsequence term
gives convergence of the entire sequence to the same limit. The metric_complete_of_cauchySeq_tendsto
leaf yields completeness. The complete metric is the SAME gtilde SOURCE distance with the original P
topology. This component proves no completeness of intrinsic C1 leaf distances and does not close
original-smooth spectral/count/global-product/finite-μ gaps or the classification theorem.

9. The induced integral matrix and homotopy class
Use coordinate winding numbers to identify π1(T^n) with Z^n. The homeomorphism q and f induce an
automorphism A of Z^n, hence an integral matrix unit. Basepoint-path changes act by inner
automorphisms and have no effect because Z^n is abelian. The linear model Abar acts by this same A
on winding coordinates. Pull the finite cubical CW structure of T^n back along q^(−1), so the CW
hypothesis of Franks Proposition (2.1) does not assume a smooth triangulation or a standard smooth
atlas. Once a fixed point x0 has been obtained, translate q(x0) to 0; translation acts identically
on π1. Then q∘f and Abar∘q are based maps with equal induced π1 maps and are based homotopic by the
aspherical CW homotopy uniqueness theorem. The continuous based homotopy lifts through the already
constructed universal cover by the covering homotopy lift theorem; this topological lift adds no
smoothness claim.

10. Characteristic doubled cover in the canonical topological model
Define m2:T^n→T^n by coordinate doubling of quotient classes; it is well-defined because doubling
preserves the integer lattice. Its composite with p0 is v↦p0(2v), continuous, so quotient-map
continuity proves m2 continuous. Around any point choose an open p0-sheet U in E, with p0|U a
homeomorphism onto the open O=p0(U); shrink within a disjoint-integer-translate neighborhood if
necessary. The preimage m2^−1(O) is the union of the 2^n open sets V_r=p0((U+r)/2), r∈{0,1}^n, since
each integer vector decomposes uniquely as 2k+r and p0(w−k)=p0(w). They are pairwise disjoint: if
p0(w)=p0(w′), write w−w′=k∈Z^n; writing 2w=u+r,2w′=u′+r′ with u,u′∈U gives u−u′=2k−r+r′.
Disjointness of integer translates of U forces u=u′, and the parity representatives force r=r′. On
V_r, m2 is a homeomorphism to O, with inverse t↦p0(((p0|U)^−1(t)+r)/2); the displayed expressions
prove continuity and both inverse identities. Thus this is an actual finite covering on the
canonical quotient-product topology, including the singleton n=0 case. Pull it back to
B={(x,t)∈M×T^n:q(x)=m2(t)}, with b(x,t)=x, using the same open-sheet formulas as for P. Its
projection to t is a homeomorphism B≅T^n, with inverse t↦(q^−1(m2(t)),t); hence B is compact and
connected. The universal real-coordinate cover above shows T^n, and therefore B, is path connected
(continuous surjective image of the path-connected E) and locally path connected (each point has a
local Euclidean covering sheet chart). In coordinate winding normalization, the loop γ with lifted
real path v has endpoint z; the loop m2∘γ has lifted path 2v with endpoint 2z. Hence m2 induces
multiplication by2 on π1 and the image of b_* in π1(M) is precisely 2Z^n under q_*. This calculation
uses the winding definition, not the integral-matrix-unit clause for the nonunit 2I. The
automorphism A preserves 2Z^n, so the pointed range-inclusion lifting criterion constructs a
continuous lift of f∘b and the matching inverse lift of f^−1∘b. Uniqueness for the connected locally
path-connected source B makes these lifts inverse just as for P. The general sheet-atlas/tensor
formulas already written above require only an actual covering, not simple-connectedness: applied to
b they give the original real smooth finite cover, smooth lifted dynamics and pullback metric.
Compactness makes this finite-cover path metric complete after its metric construction. Let
Q_B:B≃ₜT^n be the second-projection homeomorphism. For the lift f_B, write A_B for the winding
matrix of Q_B f_B Q_B⁻¹. The identities q b=m2 Q_B and b f_B=f b give 2A_B=A2 after taking winding
actions, since the explicit lifted-loop calculation above gives m2_* =2I. Cancel2 entrywise in the
torsion-free integer group to obtain A_B=A. At moved basepoints choose connecting paths on each
space; a different choice only conjugates the abelian winding group. Recentering by translations
acts identically on winding, and another lift differs by a half-lattice deck translation, also
acting identically. At the scope of the named winding/H1 naturality and rational cup/Kronecker
providers, the same coordinate action on rational H1 is 2I_Q and its inverse is (1/2)I_Q, so the
cover action has exactly A_Q, not merely an unspecified matrix with a hoped-for spectrum. This does
not prove those open homology/cochain providers.

11. Hyperbolicity through intrinsic orientation covers and periodic counts
Manning Theorem A, pp.424–426, can be pursued on M without differentiating q. Pull back the toral 2I
covering along q, endow it with the smooth covering atlas from M, and lift f because 2Z^n is
characteristic. Write b:M₂→M for this already constructed connected characteristic 2Z^n smooth
cover, and let E^u→M be the ORIGINAL continuous real expanding bundle of constant rank d. Apply the
current source-complete topo.real_vector_bundle_orientation_monodromy_g9 to this bundle. If d>0, let
π_u:O(E^u)→M be its native ordered-basis orientation covering and choose o₀ over the marked
basepoint. The actual path-transport definition and Hatcher AT Proposition1.31 printedp61 give
(π_u)_*π₁(O(E^u),o₀)=ker w: precisely the loops whose chosen orientation lift closes have
monodromy+1. The already established winding identification gives image b_*=2Z^n, and
w(2z)=w(z)^2=1. Therefore apply mathlib.covering_lifting_criterion, the written Hatcher1.33 pp61–62
pointed-lift construction, to the actual map b:M₂→M. Its connected smooth source is locally path
connected, and the subgroup inclusion just checked gives a continuous o₂:M₂→O(E^u) with π_u∘o₂=b. In
the literal Hatcher VBKT Proposition1.5 pp18–19 product-subspace pullback b*E^u={(y,v):b(y)=π_E(v)},
the original independent local sections s_j pull back to (y,s_j(b(y))) and their transition matrices
are A_ij(b(y)). The supplier's native section/oriented-local-frame equivalence thus makes o₂ a
continuous orientation of THIS pullback bundle. In the original smooth covering charts, Db_y
identifies the actual lifted expanding bundle with b*E^u, with local frames (Db_y)⁻¹s_j(b(y)); these
are continuous independent frames, not asserted smooth sections of E^u. For each lifted iterate
f₂^m, the covering equation b∘f₂^m=f^m∘b and mathlib.mfderiv_comp give Db_(f₂^m
y)∘D(f₂^m)_y=D(f^m)_(b(y))∘Db_y. Original invariance and the inverse derivative therefore give a
continuous fibre-linear isomorphism of this actual continuous lifted bundle covering the continuous
map f₂^m. The supplier's comparison-sign theorem makes its orientation sign ε_m constant on
connected M₂. Hatcher VBKT Lemma1.1 p8 supplies the local inverse-matrix continuity behind the
pullback fibre-isomorphism identification; no monodromy-naturality theorem or tangent-manifold
orientation is assumed. If d=0, use the canonical empty-basis orientation and sign+1 directly,
without a two-sheet orientation carrier.  The explicit winding calculation in the preceding step
gives the lifted integer matrix A_B=A. Relative to the named winding/H1 and rational cup/Kronecker
providers, b_* is 2I_Q in the coordinate bases, with inverse(1/2)I_Q, so the induced rational action
has exactly A_Q. Apply dynamics.smale_original_anosov_spectral_basins_g7 to this original smooth
lifted Anosov diffeomorphism: its compact connected source and splitting satisfy that theorem
without a standard smooth atlas or transitivity assumption. This supplies finite locally maximal
transitive hyperbolic basic sets relative to that named open geometric source theorem. Apply
topo.original_torus_lefschetz_determinant_g7 to the topological homeomorphism q and the original
smooth continuous f (and separately to its characteristic orientation cover). It proves
L(f^m)=det_Q(I−A_Q^m) from ordinary rational homology; it is conditional on its named rational
cup-basis/Kronecker and winding/H1 prerequisites, not on any smooth atlas transported by q. To apply
the ENR sum theorem explicitly, identify each UnitAddCircle with Circle by
AddCircle.homeomorphCircle at period1. Embed the product in R^(2n) as the product of unit circles;
on the open product annulus {v_i:1/2<‖v_i‖<3/2} retract coordinatewise by v_i↦v_i/‖v_i‖. Compose
this continuous section/retraction with q/q⁻¹. These give an actual finite-dimensional Euclidean ENR
representation of M and of the orientation cover. The determinant theorem gives the finite rational
homology bounds. Each fixed set is closed in compact M and every fixed point is isolated by the
original smooth Anosov derivative calculation below, so compact-discrete finiteness applies. Apply
the current source-replaced topo.compact_enr_lefschetz_local_index_sum_g7. It follows Dold1965
Theorem4.1/Lemma4.2 pp5–6 and the written six reductions in §5 pp6–8, with its two exact named
foundations topo.rational_relative_homology_cross_product_kunneth_g7 and
topo.finite_cubical_skeleton_homology_neighborhoods_g7, both now complete one level. The
rational-product proof identifies the literal one-relative-factor quotient by the natural
exact-sequence/five-lemma argument, treats H0 by its actual cokernel, applies the field chain-tensor
theorem and retains the Koszul flip and diagonal coherence. Its Eilenberg–Zilber and field
chain-tensor providers are also complete one level. Barr Proposition5.5 p116 now supplies the three
formerly omitted natural uniqueness cases via
topo.singular_acyclic_models_remaining_uniqueness_cases_g2, with one global common universe and
canonical lifted-Q coefficient transport, model representability, augmented-Hom exactness and the
degree-zero start verified. The signed-shuffle provider topo.singular_signed_shuffle_chain_map_g2 is
reviewed SOURCE/split/proof-complete at its OWN ONE LEVEL using the supplied Eilenberg–Mac Lane1953
original, §5 Theorem5.2 (5.8) pp66–67, with §§2–3/§5 definitions and recursive proof. Its
unnormalized-grid sign, diagonal free-singular carrier and rational extension are accounted for;
this does not certify transitive homology, native/spectral/global/classification, Lean or
full-target closure. Other named lower homology obligations remain separate. The finite-cubical
proof supplies the actual finite-cell singular/cellular comparison, skeleton surjections and
boundary generators, and nested open deformation retracts/radial boundary collars, relative to its
own named lower providers. In Dold4.1 take the compact containing set to be the entire original
compact ENR M (and then the entire compact orientation cover), so its homology endomorphism is the
ordinary rational f_*. No Leray quotient or standalone normalization(VII) is used. Thus L(f^m)
equals the rational cast of the finite integer local-index sum; on this orientation cover the local
smooth calculation below gives every hyperbolic fixed point of an iterate the sign (−1)^d ε_m, with
d=rank E^u and ε_m the constant derivative orientation sign. The named G9 basic index provider
supplies the stated restriction/additivity/common-support homotopy conclusions; Dold1.8/2.3 below
supplies ENR independence using that provider’s completed D6a–D6d integral product proof, including
arbitrary compact supports, positive product orientation and the ordinary H0 point unit; the
published Dold global trace deduction uses these completed one-level rational-product and
finite-cubical foundations relative to their precise lower prerequisites; with the common nonzero
local sign the sum theorem gives N_m=|L(f^m)|. Apply
dynamics.manning_original_basic_set_signed_trace_g7 to each locally maximal transitive hyperbolic
basic set of this same original smooth lifted Anosov map. Its Cλ bounds can enlarge C to max(C,1).
Its statement gives the concrete finite ordered-disjoint related-set zero-one matrices and N_m as
their signed trace sum, now supplied by its complete one-level source proof using de Jong’s
common-image-first construction before Manning’s periodic-fibre no-cross and complement
cancellation. Its one guarded joint Bowen witness (N,D,R,T,π), chosen after original-distance
expansivity, supplies finite fibres, every label at every integer coordinate and periodic-coordinate
rigidity for exactly that coding map. Its current Fact1 and joint Bowen coding suppliers are
SOURCE/split/proof-complete at their OWN ONE LEVEL, with their named lower prerequisites remaining
independent and no unrelated connected original-partition inference; no arbitrary-given-partition
fibre variant or global transient matching uniqueness is assumed. Fibre permutations must be
retained and a period-m source point is not presumed to have a period-m ordinary code. All
correction matrix words project to the relative partition frontiers with a uniform per-point
multiplicity bound; the strict boundary rate remains separate. CENTRAL ORIGINAL-MAP SOURCE
APPLICATION, conditional on the named original-smooth spectral, index and homology inputs above.
(C1: common return before primitivity.) Apply the WRITTEN Shub1987 Theorem8.13 pp106–107 cyclic
decomposition to the original characteristic-cover map f_B, not to a standard-smooth torus map. For
a periodic p its unstable closure X_p is relatively open and closed in Ω, and two such closures are
equal or disjoint by the local-product/periodic approximation argument. Compactness leaves finitely
many, which f_B permutes. Take one positive common multiple N of all permutation-cycle lengths. Shub
p107 proves mixing for ANY return N preserving X_p: for nonempty open U,V in X_p choose periodic
p₁∈V of period k for f_B^N; for each residue i=0,…,k−1 choose z_i∈U∩W^u(f_B^{iN}p₁). Backward
iterates F^{-kℓ}z_i approach F^i p₁. Applying the fixed continuous map F^{-i} gives
F^{-(kℓ+i)}z_i→p₁∈V. Choose one threshold for the finitely many residues and write every large time
t=kℓ+i; then F^{-t}z_i∈V while z_i∈U, so (f_B^N)^t(V) meets U. Since U,V were arbitrary, exchanging
their names proves mixing in the usual ordered formulation. This is actual mixing, not
transitivity⇒primitivity. Put F=f_B^N on the ORIGINAL smooth cover. Its splitting satisfies C(λ^N)^j
at all j≥0, with the same original norm. Per(F)=Per(f_B), since F-periodicity implies
f_B-periodicity and an f_B-periodic point is F-periodic after a multiple. Apply the named Smale
theorem to both maps, conditionally on its still-open lower geometric inputs: their nonwandering
sets equal the closure of this common periodic set. Shub p107's uniqueness proof identifies the
finite F-invariant mixing pieces with the Smale F-basic sets: intersect two finite disjoint closed
invariant transitive decompositions; a dense orbit in a piece cannot meet two disjoint invariant
pieces, so that whole piece lies in one piece of the other decomposition, and the reverse inclusion
proves equality. Thus LOCAL MAXIMALITY comes from the Smale F-basic-set export, not from mixing
alone. Keep all original orientation/index calculations for F; its induced integer action is
A_B^N=A^N by functorial iteration.

(C2: the SAME joint coding becomes mixing.) For each nonempty mixing F-basic set Λ_b choose exactly
the joint Bowen witness used by dynamics.manning_original_basic_set_signed_trace_g7 and
dynamics.bowen_hyperbolic_basic_set_markov_coding_g7. Bowen1970 Proposition30 p742 proves its shift
mixing by cylinders, as follows. A nonempty cylinder with prescribed labels on [−j,j] has a
finite-word rectangle intersection; Lemma26 makes the strip proper and Lemma27 gives its coded
point. The intersection of the corresponding interiors is nonempty and open. Lemma29 puts every code
of that physical open set in the chosen cylinder. Physical mixing of Λ_b therefore forces every
sufficiently large shift iterate of one cylinder to meet the other. The provider's every-label image
identity ensures each one-coordinate cylinder is nonempty. For every ordered pair of labels select
the resulting mixing threshold, and take the maximum over the FINITE pairs. A point in the cylinder
intersection gives an admissible path of length m, so every entry of T_b^m is positive for all
sufficiently large m. In particular some POSITIVE m has T_b^m>0. T_b is a finite, nonempty,
nonnegative primitive matrix. No period-m physical point is assumed to have a period-m ordinary
code, and no weighted phase formula is introduced. On a finite mixing basic set there is just one
point; choose its one-symbol witness directly, T_b=[1], with empty frontiers and no nonempty
correction alphabets.

(C3: physical boundary loss, before any correction-spectrum claim.) Let B_s be the finite union of
stable relative frontiers of THIS partition and B_u the unstable relative frontiers. They are
compact proper subsets. Bowen1970 Proposition31 pp742–743 proves F(B_s)⊂B_s and F^{-1}(B_u)⊂B_u: if
a stable-frontier point mapped to an unstable-interior point of a receiving rectangle, the Markov
u-subrectangle law would pull a full local unstable neighborhood back to the original point,
contradicting that frontier; the unstable statement is the inverse argument. The cylinder-image
identity used here is the SAME joint coding's π(C_i)=R_i, including every boundary label. This is
not an assertion about an unrelated partition or an intrinsic leaf topology.

For a nontrivial mixing piece use Bowen1971's actual C-density/specification proof. The finite
relatively open-and-closed unstable-closure decomposition in §2.7 pp379–380 is invariant under a
return; mixing forbids two nonempty such pieces, so the whole piece is C-dense. Its actual
specification algorithm applies. Here is the omitted-time counting calculation of Proposition3.11
pp385–386, also used by the forward-invariant version in Bowen1970 Lemma32 p743. Choose a ball about
w outside the closed proper set B_s and the printed sufficiently small ε, with specification
shadowing error ε/2 and 2ε<δ_* for the original expansive constant, BEFORE the periodic separation
inequality. Every orbit starting in B_s avoids that ball at every nonnegative time. More generally,
for m prescribed omitted times among 1,…,n−1 choose J of q omitted times separated by more than 2M,
with q≥m/(2M+1), where M is the FIXED specification gap. For each I⊂J and each point x in an
(n,ε)-separated subset E of the avoiding set, the specification follows x outside the disjoint
windows [j−M,j+M] indexed by j∈I (not all of J), shadows these prescribed orbit segments within ε/2,
and visits w at j∈I; the written construction produces a period-(n+M) point p(x,I). Distinct I
produce disjoint sets of constructed points: at the first discrepant insertion one construction
visits the missing ball while the other follows an orbit that avoids it. For fixed I the fibre
multiplicity is at most g^{|I|}, with g=N(2M+1,ε/2), by recording separated names in the insertion
windows. Consequently Σ_{I⊂J}|E|g^{−|I|}=(1+1/g)^q|E| is at most the total period-(n+M) count, which
the printed separation estimates bound by N(n+M,2ε)≤N(n,ε)N(M,ε). Thus N(n,ε,B_s)≤c τ^m N(n,ε),
c=N(M,ε), τ=(1+1/g)^{−1/(2M+1)}<1. Taking m=n−1 gives a STRICT exponential loss. Bowen1971
Proposition4.6 p388 identifies the sufficiently small fixed-scale separation growth with entropy:
expansivity gives a fixed D(ε) such that N(n,δ_*)≤N(n,ε)≤N(n+D(ε),δ_*), so the additive time shift
does not change the rate. This proves the operative forward-invariant avoidance conclusion of4.7
from its written proof, not by silently weakening its printed invariant-set statement. Apply the
inverse-time proof to B_u. Period-m physical points in each boundary are (m,ε)-separated: if two
were ε-close at all m residue times, periodicity makes them close at every integer time and original
expansivity makes them equal. Hence their PHYSICAL counts have limsup m^{-1}log bounded strictly
below h(F|Λ_b). No measure-zero boundary, periodic equidistribution or code-fibre entropy is
assumed.

For each nonprincipal related-set composition ι, the exact signed-trace supplier sends every
period-m B_ι word to a PHYSICAL F^m-fixed point on B_s∪B_u, with its uniform per-point bound D
independent of m. Therefore 0≤tr(B_ι^m)≤D(N_m(B_s)+N_m(B_u)). Empty alphabets have trace0. There are
finitely many ι. Once the principal normalization h(F|Λ_b)=log ρ_b is bound, the strict loss gives
constants C_b<∞ and 0<r_b<ρ_b with all correction traces ≤C_b r_b^m (enlarge C_b for the finitely
many early m). Their signed sum divided by ρ_b^m tends to0. The formal
`franks_manning_correction_trace_limit` and `franks_manning_signed_corrections_limit` prove
this decay from eventual strict exponential bounds, allowing a separate bound for each term. This is a direct bound on correction
TRACES; it neither asserts that all correction eigenvalues have smaller modulus nor needs a global
tuple dynamics or an ordinary periodic code lift. Bowen1970 Theorem33 pp743–744 identifies the
entropy of this SAME physical factor with its symbolic entropy; the finite primitive shift's
symbolic-entropy/Perron normalization is part of the precise lower carrier binding specified in C4
below.

(C4: actual primitive Perron proof and original triangular/entropy source application.) Gantmacher,
Applications of the Theory of Matrices, Interscience1959, ChapterIII pp66–75 and the FORWARD
implication of Theorem8 p97, supplies the written finite primitive-matrix dominance argument. On
nonnegative nonzero x set r_x=min_{x_i>0}(Tx)_i/x_i. Homogeneity restricts to the compact
nonnegative unit sphere. Replace it by (I+T)^{d−1} of that sphere, whose points are positive for
irreducible T; the commuting positive multiplication does not decrease r_x. On this positive compact
image r_x is continuous and attains r at z>0. If Tz−rz were nonzero and nonnegative, multiplication
by (I+T)^{d−1} would make the residual strictly positive, giving a strictly larger ratio, a
contradiction. Thus Tz=rz and r>0. For Ty=αy, |α||y|≤T|y| gives |α|≤r. Equality forces positive
moduli; a linear combination with a zero coordinate excludes two independent Perron eigenvectors.
Applying the same argument to Tᵗ, the adjugate B(r)=adj(rI−T) has positive right/left eigenline
columns/rows. The written cofactor derivative identity Δ′(r)=Σ_i B_ii(r)>0 proves algebraic
simplicity. The equality-phase lemma pp70–73 proves that peripheral eigenvalues are simple and their
phases form a finite cyclic group; pp74–75 gives the corresponding cyclic block form. For a POSITIVE
power T^q, q≥1, the forward implication of Theorem8 p97 first rules out reducibility. Its literal
remaining argument counts multiplicities: the h simple peripheral roots of T yield h powered roots
of T^q counted ALGEBRAICALLY, even when their q-th powers coincide. The positive matrix T^q has a
simple, strictly dominant Perron root, so h=1 and r is the UNIQUE peripheral eigenvalue. The
concrete triangular-basis calculation below supplies this power/multiplicity inference on the same
original matrix. Nonempty finite dimension and a genuinely positive power are essential; a zero
scalar matrix or an empty index set is not admitted by vacuous positivity.

(C4a: SAME triangular carrier, written source and exact shape/product APIs.) For each nonempty
finite real transition matrix T take its entrywise complexification T_C and the endomorphism
f_T=T_C.mulVecLin of the ORIGINAL finite complex coordinate space. The finite field module has its
actual standard basis; no positivity, self-adjointness, normality or diagonalizability of f_T is
assumed. Axler4e5.44 pp159–160 constructs an upper-triangular basis by induction on the number of
linear factors of the minimal polynomial: with U=range(f_T−d_last I), U is invariant, the
restriction is annihilated by the preceding factors, its triangular basis is extended to the full
space, and every added vector maps to U plus d_last times itself. The fundamental theorem of algebra
splits the complex minimal polynomial, giving5.47p160. Choose ONE such basis b, and let
H=toMatrix(b,b,f_T); write d_i=H_ii. The written coordinate-composition calculation3.43p74 gives
toMatrix(b,b,f_T^m)=H^m; its basischange formula3.84p93 identifies H with the original coordinate
matrix by conjugation. These statements refer to the same f_T and basis for ALL powers.

The exact Matrix.BlockTriangular.pow terminal instantiated with the identity block label on the
finite ordered index proves H^m upper triangular, including m=0; this supplies the shape step which
Axler5.81p179 and8.31p313 refer to as the Section5C exercise. We do NOT call that exercise a printed
proof. The written5.81 calculation supplies diagonal multiplication: (HJ)_ii=Σ_k H_ik J_ki has only
k=i surviving when H,J are upper triangular (k<i kills H_ik, k>i kills J_ki). Thus induction gives
(H^m)_ii=d_i^m for all m≥0, with m=0 the identity diagonal1. The exact
Matrix.charpoly_of_isUpperTriangular terminal gives charpoly(H^m)=Π_i(X−C(d_i^m)); at m=1 it gives
Π_i(X−C(d_i)). This is the characteristic-polynomial determinant product from Axler9.62p363 on this
same basis. Hence every diagonal occurrence represents its algebraic root multiplicity, and
collisions d_i^m=d_j^m are retained as repeated factors. Axler8.31p313 explicitly identifies
diagonal occurrences with generalized-eigenspace multiplicity; its8.49–52pp326–328 gives the finite
double-sum cyclic-trace and basis-invariance proof. More directly in the existing exact API,
LinearMap.trace_eq_matrix_trace applied to the same endomorphism f_T^m first in its ORIGINAL
standard basis and then in b identifies the two matrix traces. Matrix.trace is the finite diagonal
sum. Therefore tr(T_C^m)=tr(H^m)=Σ_i d_i^m. Entrywise scalar mapping/power preserves the original
real T^m, whose trace is the same real number cast into ℂ. No use of a generic unspecified
eigenvalue list, Jordan functional calculus, reduced adjugate Eq82/84 or a different triangular
basis at each m is made.

The formal `franks_manning_positive_eigenvector_unique` and
`franks_manning_positive_power_eigenvector_unique` isolate Gantmacher's zero-coordinate
argument, conditional on the strictly positive matrix (or positive power) and a positive
eigenvector. In the Gantmacher positive-power inference above, list the h simple peripheral roots
among these diagonal occurrences for T. For q≥1, the SAME product Π_i(X−C(d_i^q)) shows that their q-th powers
contribute h algebraic occurrences to T^q, including collisions. The same list bounds every root
modulus byρ^q and contains a root of modulusρ^q, so the spectral maximum of T^q isρ^q. A positive
matrix T^q has exactly one peripheral root, of algebraic multiplicity1, by the written positive
Perron proof. Thus h=1. This closes the distinct power-spectrum/multiplicity application by the
concrete triangular product calculation, rather than assuming the eigenvalue-power existence leaf
proves multiplicities. With the simple strictly dominant Perron occurrence first,
tr(T^m)/ρ^m=1+Σ_{i>1}(d_i/ρ)^m→1 by the real norm geometric limit and finite sums. The formal
`franks_manning_triangular_trace_limit` proves this limit for the same upper triangular matrix,
and `franks_manning_endomorphism_trace_limit` transports it to the original endomorphism through
one fixed basis. The triangular basis and its simple strictly dominant diagonal remain inputs. Zero-dimensional
matrices bypass the book's nonzero-space reasoning: their trace is0 and charpoly is the empty
product1; they are never used to produce a positive Perron root. The q=0 identity case is covered
algebraically but never used as the positive-power primitive witness; scalar zero is still excluded
by genuine q≥1 positivity.

(C4b: written two-sided entropy normalization on the SAME finite matrix.) Use Walkden, MAGIC010
Lecture8 Topological Entropy, AUTHOR LECTURE NOTES, Proposition8.12/Theorem8.13 pp12–13,
Proposition8.15 pp13–14 and Proposition8.17 pp15–16. The original two-sided finite-type shift Σ_T is
compact, and its zero-coordinate cylinders form a finite clopen partition α. An all-integer cylinder
itinerary determines each coordinate, so its intersection contains at most one sequence; this
directly proves the generator premise without invoking the omitted Proposition8.14. The shift is
expansive by the same coordinate test. For THIS clopen coordinate generator, an atom of ∨_{j=−N}^N
σ^{−j}α fixes every coordinate in [−N,N]; the standard finite-symbol product metric directly makes
its diameter tend to0. Thus no broad diagonal-subsequence proof is imported for an arbitrary
generator. For any finite open cover β choose a Lebesgue number and then such a finite window
refining β. Its n forward joins are contained in the single window from −N through n+N−1, having
n+2N times; dividing by n gives the same limiting entropy as α. Hence α computes open-cover entropy.
The written8.12–8.13 spanning/separated comparisons give the SAME separated-set entropy used in
Bowen: a cover with Lebesgue radius r yields N(∨T^{−j}α)≤p_n(r/2)≤q_n(r/4), while a cover of
diameter<ε gives p_n(2ε)≤q_n(ε)≤N(∨T^{−j}β). The factor2 is explicit: a maximal set with pairwise
orbit distance>ε has every point at distance≤ε from one of its members, hence it spans by OPEN
radius2ε balls. This follows the source maximality algorithm while repairing the literal open-ball
boundary in Lemma8.10; it does not assert open ε-spanning from that algorithm. Taking logarithms,
dividing by n and shrinking the mesh identifies the two definitions. No missing generator-existence
theorem is used.

The n-fold α join is the DISJOINT partition into nonempty cylinders with n symbols, so its minimal
subcover has exactly the number W_n of allowed words. Every such word has n−1 edges. Matrix
multiplication counts paths by finite induction, giving W_n=Σ_{i,j}(T^{n−1})_{ij} for n≥1. Every
finite allowed word extends to a bi-infinite path: a genuinely positive power supplies a finite loop
through each endpoint, repeated backwards before the initial vertex and forwards after the terminal
vertex. Thus no transient or nonextendable words are counted. This corrects the printed8.17
off-by-one T^n to T^{n−1} rather than changing the entropy. For d≥1 put S_m=Σ_{i,j}|(T_C^m)_{ij}|
and R_m=max_iΣ_j|(T_C^m)_{ij}|. The complexification preserves nonnegative real entries, hence
W_n=S_{n−1}. Each nonnegative row sum is at most S_m and at most R_m, respectively, and summing the
d rows gives R_m≤S_m≤d R_m. Neither entry-sum nor a Euclidean matrix norm is silently identified
with an operator norm.

Install on the SAME matrix algebra Matrix (Fin d) (Fin d) ℂ the explicit Matrix.linftyOpNormedRing
and Matrix.linftyOpNormedAlgebra instances. The existing mathlib.matrix_pi_sup_operator_norm_g10 row
formula gives its norm exactly R_m. The existing finite_dimensional_pi_g8 gives Module.Finite ℂ (Fin
d→ℂ); the exact generic Module.Finite.pi leaf applies to the outer finite index with that finite
receiving module, giving Module.Finite ℂ (Fin d→(Fin d→ℂ)), the actual matrix module. Existing
finite_dimensional_complete then gives completeness for THIS installed normed-module uniformity. No
default Pi metric, extra currying theorem or finite-dimensionality transfer across an unproved norm
equivalence is substituted. Matrix.mem_spectrum_iff_isRoot_charpoly on the SAME unital complex
algebra identifies its algebraic spectrum with the characteristic roots, independent of this choice
of norm. The written Gantmacher proof supplies a positive real Perron root ρ and bounds every root
modulus byρ. Thus ofRealρ belongs to the norm image of the spectrum and is an upper bound on every
such image. Apply the exact spectralRadius_eq_of_unital leaf to this unital ring/algebra: it
identifies spectralRadius with the ENNReal indexed supremum over algebraic-spectrum norms, although
the underlying general definition uses quasispectrum. This identity therefore gives spectralRadius ℂ
T_C=ENNReal.ofRealρ: one inequality is the uniform upper bound, and the reverse is the actual Perron
spectrum member. This uses no unproved spectral maximum lemma or eigenbasis.

Apply the existing exact Gelfand norm-root leaf with these NormedRing, NormedAlgebra ℂ and
CompleteSpace structures: ENNReal.ofReal(R_m^(1/(m:ℝ)))→ENNReal.ofRealρ. The limit is finite, and
every real root is nonnegative. Existing ENNReal.tendsto_toReal at this finite limit recovers
R_m^(1/m)→ρ. Positivity ρ>0 and real logarithm continuity give (1/m)logR_m→logρ for m≥1; nonzero
T_C^m follows already by applying it to the positive Perron vector, so no logarithm of0 occurs. From
R_m≤S_m≤dR_m, 0≤(logS_m−logR_m)/m≤logd/m→0, and therefore (1/m)logS_m→logρ. Finally n−1→∞ and
(n−1)/n→1 imply (1/n)logW_n→logρ. Walkden's generator calculation gives h(σ_T)=logρ, and Bowen1970
Theorem33 on the SAME joint partition gives h(F|Λ_b)=logρ. This completes the needed normalization
for the physical frontier estimates and count limits above. The finite mixing singleton uses T=[1]
and zero entropy directly; d=0/empty correction alphabets bypass this nonempty Perron/Gelfand
argument, as already stated. The logarithm continuity is at ρ>0; no claim logρ>0 is necessary (the
singleton has ρ=1).

Current source scope: the two triangular algebraic bindings and the symbolic entropy/Perron
normalization are supplied by this ONE coherent original-carrier C4 application, relative to the
exact named terminals and the unchanged original Smale/index/homology providers. Prior three-guard
records are historical epochs superseded ONLY for these three bindings. Eq82/84 remain unused,
Brin–Stuck's exercise-dependent candidate remains a historical negative screen, and the whole Franks
theorem remains SOURCE/open/incomplete on its actual named lower and global obligations.


(C4c: normalized physical counts.) The finite-family normalization and its eventual-positivity
consequence are formalized by `franks_manning_normalized_count_sum` and
`franks_manning_count_sum_eventually_pos`; their hypotheses retain the individual basic-set
asymptotics. C4a gives tr(T_b^m)/ρ_b^m→1. C4b identifies the SAME physical
entropy with logρ_b, so C3's strict physical-frontier estimate and its uniform
word-to-physical-point multiplicity give every correction trace divided byρ_b^m→0. The exact signed
count therefore yields N_{b,m}/ρ_b^m→1. The exact limit passage, including the real-valued
physical-count conclusion, is formalized by `franks_manning_real_count_limit_of_signed_traces`;
the signed count identity and actual boundary bounds remain explicit premises. Sum over the finitely many mixing F-basic sets: with
ρ=max_bρ_b>0, the lower-rate terms vanish geometrically and N_m/ρ^m→c, where c is the positive
integer number of maximizing pieces. This is Manning Case2 on the ACTUAL common return F. In
particular N_m>0 eventually. The finite singleton is direct. These conclusions use the named
original Smale spectral/basic-set, winding/homology, orientation and local-index/count inputs; their
lower obligations remain independent. Gantmacher Eq82/84 remains unused, so no
reduced-adjugate/minimal-polynomial functional calculus or full normalized-matrix-power source proof
is claimed.

(C5: the written irrational-frequency argument.) Let ζ₁,…,ζ_n be the characteristic roots of the
ORIGINAL complexification of A^N, with algebraic multiplicities. The determinant count above is
N_m=∏_i|1−ζ_i^m|. A root of unity would force zero for infinitely many m, contradicting eventual
positivity. For each unit-modulus root write ζ=e^{2πit}; non-root-of-unity implies t irrational.
Kuipers–Niederreiter1974 Chapter1 Theorem2.1 pp7–8 and Example2.1 p8 prove its uniform distribution:
for every nonzero integer h the geometric-sum identity bounds |M^{-1}Σ_{j=1}^M e^{2πihjt}| by
1/(M|sinπht|)→0. Approximate a continuous periodic function uniformly by a finite trigonometric
polynomial; the nonconstant Fourier averages vanish and the constant coefficient is its integral.
Theorem1.1 pp2–3 then squeezes interval indicators between continuous lower/upper approximants with
arbitrarily small integral gap, so averages of interval indicators tend to interval length.
Corollary1.1 p3 allows the Riemann-integrable arc indicators; split an arc crossing0 into two
intervals. Its finitely many endpoints have frequency0 by the same arbitrarily short majorizing
intervals. Therefore each irrational unit rotation visits a prescribed arc with exactly its
normalized arc length, not merely infinitely often.

Write B=∏_{|ζ_i|>1}|ζ_i|>0, D_m=∏_{|ζ_i|<1}|1−ζ_i^m|∏_{|ζ_i|>1}|1−ζ_i^{-m}|→1, and
P_m=∏_{|ζ_i|=1}|1−ζ_i^m|. Thus N_m=B^m D_m P_m. Keep P_m distinct from Manning's normalized LOG of
this product. If there are k≥1 unit roots, eventual positivity makes logs defined and C4 gives
m^{-1}log P_m→ℓ=logρ−logB. Since P_m≤2^k, ℓ≤0. Choose one symmetric arc {|t|<a} about1 with 0<a and
2ka<1/2. Each bad-time set has frequency2a; the elementary finite union bound gives lower frequency
at least1−2ka>1/2 for times avoiding ALL bad arcs. At every such time each factor is ≥d=2sin(πa)>0,
so P_m≥d^k. Along these arbitrarily large good times m^{-1}log P_m≥k logd/m→0; since the whole
sequence has limit ℓ, ℓ≥0. Hence ℓ=0 and ρ=B. Now N_m/ρ^m→c and D_m→1 force P_m→c>0. Fix ONE
irrational unit root. Every smaller arc about1 has positive frequency; successively choose
increasing times at which that root lies in shrinking arcs. Its factor tends to0 and all other unit
factors are ≤2, so P_m tends to0 on this subsequence, a contradiction. No independence of rotations,
simultaneous recurrence, compact-group theorem or two specially chosen compact-group subsequences is
used. Thus A^N has no unit-modulus characteristic root, relative to the exact original-carrier
normalization supplied in C4 and the named original count/spectral inputs. If the unit list is empty
this conclusion is already true. Rank n=0 is the direct singleton case, with all empty products1 and
no eigenvalue.

(C6: return to the ORIGINAL integer endomorphism, without differentiating q.) The exact
integer-matrix power descent is formalized by `franks_manning_hyperbolic_of_matrix_power`;
its premise is the power hyperbolicity established by the preceding count argument. Regard A_C as
entrywise Complex.ofInt of A on the finite complex vector space Fin n→ℂ, and f_A=A_C.mulVecLin. The
existing mathlib.matrix_map_pow identifies complexification of A^N with A_C^N. On these finite
coordinates Matrix.toLin′ M and M.mulVecLin are the SAME linear map, as their evaluations on every v
are M*ᵥv. The exact new mathlib.matrix_toLin_prime_pow_g7, specialized to the commutative semiring ℂ
and Fin n, therefore identifies the endomorphism of A_C^N with f_A^N for every N, including N=0 and
n=0. The existing mathlib.matrix_mulVec_mulVec verifies the composition action on the original
vectors: A_C*ᵥ(A_C^j*ᵥv)=(A_C*A_C^j)*ᵥv. No basis change or nonempty-index guard is needed.
mathlib.matrix_charpoly_mulVecLin and mathlib.module_end_hasEigenvalue_iff_isRoot_charpoly bind
characteristic roots to eigenvalues on this actual finite free complex module. If f_A had an
eigenvalue ζ of modulus1, mathlib.module_end_hasEigenvalue_pow_g7 would give ζ^N for f_A^N, and
mathlib.complex_norm_pow gives |ζ^N|=1, contradicting C5. These are SAME finite coordinate carriers
and the ORIGINAL winding matrix; no smoothness of q, derivative of a topological conjugacy,
transported standard atlas or new target hypothesis is introduced. The central power-multiplicity,
trace and entropy bindings are supplied in C4; the named Smale/index/homology source obligations
remain independent; it is not whole-parent or transitive/Lean closure.

12. Fixed-point existence for the pointed construction
Once the induced A is hyperbolic, apply the current source-replaced
topo.original_torus_lift_fixed_point_existence_g8 to the original smooth M, the chosen topological
q, and its pullback universal cover p:P→M. It applies to every continuous lift F of every positive
iterate. Write G=Q F Q⁻¹=A^m v+e(v) in topological real coordinates, with e continuous,
deck-periodic and bounded by K. The actual Franks1969 Lemma1.2 homotopy is H(t,v)=t A^m v+(1−t)G(v).
Invertibility of I−A^m gives μ>0 and ‖v−H(t,v)‖≥μ‖v‖−K, so the full fixed set of this homotopy is
contained in one ball uniformly in t. It is a closed subset of the compact product of that closed
ball with [0,1], and its projected union of fixed supports is compact. This is the literal guard of
Dold1965 Homotopy Invariance1.7 p2. His Proposition1.3 p1 computes endpoint indices on the same
support fundamental class, so I(G)=I(A^m). Dold Definitions1.1–1.2 and the named linear-degree
theorem give I(A^m)=sign det(I−A^m)≠0. If G had no fixed point its support class and index would
be0. Hence G, and thus F, has a fixed point; projection with m=1 gives x0∈M and allows q(x0) to be
translated to0 for the pointed compact-CW semiconjugacy construction. This follows the published
Franks/Dold existence argument. It does not use Anosov fixed-point isolation, equal local signs,
uniqueness or global Lefschetz trace normalization, and it never differentiates Q. For n=0 all
spaces are singletons and existence is immediate.

13. Smooth nondegenerate local index in the original smooth chart
Use the homological index of topo.euclidean_fixed_point_index_basic_laws_g9 and the ENR extension
proved in the published Dold commutativity/retraction step below. In n=0 the chart is a singleton
and the local H0 index and empty determinant are both1. Handle this singleton case before any
positive-rank normalization or Taylor radius. BIND THE ORIGINAL PREFERRED CHART BEFORE THE LOCAL
HOMOTOPY. For the positive-period original smooth lift F at its fixed point x, use the ORIGINAL real
smooth structure of array2 and its preferred chart c_0 at x, so x∈c_0.source. Put
U=c_0.source∩F⁻¹(c_0.source). This is OPEN by original continuity of F and mathlib.isOpen_preimage,
and contains x because F(x)=x. Define the centered chart c(z)=c_0(z)−c_0(x) and the exact OPEN
coordinate source V_0=c(U). Translation preserves the original chart topology and smoothness, c(x)=0
and c⁻¹(0)=x. The coordinate map f_c=c∘F∘c⁻¹ is defined on V_0, takes values in the ambient original
real coordinate model and satisfies f_c(0)=0. Only the source U and ENDPOINT image F(U)⊂c_0.source
are used; no all-t homotopy-image chart or self-map assertion is added.
Let E=T_xP with its original inherited metric topology and B_native=DF_x as explicitly realized in
array13. The genuine preferred tangent trivialization over x is linear on the ORIGINAL fibre and has
x in its base set. mathlib.bundle_trivialization_continuousLinearEquivAt gives its actual
C:E≃L[ℝ]E_coord, with the literal inverse from the same trivialization.
mathlib.tangent_trivialization_chart_mfderiv, pinned Atlas411–419, identifies its forward map with
D(c_0)_x; mathlib.tangent_inverse_trivialization_chart_mfderiv, Atlas425–432, identifies its inverse
with the derivative of the SAME inverse extended chart within range I. Here array2 has
I=modelWithCornersSelf ℝ E_coord and range I=univ. mathlib.mfderivWithin_of_isOpen at that universal
set therefore identifies this with the ordinary inverse-chart derivative. The actual chart inverse
equations give C⁻¹C=Id_E and CC⁻¹=Id_coord on these same fibres. Centering is bound by the actual
manifold-valued scalar subtraction APIs: mathlib.mfderiv_sub on the original smooth c_0 and the
fixed constant c_0(x), together with mathlib.mfderiv_const, gives Dc_x=D(c_0)_x−0=C. The inverse
centering translation v↦v−(−c_0(x)) has derivative Id by those same sub/const identities and
mathlib.mfderiv_id; composing with c_0⁻¹ gives Dc⁻¹_0=C⁻¹. Alternatively the two same-chart inverse
identities differentiated by mfderiv_comp/mfderiv_id give the identical two inverse compositions. No
isometry or derivative of Q is asserted.
Follow Lee2003 Computations in Coordinates pp69–72, especially the written Eq(3.7)pp71–72: the
pushforward is the Jacobian of the literal coordinate representative on c_0(U). Apply
mathlib.mfderiv_comp to the original smooth maps at x and its actual fixed image, then
mathlib.mfderiv_eq_fderiv between the self-modeled coordinate spaces. The smooth maximal-atlas
coordinate criterion mathlib.contMDiffAt_iff_of_mem_maximalAtlas applies with both chart-source
memberships just verified. These give smoothness and the actual ordinary derivative
B=Df_c(0)=C∘B_native∘C⁻¹ in the supplied coordinate norm. In particular this is a LOCAL coordinate
derivative of F on V_0, not a derivative of a topological torus chart or an identification of
arbitrary fibres.
mathlib.differentiableAt_hasFDerivAt turns this original local differentiability into HasFDerivAt
f_c B 0. The actual linear map B has derivative B by mathlib.continuousLinearMap_hasFDerivAt. Define
r(v)=f_c(v)−Bv on V_0; mathlib.hasFDerivAt_sub gives HasFDerivAt r 0 0, while f_c(0)=0 gives r(0)=0.
Applying mathlib.hasFDerivAt_iff_isLittleO_nhds_zero to f_c at0 yields precisely r(v)=o(v),
equivalently r(v)=o(||v||) and ||r(v)||/||v||→0 along nonzero v→0 in this OPEN neighborhood. The
zero-derivative form applied to r gives the same assertion. These are local statements on the
original chart, and all displayed evaluations are retained within V_0.
The ACTUAL unit inverse constructed in array13 for L_native=Id_E−B_native supplies a bounded
continuous S_native on E with L_native∘S_native=Id_E and S_native∘L_native=Id_E. In the coordinate
norm put L=Id_coord−B=C∘L_native∘C⁻¹ and S_c=C∘S_native∘C⁻¹. Directly using BOTH original unit
identities and C⁻¹C=Id_E, CC⁻¹=Id_coord gives L∘S_c=Id_coord and S_c∘L=Id_coord. Thus S_c is the
genuine SAME-map bounded inverse L⁻¹ used below. No determinant bridge, new norm, orthogonality or
isometric-chart premise enters. Shrink the ORIGINAL coordinate neighborhood to contain a closed ball
of radius2ε before the Bredon Taylor construction, keeping its source in V_0 and its endpoint
F-image in c_0.source. The smooth chart/remainder/transported inverse application is now supplied at
this node's one level, relative to the named original derivative/unit providers.

For the positive-rank LOCAL nonlinear homotopy follow only the written normalization, Taylor
estimate and INNER homotopy in Bredon, Topology and Geometry(1993), IV§7 Propositions7.1–7.2
printedpp190–191, specifically7.2p191/PDF108right. The actual derivative displacement L=I−B has the
genuine same-map bounded inverse supplied by Step14's unit/equivalence construction, transported
through the ORIGINAL smooth chart derivative. Put D(v)=Lv−r(v) and normalize H(v)=L⁻¹D(v)=v+g(v),
where g(v)=−L⁻¹r(v). Thus H(0)=g(0)=0 and DH(0)=I; boundedness of this actual L⁻¹ and the original
differentiability give g(v)=o(||v||). Use the literal Taylor local shrink in the printed proof to
choose ε>0 with the radius2ε closed coordinate ball inside the original source/image chart guards
and ||g(v)||<(1/2)||H(v)|| for0<||v||≤2ε. This is the printed estimate relative to H, replacing the
previous reciprocal inverse-norm radius choice. Original derivative/remainder/coordinate and
actual-inverse identification are the explicit application data, not stronger target hypotheses.
On the INNER ball ||v||<ε use exactly its branch H_t(v)=H(v)−t g(v), t∈[0,1], whose endpoints are
H_0=H and H_1=Id. For v≠0 the strict printed estimate forces H(v)≠0 and gives
||H_t(v)||≥||H(v)||−t||g(v)||>(1/2)||H(v)||>0. At0 every H_t is0. Compose back by the actual L and
reverse t: D_t(v)=L H_(1−t)(v)=Lv−t r(v), so D_0=L and D_1=D. This is a direct specialization of the
written local inner branch, not its global sphere construction, annular interpolation,
unique-preimage theorem or compactification. Each D_t is nonzero off0, and the original continuous
coordinate maps and actual linear inverse give joint continuity in(t,v). Therefore it supplies local
isolation and the fixed-pair homotopy on (ball(0,ε),ball(0,ε)\{0})→(ℝⁿ,ℝⁿ\{0}) under those exact
original-chart bindings. Bind this SAME inner homotopy to Dold1965 Definitions1.1–1.2/Proposition1.3
printedp1 and the written homotopy proof1.7 printedp2, through the public
topo.euclidean_fixed_point_index_basic_laws_g9. Set V=ball(0,ε), K={0}, and k_t(v)=v−D_t(v)=(I−L)v+t
r(v), a jointly continuous map V×[0,1]→R^n. Its endpoints are k_0(v)=Bv and k_1(v)=Bv+r(v)=f_c(v),
since L=I−B. Its fixed set is EXACTLY K for every t: k_t(v)=v iff D_t(v)=0, and the retained inner
estimate shows this happens precisely at0. Thus the union of fixed sets is the compact singleton K,
and the full fixed graph is K×[0,1], compact in V×[0,1]. No k_t(V)⊆V or homotopy-image-into-chart
requirement is imposed: Dold's maps have open SOURCE V and ambient TARGET R^n. The original
coordinate map endpoint alone keeps its already selected source-and-image chart guards.

Dold1.1 defines the SAME positive supported class o_(V,K)∈H_n(V,V\K;Z) by restricting the positive
compactification class and excising into this actual open V. Dold1.2 defines
I(k_t,V)=(id−k_t)_*o_(V,K)=(D_t)_*o_(V,K) in the SAME oriented H_n(R^n,R^n\{0};Z). Dold1.3 permits
this exact isolating V and this compact common K. Its written1.7 proof now applies literally:
D_t:(V,V\K)→(R^n,R^n\{0}) is a homotopy of these FIXED pairs, so
topo.relative_singular_homotopy_invariance equates the endpoint induced homomorphisms on o_(V,K).
This is not an appeal to a varying-support index theorem without checking its support, nor a new
graph/intersection definition of the index. Hence I(f_c,V)=I(B|V,V)=L_*o_(V,K).

For the last notation, the inclusion j:(V,V\{0})→(R^n,R^n\{0}) carries o_(V,{0}) to the standard
positive local generator by Dold1.1/1.3 and their natural excision comparison. The endpoint
displacement is L∘j, so functoriality gives (L∘j)_*o_(V,{0})=L_*(j_*o_(V,{0})). The public
topo.invertible_real_linear_local_degree_g9 identifies this automorphism on the ACTUAL local
relative group as multiplication by sign(det L), independent of the chosen generator. Consequently
the original chart index equals sign det(I−B). The derivative B is that of the original smooth F in
this ORIGINAL smooth chart, never a derivative of the topological Q; another smooth chart conjugates
B by its derivative and leaves det(I−B) unchanged.

Finally apply the already written published Dold ENR transfer in Step16 (arrayindex15), specifically
Dold2.3p3 and2.4pp3–4. If X′ is this original chart neighborhood, use the open local SOURCE
W=X′∩F⁻¹(X′) containing the isolated fixed point, so the endpoint map F|W has TARGET X′. The
coordinate representative and the restricted Q representation of this local ENR neighborhood are the
two representations to which the protected triangular commutativity/representation-independence
proof applies. Dold1.3 restricts further to the selected coordinate V, containing the whole
singleton support. It follows that the computed chart index is the original intrinsic local ENR
index i_F(x)=sign det(I−DF_x). No F(W)⊆W is required, and no Q derivative is taken. In dimension0
the initial singleton/H0/empty determinant calculation supplies1 directly; no positive-radius Taylor
or sphere assertion is used there. This discharges ONLY the former SAME
relative-displacement/support-class/excision/local-degree/ENR chart-application gap, conditional on
the unchanged original chart/remainder/inverse guards and the named providers' genuine lower
homology foundations. The construction/naturality use the exact Dold1.1–1.3/1.7 source portions of
the named G9 basic-law theorem; its entire basic-law conjunction now has a complete Stage1 source
proof, with D6a–D6d supplying the integral product law relative to the named lower homology
prerequisites; the separate Dold global Lefschetz proof and its open product/cubical foundations are
not part of this derivative calculation.

14. Hyperbolic determinant sign without an adapted metric
Fix a POSITIVE iterate m≥1 in the original periodic-point application. At a fixed point x of its
smooth lift F, put y=p(x), so f^m(y)=y. Use the ACTUAL real tangent fibre E=T_xP with the pullback
of the GIVEN original Riemannian norm, not a complex tangent or a new coordinate/adapted norm. The
protected smooth covering/pullback tensor construction makes Dp_x:E→T_yM a real linear isometry and
identifies B=DF_x with D(f^m)_y by Dp_x B=D(f^m)_y Dp_x. The original tangent metric induces the
existing fibre topology, as in geo.def_smooth_real_tangent_metric, so the smooth derivative B is the
same continuous real linear map with this norm. The original real tangent bundle is the rank-n
native vector bundle; mathlib.vector_bundle_fibre_finite_dimensional, with K=ℝ and its actual real
n-dimensional model, gives the finite-dimensional fibre E. Write E_s,E_u for the inverse images
under Dp_x of the GIVEN original invariant E^s_y,E^u_y. They are the actual complementary real
tangent submodules with their INHERITED Riemannian norms/topologies.
mathlib.finite_dimensional_submodule_g8 makes each finite dimensional, without smoothness of these
subbundles, orthogonality, a nonzero vector or a positive-rank premise.

ORIGINAL FINITE/FREE MODULE GUARDS. For W=E,E_s,E_u the FiniteDimensional ℝ W already supplied above
is DEFINITIONALLY Module.Finite ℝ W: pinned LinearAlgebra/FiniteDimensional/Defs.lean72–75 defines
the abbreviation, with Basis/VectorSpace imported at8. Freeness is a separate genuine
basis-existence input: apply mathlib.module_free_of_divisionRing_g7, the exact priority100 instance
Module.Free.of_divisionRing from Basis/VectorSpace.lean155–157. Its printed proof uses
Module.Free.of_basis (Module.Basis.ofVectorSpace ℝ W), whose basis extends the empty independent
family; its only guards are DivisionRing ℝ, AddCommGroup W and Module ℝ W. These hold for the
original tangent module and its actual submodules. No topology, positive rank, nonzero vector or new
finite-dimensionality premise is needed. Thus the original SAME real modules have the
Module.Finite/Module.Free instances required by the determinant/unit theorems below, including zero
summands.

The native chain rule mathlib.mfderiv_comp applied to the original smooth F and its inverse, and
mathlib.mfderiv_id on their two compositions, gives the genuine inverse B^(-1)=D(F^(-1))_x on the
SAME fixed fibre. The GIVEN original invariant splitting, pulled back through Dp_x, is preserved by
both derivatives. Apply the exact source definition mathlib.continuousLinearMap_restrict_g8 to
obtain B_s:E_s→L[ℝ]E_s, B_u:E_u→L[ℝ]E_u and the corresponding restrictions of B^(-1). Their ambient
values are the original Bv or B^(-1)v by the written coe_restrict_apply/restrict_apply equations.
The actual source restrict_comp identity identifies their composites with the identity restrictions,
so the backward unstable restriction is the genuine B_u^(-1), not a separately chosen inverse
operator. Multiplication in each continuous-linear endomorphism algebra is composition and its unit
is the SAME identity map. Repeated native chain rule at the FIXED point and the
restriction/composition equations identify B_s^k and (B_u^(-1))^k, including k=0, with the
corresponding actual restrictions of D(F^k)_x and D(F^(-k))_x. The covering derivative relation in
both directions identifies these with D(f^(mk))_y and D(f^(-mk))_y under the SAME isometry Dp_x; it
never compares arbitrary tangent fibres by an unprovided chart identification.

For EVERY v in the corresponding original inherited-norm subspace the GIVEN Anosov bounds therefore
give
 ||B_s^k v||≤C(λ^m)^k||v||,  ||(B_u^(-1))^k v||≤C(λ^m)^k||v||
for every k≥0. Put q=λ^m; m≥1 and the original 0<λ<1 give 0<q<1. Since Cq^k≥0, apply the actual
written mathlib.continuousLinearMap_opNorm_le_bound to EACH actual restricted power with M=Cq^k. It
yields ||B_s^k||≤Cq^k and ||(B_u^(-1))^k||≤Cq^k in exactly these original fibre norms. The source
applies to all-vector bounds and needs no unit sphere, nontrivial fibre, one-step operator norm<1,
alternate C or adapted metric. At k=0 it is the original identity bound; in a zero-dimensional
summand the identity is the unique zero map and its norm is0, so there is no division by a
vector/identity norm or positive dimension requirement.

For either W=E_s or W=E_u, use R=(W→L[ℝ]W) with this INHERITED operator norm. The actual pinned
ContinuousLinearMap.toNormedRing constructor makes it a Hausdorff normed ring, and
ContinuousLinearMap.toNormedAlgebra supplies its ordinary real scalar action/algebra compatibility;
neither constructor assumes Nontrivial W or norm(I)=1. The existing
mathlib.finite_dimensional_complete gives CompleteSpace W over the complete scalar field ℝ. The
exact mathlib.continuousLinearMap_instCompleteSpace, with k1=k2=ℝ, σ=id and E=F=W, gives
completeness of the SAME bounded-convergence uniformity, which its qualified normed-space
compatibility identifies with this operator-norm uniformity. Normed spaces supply the topological
additive group, continuous scalar multiplication and sequentiality premises; the identity scalar
homomorphism is isometric. Thus R is the ACTUAL complete operator-norm carrier, not a declared
unspecified endomorphism API.

Fix t∈[0,1] and take T=B_s on E_s or T=B_u^(-1) on E_u. Put X_t=t•T∈R. The WRITTEN pinned smul_pow
induction, with scalar monoid ℝ and endomorphism monoid R, gives (t•T)^k=t^k•T^k for every k,
including k=0. Its IsScalarTower ℝ R R and SMulCommClass ℝ R R premises are exactly the
scalar/composition compatibility of the real endomorphism algebra, not commutativity of arbitrary
operators. Apply mathlib.norm_smul: since 0≤t≤1, |t|^k≤1, and therefore ||X_t^k||=|t|^k||T^k||≤Cq^k.
The existing mathlib.real_hasSum_geometric gives summability of k↦q^k for 0≤q<1; multiplying the
real series by the fixed C gives summability of the REAL majorant k↦Cq^k. Now
mathlib.summable_norm_comparison, the literal Summable.of_norm_bounded theorem on the COMPLETE
normed additive group R, yields h_t:Summable(k↦X_t^k). This is summability of the net of all finite
subsets supplied by that theorem, not merely convergence of ordered partial sums. Define
S_t=∑′_(k≥0)X_t^k; the same scalar-power identity makes this exactly the original S_t=Σ_(k≥0)t^kT^k.

Instantiate the TWO protected source theorems mathlib.summable_tsum_pow_mul_one_sub_g2 and
mathlib.summable_one_sub_mul_tsum_pow_g2 in this precise Hausdorff topological ring R with x=X_t=t•T
and the just-supplied h_t. The original-real carrier, inherited norms, restriction/power identities,
scalar modulation, complete uniformity and summability applications are now explicitly supplied at
this one level. The entire following inverse/determinant/block/unit/rank-zero suffix is retained
LITERALLY. Its historical original carrier/power/scalar/summability guards are superseded ONLY by
this supplied application; its other finite-module, original-chart/local-index and global Franks
source applications remain separate and no whole-parent completion is claimed.
The first source theorem gives S_t*(I−tT)=I, and the second gives (I−tT)*S_t=I. Their actual written
proofs use h.hasSum.mul_right(I−x), respectively h.hasSum.mul_left(I−x), to obtain the limits of the
multiplied natural partial sums; the finite geometric multiplication identity rewrites each to
I−x^N, h.tendsto_atTop_zero makes the remainder tend to0, and uniqueness of the Hausdorff limit
gives I. Thus both multiplication orders are supplied by literal generic summability identities. No
commutativity or norm<1 hypothesis is imported, and no continuity of t↦S_t is asserted or needed.
Thus I−tT stays invertible throughout [0,1]. For determinant nonvanishing and positivity use the
exact existing determinant and intermediate-value source leaves on this SAME real endomorphism
carrier. Put L_t=I−t•T and d(t)=det(L_t), where the determinant is the determinant of its underlying
real linear endomorphism. Forget continuity in the already supplied identity L_t*S_t=I and apply
mathlib.linearMap_det_comp and mathlib.linearMap_det_id: d(t)det(S_t)=1 for every t∈[0,1]. Thus
d(t)≠0 there, directly in ℝ; neither positive rank nor continuity of t↦S_t is required. The maps
t↦t•T and t↦I−t•T are continuous by mathlib.continuous_smul and mathlib.continuous_sub with the
identity scalar map and constant endomorphisms. Composition with
mathlib.continuous_linear_map_determinant makes d continuous, and L_0=I with det_id gives d(0)=1.
Fix any t∈[0,1]. If d(t)≤0, apply the ASCENDING-endpoint theorem mathlib.intermediate_value_Icc to
the continuous real function a↦0−d(a) on [0,t]. Its endpoint values satisfy −1=0−d(0)≤0≤0−d(t), and
0≤t. The exact theorem therefore gives s∈[0,t] with 0−d(s)=0. Since 0≤s≤t≤1, the previously proved
d(s)≠0 is contradicted. Hence d(t)>0 for every t∈[0,1]. Taking t=1 for the two original choices
T=B_s and T=B_u^−1 yields det(I−B_s)>0 and det(I−B_u^−1)>0. For the remaining block factorization
instantiate four exact source providers on the ORIGINAL invariant splitting. Let E be the SAME real
tangent space on which B acts, and E_s,E_u the actual original stable and unstable tangent
submodules. The GIVEN complementary splitting supplies IsCompl(E_s,E_u), so
mathlib.submodule_prodEquivOfIsCompl gives e:E_s×E_u≃ₗ[ℝ]E with e(u,v)=u+v. For every actual u∈E_s
and v∈E_u, the source prodEquivOfIsCompl sum formula gives e(u,v)=u+v. The already bound
coe_restrict_apply/restrict_apply equations give the ambient values of B_su and B_uv as B(u) and
B(v). Original linearity therefore gives B(e(u,v))=B(u+v)=B(u)+B(v)=e(B_su,B_uv) on these very
submodules. Subtracting this identity from e(u,v) gives (I−B)∘e=e∘((I−B_s).prodMap(I−B_u)); hence e
conjugates that product map to I−B. These are the required original-data realizations of the GIVEN
splitting, not new hypotheses, an orthogonal decomposition or an identification with unrelated
coordinate blocks. The ORIGINAL finite/free instance application above supplies exactly Module.Free
for det_smul and BOTH Module.Free/Module.Finite for det_prodMap on E_s,E_u, with their original real
ranks.
Apply mathlib.linearMap_det_conj to f=(I−B_s).prodMap(I−B_u) and this e, then
mathlib.linearMap_det_prodMap_g2, to obtain det(I−B)=det(I−B_s)det(I−B_u). On the original unstable
fibre the GENUINE two-sided inverse B_u^−1 gives I−B_u=(−B_u).comp(I−B_u^−1), directly because B_u
B_u^−1=I. The already used mathlib.linearMap_det_comp and new mathlib.linearMap_det_smul_g2 at
scalar−1 give det(I−B_u)=(-1)^d det(B_u)det(I−B_u^−1), where d=Module.finrank ℝ E_u is the original
real unstable rank. In particular det(B_u)≠0 follows by det_comp/det_id applied to its actual
inverse identity. The two determinant factors det(I−B_s) and det(I−B_u^−1) are positive by the
reviewed determinant/IVT component above, so the displayed product identities yield sign
det(I−B)=(-1)^d sign det(B_u). These exact source formulas allow zero-dimensional factors; no
nonzero-rank, orthogonality, operator-commutation, spectral or norm<1 premise is added. Realize the
inverse needed by the preceding original-chart local argument using the three exact source terminals
and the existing finite-dimensional upgrade. The displayed determinant product has no zero factor:
the two I-minus determinants are positive and det(B_u)≠0, so det(I−B)≠0 in ℝ. Apply
mathlib.isUnit_iff_ne_zero_g2 ONLY to this REAL scalar determinant, never to the endomorphism ring.
On the SAME actual finite free real tangent module E apply
mathlib.linearMap_isUnit_iff_isUnit_det_g2 to the underlying endomorphism L=I−B. Its BOTH
Module.Finite/Module.Free premises are the actual original-tangent instances just supplied above,
not target assumptions. It gives IsUnit L, hence a witnessing unit u in (E→ₗ[ℝ]E)ˣ with u.val=L. The
actual definition mathlib.linearMap_generalLinearGroup_toLinearEquiv_g2 supplies a linear
equivalence with forward map u.val=L and inverse u.inv, whose two inverse identities are the unit
identities. This does not equip End(E) with a GroupWithZero instance. The existing
mathlib.linearEquiv_toContinuousLinearEquiv upgrades this SAME equivalence on the original
finite-dimensional real normed tangent carrier, preserving both maps and the supplied norm; its
inverse is therefore a genuine bounded continuous linear inverse. For the displacement derivative in
the preceding local argument, transfer the equivalence through the derivative of the ORIGINAL smooth
chart and its already declared same-derivative conjugacy, then use the same finite-dimensional
upgrade in that chart's supplied real coordinate norm. No topological torus chart q, replacement
norm or positive-rank premise is used. The original tangent/norm, actual finite/free instances and
invariant-block sum conjugacy are now supplied here; the SAME original preferred-chart
derivative/remainder/inverse transport is supplied in Step13. Its protected Bredon/Dold local
fixed-pair application retains the named lower homology and local-degree prerequisites. These
inverse constructions allow rank0. This argument uses powers bounded by Cλ^k, not an unjustified
one-step bound ‖B_s‖<1. Zero-rank summands have determinant1; in particular the d=0 case has sign+1.

15. Lifted unstable orientation and common local sign
For n>0 the pullback cover P is homeomorphic to R^n, hence nonempty, connected, simply connected and
locally path connected; its smooth structure is only the original covering structure constructed in
the real pullback-atlas steps above. The lifted continuous expanding bundle has constant rank d on
connected P. Apply topo.real_vector_bundle_orientation_monodromy_g9 to the actual original pullback
p*E^u={(u,v):p(u)=π_E(v)}. Hatcher VBKT Proposition1.5 pp18–19 gives its original pulled-back local
frames (u,s_j(p(u))). The smooth covering derivative Dp_u identifies this bundle with the actual
lifted expanding bundle, whose local frames are (Dp_u)⁻¹s_j(p(u)); Hatcher Lemma1.1 p8 gives
continuity of this fibre-isomorphism inverse. The provider's simply-connected orientation conclusion
supplies a continuous fibre orientation on this bundle over P, using its native orientation covering
and section/frame equivalence; for d=0 take the canonical single empty-basis orientation. For every
lifted iterate F^m, p∘F^m=f^m∘p and mathlib.mfderiv_comp give Dp_(F^m u)∘DF^m_u=D(f^m)_(p(u))∘Dp_u.
Original splitting invariance and the inverse derivative give a continuous fibre-linear isomorphism
on this continuous expanding bundle covering F^m. The provider's comparison sign ε_m∈{±1} is
constant on connected P; it requires neither smoothness of the subbundle nor a global frame. ONLY at
a fixed point F^m u=u are source and target the SAME actual fibre, so in any pointwise basis this
sign is sign det(B_u). The previous determinant calculation gives the identical local index (−1)^d
ε_m at every fixed point. No orientation of the whole tangent manifold, global trivialization of
E^u, smoothness of E^u, or smoothness of Q is needed.

16. Published Dold commutativity and ENR index transfer, with the actual domains
Follow Dold1965(1.8), printed pp2–3, and the representation-independence proof(2.3), printed p3,
rather than the former Granas ANR detour. First take continuous a:U⊆R^N→R^N′ and b:U′⊆R^N′→R^N with
open domains. The composites ba and ab have domains E=U∩a⁻¹(U′), E′=U′∩b⁻¹(U). Their fixed sets are
homeomorphic under a,b: if ba(x)=x then y=a(x)∈E′ and ab(y)=y, and conversely. Suppose this fixed
set K is compact. On E×E′ define γ(x,y)=(b(y),a(x)). Its fixed set is the compact graph
{(x,a(x)):x∈K}. Dold’s first written homotopy γ_t(x,y)=(t ba(x)+(1−t)b(y),a(x)) has exactly this
same fixed graph for all t, because a fixed point has y=a(x) and then x=ba(x). At t=1 restrict the
map δ(x,y)=(ba(x),a(x)) on E×R^N′ to E×E′; the support graph lies in that smaller open domain, so
index restriction identifies its index with I(γ_1). The second written homotopy
δ_t(x,y)=(ba(x),(1−t)a(x)) has total fixed support the compact image of K×[0,1]. Dold1.7 gives
I(δ)=I(ba×0); Dold1.6 and1.4 give I(ba×0)=I(ba)·1. For the other equality use the two analogous
homotopies written on p3, keeping the original coordinate order: on E×E′ put γ′_t(x,y)=(b(y),t
ab(y)+(1−t)a(x)). A fixed point has x=b(y), so y=ab(y); the fixed graph is again {(x,a(x)):x∈K}. At
t=1 extend this map to δ′(x,y)=(b(y),ab(y)) on R^N×E′, and apply restriction to E×E′, which contains
the fixed graph. The homotopy δ′_t(x,y)=((1−t)b(y),ab(y)) has total fixed support {(
(1−t)b(y),y,t):y∈a(K),t∈[0,1]}, a compact image of a(K)×[0,1]. Its endpoint is 0×ab. Thus
Dold1.7/1.3/1.6/1.4 give I(γ)=I(0×ab)=1·I(ab), hence I(ba)=I(ab). This calculation does not
presuppose coordinate-swap or ENR conjugacy invariance. These are the source’s actual triangular
homotopies, and each compact-union guard is checked, with no compact-map or mutually invariant
neighborhood assumption. The two multiplicative endpoints invoke
topo.euclidean_fixed_point_index_basic_laws_g9, whose completed Stage1 D6a–D6d now supplies the
exact source foundation: Bredon’s natural bilinear integral relative cross product on the complement
pair, its open-pair agreement with Hatcher’s written simplex product, the positive point-product
sign in ordered coordinates, and Hatcher’s compact-support uniqueness to identify the product of
arbitrary supported orientation classes. Applying naturality to the two displacements and integral
bilinearity proves Dold1.6. Both products with the constant zero map have unit +1, including N=0 or
N′=0 by the ordinary H0 point convention. Hence the former integral support-product application gap
in these triangular homotopies is discharged at Stage1. All these conclusions remain relative to the
provider’s named lower ordinary homology proofs; no completed Lean proof is asserted. Now let X be
an ENR with two representations s:X→V,r:V→X and s′:X→V′,r′:V′→X, and f:W→X continuous on open W with
compact fixed set. In the preceding commutativity proof take U=D=r⁻¹(W), U′=V′, a=s′fr:D→V′,
b=sr′:V′→V. Then E=D (because a takes values in V′), E′=D′=r′⁻¹(W), ba=sfr and ab=s′fr′. Their fixed
sets are precisely sK and s′K, both compact. Thus the indices of the two retracted maps agree
exactly as in Dold2.3; no condition f(W)⊆W is needed. Excision supplies independence of smaller
isolating neighborhoods. For a homeomorphism h:X→Y choose the representation of Y as
s_Y=sh⁻¹,r_Y=hr; its retracted conjugate equals sfr, so local and global ENR index conjugacy
invariance follows without differentiating h. Apply this to the intrinsic cover P with
representation Q:P→R^n,Q⁻¹:R^n→P. To use an original smooth local chart near an isolated fixed
point, first restrict the local map to W=X′∩f⁻¹(X′), where X′ is the chart neighborhood; W is open
and contains the isolated support. Dold2.4 pp3–4 explicitly permits replacement by such an ENR
neighborhood of the compact fixed set. The chart and the restricted Q representation are then two
local representations of this same ENR neighborhood, so the preceding independence argument applies.
The topological Q transfers indices, never displacement derivatives. This substantive Dold
replacement removes the parent’s direct use of topo.enr_local_fixed_point_index_conjugacy_g9; that
shared node remains independently used beneath the global Dold theorem and is not deleted.

17. Bounded homotopy, finite localization and unique fixed lift
Write G(v)=A^m v+e(v) with ‖e(v)‖≤K. Hyperbolicity makes L=I−A^m invertible; choose a>0 with
‖Lv‖≥a‖v‖. For the straight homotopy H_t(v)=A^m v+(1−t)e(v), ‖v−H_t(v)‖≥a‖v‖−K, so all fixed points
for all t lie in the ball of radius K/a. Choose a strictly larger closed ball. The total fixed set
in this ball×[0,1] is closed by continuity, hence compact, and avoids its boundary; it is also
exactly the full fixed set in R^n×[0,1]. The original smooth local calculation shows fixed points of
F are isolated; under Q they form a discrete closed subset of that compact ball, and
mathlib.compact_discrete_finite_g8 makes the set finite. Using the source-replaced basic index
theorem topo.euclidean_fixed_point_index_basic_laws_g9, admissible-homotopy invariance gives total
I(G)=I(A^m), while the linear-degree child computes I(A^m)=sign det(I−A^m) with absolute value1.
Excision and finite additivity localize I(G) as the sum of its local indices. The preceding
published Dold ENR conjugacy/chart argument and the common-sign calculation identify each summand
with (−1)^d ε_m. Thus |I(G)| equals the number of fixed points and equals1. This is precisely the
index argument of Franks1969 Lemma1.2 pp118–119, applied to the intrinsic original-smooth cover; Q
remains solely topological. It closes the local derivative/linear normalization/orientation
reasoning, relative to the named G9 basic-index and linear-degree conclusions, the published Dold
commutativity/retraction argument above, and their own lower source prerequisites. Dold’s separate
global Lefschetz trace theorem is not needed in this bounded homotopy uniqueness calculation. It
does not close hyperbolicity, Markov or later classification steps.

18. Semiconjugacy without a standard source atlas
Given hyperbolicity and x0 from the independent published Franks/Dold fixed-lift existence step,
apply Franks Proposition (2.1), pp.70–71, through topo.franks_pi1_semiconjugacy to K=M, g=f,
basepoint x0, and translated q. Its compact-CW theorem gives h:M→T^n homotopic to q, h(x0)=0, and
h∘f=Abar∘h. For the pointed lifted maps it gives H:P→R^n with H∘F=A∘H, H(δ_z x)=H(x)+z, and H=Q−v
with v continuous, bounded and deck-invariant. For properness follow the actual finite-translates
argument of Franks1970 Lemma3.4 printed pp75–76/PDF84–85 on these ORIGINAL topological cover
objects, without its later asserted surjectivity. Let u0 be the pointed lift, so H(u0)=0, and write
v0=Q(u0); do NOT assume v0=0. Let J=v0+[0,1]^n in the canonical real coordinate space and D=Q^−1(J).
This finite-dimensional closed cube is compact (closed and bounded inside a compact Euclidean closed
ball), and Q^−1 is continuous, so D is compact and contains u0. Its integer translates cover P,
because the integer translates of J cover R^n coordinatewise and Q(δ_z x)=Q(x)+z. Only compactness
and this covering property of the SOURCE domain are used. Put K=H(D). It is compact by continuity
and contains0. It is NOT asserted to be a target fundamental domain, regular closed, or to cover the
target by its translates; no onto conclusion is used to obtain it.
For a compact target set B⊂R^n, the empty case gives empty compact inverse image. Otherwise choose
r>0 with B⊂B_r(0), and a finite Δ≥diam K. Choose t>r+Δ. If (K+z)∩B is nonempty, choose k∈K with
k+z∈B. Since0∈K and target deck translations are Euclidean isometries,
||z||≤||z−(k+z)||+||k+z||=||k||+||k+z||≤Δ+r<t. This is precisely Franks's printed
basepoint/diameter/translate-intersection inequality; boundedness of the correction v is not its
input.
Use the compact CLOSED target ball closedBall(0,t): Franks defines B_t as open on p75 but calls it
compact on p76, so that literal open-ball compactness claim is not repeated. The canonical target
covering fibre p0^−1({p0(0)}) is CLOSED, since p0 is continuous into the Hausdorff canonical torus,
and has the discrete induced topology by its covering sheets. Its intersection with closedBall(0,t)
is compact by the closed-subset-of-compact leaf and discrete in that same induced topology;
compact_discrete_finite_g8 makes it finite. The earlier canonical fibre calculation identifies each
fibre point with a UNIQUE integer vector z. Hence T={z:(K+z)∩B≠∅} is finite, since its injective
orbit image lies in that finite compact-fibre intersection. This is Franks's covering-orbit
finiteness step, not a new lattice counting or bounded-correction proof.
If H(x)∈B, choose z and d∈D with x=δ_z d from the SOURCE translated-domain covering. The unchanged
equivariance gives H(x)=H(d)+z, so z∈T. Therefore H^−1(B)⊂⋃_(z∈T)δ_z(D). Each δ_z(D) is compact by
continuity of the original deck homeomorphism, and the exact existing Set.Finite.isCompact_biUnion
leaf makes this finite union compact (also when T is empty). B is closed in Euclidean R^n, so
H^−1(B) is closed by continuity. The exact closed-subset-of-compact leaf now makes H^−1(B) compact.
Thus H is proper. For n=0 both canonical real space and connected P are singletons, the deck group
is trivial and every inverse image of a compact set is empty or a singleton; use this direct case
rather than a positive-radius sphere or nonzero deck label. This source application requires no
properness of p, differentiability of Q, lifted homotopy-equivalence→onto assertion, or metric
transport through Q. For surjectivity use directly the written supported-index definitions and
homotopy proof of Dold1965 §§1.2–1.4 printed p1 and §1.7 p2, through
topo.euclidean_fixed_point_index_basic_laws_g9. First, if n=0, R^0 and P are singletons under Q, so
H and the projected h are onto directly. For n>0 choose C≥0 with ||v(x)||≤C for every x∈P. Fix ANY
target y∈R^n and put G_y(w)=y+v(Q^−1(w)) on the OPEN domain U=R^n. The original Q^−1 is used only as
a continuous homeomorphism. Continuity of v and Q^−1, followed by addition, gives continuity of G_y
by mathlib.continuous_comp and mathlib.continuous_add_g8. Define Ψ(w,t)=t G_y(w) for (w,t)∈U×[0,1].
Its joint continuity is the exact mathlib.continuous_smul binding. For EVERY fixed pair w=Ψ(w,t),
||w||=t||G_y(w)||≤||y||+C. Choose R>||y||+C. The equality locus Z={(w,t)∈U×[0,1]:Ψ(w,t)=w} is closed
by mathlib.isClosed_eq_g8, and lies in closedBall(0,R)×[0,1]. This product is compact: the actual
original coordinate R^n and R are finite-dimensional proper real spaces, the closed ball is compact,
[0,1] is the real closed ball of center1/2 and radius1/2 with its induced compact topology, and
mathlib.isCompact_prod applies. Thus mathlib.isCompact_of_isClosed_subset makes the ENTIRE joint
fixed set Z compact. This verifies compactness of one joint carrier, not merely compactness of each
time slice. Its projection J⊂U is compact by mathlib.isCompact_image_of_continuousOn, contains every
endpoint fixed set, and equals the union of all time-t fixed sets. The endpoint supports are compact
as well: their equality loci are closed and are contained in the same compact closedBall(0,R).

Follow Dold1.3/1.7 on this SAME common support. For w∉J the displacement w−tG_y(w) is nonzero for
every t, so these continuous displacements give a homotopy of the single pair (U,U\J) into
(R^n,R^n\{0}). The printed support-enlargement formula1.3 computes each endpoint index by applying
its displacement-induced map to the ONE oriented support class o_(U,J). The printed homotopy
proof1.7 identifies the two endpoint induced maps, hence I(G_y,U)=I(0,U). Dold1.4 gives I(0,U)=1
because the constant value0 belongs to U. If G_y had empty fixed support, Dold1.2's empty-support
index would instead be0, a contradiction. There is therefore w with w=y+v(Q^−1(w)), and the ORIGINAL
identity H=Q−v gives H(Q^−1(w))=w−v(Q^−1(w))=y. As y was arbitrary, H is onto R^n. For any target
class ybar∈T^n choose y with p0(y)=ybar, using the surjectivity of the canonical target QUOTIENT
covering p0. Then the original lift equation h∘p=p0∘H gives h(p(Q^−1(w)))=ybar, so h is onto. No
self-map of a closed ball, differentiability of Q, isolated fixed points, determinant sign or
unique-fixed-lift theorem is needed for this argument. Franks1969 Lemma1.2 pp118–119 writes the
bounded-support homotopy ALGORITHM for a different, narrow Anosov-lift theorem. That theorem is not
applied to G_y: the displayed constant-comparison family, uniform bound and compact-support
verification are the explicit source-omitted APPLICATION of Dold's actual written
support-class/homotopy argument. Neither Franks Proposition2.1 nor its later asserted onto
conclusion is cited as printing this G_y application. Franks Theorem (2.2), pp.71–74, uses the same
compact-CW source generality for an infranil target; its Lie-group machinery is unnecessary for this
abelian target.

19. Full nonwandering set on the original smooth source
For the fixed-count contradiction in this paragraph, work on the characteristic connected smooth
orientation cover B already constructed, with its lifted f_B and an onto semiconjugacy h_B furnished
by the same pointed compact-CW construction; temporarily denote these by M,f,h. This is essential: a
nonorientable unstable bundle on the original M does not justify N_m(f)=|L(f^m)| there. Manning
Lemmas3–4 p427 allow a compact smooth source distinct from the algebraic target. For the
semiconjugacy h above, suppose a periodic target orbit is disjoint from h(NW(f)). Its full preimage
is a nonempty compact invariant source set K. A forward orbit in K has an accumulation point y∈K;
any neighborhood of y contains two sufficiently separated orbit visits and therefore a positive
return, so y∈NW(f), a contradiction. Here is the target periodic-density input, following the
written finite-grid proof of Ha–Kim–Lee2010 Lemma2.2 printed pp2–3 and Corollary2.3 p3, specialized
to the integral automorphism A∈GL(n,Z). For each positive integer k, define C_k⊆T^n as the image of
the finite type Fin n→Fin k under a↦p0((a_i/k)_i), using the canonical product quotient p0 from
Step0 and real casts of the integers. The finite-product instance and finite-image theorem make C_k
finite, including n=0. Every vector of integers divided by k has its image in C_k: replace each
numerator by its residue modulo k, whose difference is a multiple of k, hence changes the real
vector by an integer deck vector and leaves its p0-image unchanged. Since both A and its inverse
B∈GL(n,Z) have integer entries, multiplying any such vector by either matrix again gives integer
numerators over the same k. Thus Abar and Bbar preserve C_k; their matrix inverse identities descend
through p0 and make their restrictions mutually inverse. On the actual finite subtype C_k, use
Equiv.ofBijective to form the permutation σ_k whose forward map is precisely Abar restricted to C_k.
Classical decidable equality and the finite subtype supply the hypotheses of fintypePerm. Set
m_k=orderOf σ_k. The finite permutation group is left-cancellative, so orderOf_pos gives m_k>0, and
pow_orderOf_eq_one gives σ_k^m_k=id. For every natural j, evaluation of permutation powers is the
j-fold iterate of the forward map: prove this by induction, using that permutation multiplication is
composition and its identity is the identity function. Inclusion of the subtype commutes with σ_k
and Abar, and induction therefore gives Abar^j(x)=x for j=m_k and every x∈C_k. Hence every point of
C_k is periodic, with a genuine positive period, rather than only eventually periodic. This is the
published grid/permutation argument; the literal GL(n,Z) hypothesis supplies an integral inverse, so
the source’s more general determinant-coprimality and finite-index calculation is unnecessary here.

Every rational vector in R^n belongs to one of these grids after projection: choose positive integer
denominators for its finitely many coordinates and their finite product k; rewrite each coordinate
with denominator k and then reduce the integer numerator modulo k. For n=0 the empty denominator
product is1, the torus and C_1 are singletons and their unique point is fixed. To spell out the
density abbreviated in Ha–Kim–Lee Corollary2.3, let O⊆T^n be a nonempty open set. The canonical p0
is a continuous surjective open quotient map by Step0, so p0⁻¹(O) is a nonempty open subset of the
finite product R^n. At a chosen point of that preimage the product topology supplies a basic finite
product neighborhood contained in it. In each real coordinate choose a smaller interval with
rational endpoints using Real.isTopologicalBasis_Ioo_rat, and choose a rational strictly between
those endpoints using exists_rat_btwn. The finite coordinate choices give a rational vector in
p0⁻¹(O); its image lies in O and in some C_k and is periodic by the preceding argument. In n=0 the
sole point is in every nonempty open set. Thus the target periodic points are dense on precisely the
canonical torus; no new source smoothness assumption, hyperbolicity input, ergodicity inference or
classification theorem is used for this density argument. Since NW(f) is closed in compact M,
h(NW(f)) is compact and hence closed in the Hausdorff target. The preceding periodic-orbit preimage
argument puts every target periodic point in h(NW(f)), so density gives h(NW(f))=T^n. Apply the
named open dynamics.smale_original_anosov_spectral_basins_g7 at the exact original-smooth Anosov
hypotheses to obtain finitely many locally maximal transitive hyperbolic basic sets, relative to its
geometric prerequisites. Apply dynamics.mane_linear_toral_ergodicity_transitivity_g1 to this target
integral matrix: its previously required hyperbolicity implies that no eigenvalue is a root of
unity, since every root of unity has modulus1. The source child proves Haar ergodicity and supplies
a dense forward orbit on the canonical target torus, with no assumption on the source smooth
structure. Then choose that target point with dense forward (hence full) orbit and a preimage in
NW(f); the source basic set Λ1 containing this preimage maps onto the target by compactness and
covariance. Conditional on the orientation-cover Lefschetz count N_m(f)=N_m(g), if NW(f) is proper,
that spectral/basin theorem gives at least two basic sets. Indeed if there were only Λ1, its forward
and backward basins would each equal M and their intersection would equal Λ1, forcing NW(f)=M. Hence
another nonempty basic set exists and contains a periodic point by the theorem’s componentwise
periodic-density assertion; no separate no-cycle assumption is added. For one period q this makes
#Fix(f^q|Λ1)<#Fix(f^q)=#Fix(g^q), hence there is z∈Fix(g^q) omitted from h(Fix(f^q|Λ1)). Apply
topo.manning_original_smooth_periodic_fibre_g7 to Λ1,h,g,z,q. It gives a periodic x∈Λ1 with h(x)=z;
since z is omitted from the same-period image, y=f^q x differs from x and h(y)=z. Choose r≥1
divisible by q and by a period of x, so x,y and z are fixed for f^r,f^r,g^r respectively. Here the
same-lift step is explicit. Choose u over x, v over y; alter v by an integer deck translate so
H(v)=H(u)=w, using the integer difference of their H-images. Let F_r be the lift of f^r fixing u.
The maps H∘F_r and A^r∘H are lifts of the same target map and their difference is a constant integer
c; evaluation at u gives c=w−A^r w. Since y is fixed, F_r(v)=δ_d(v) for some integer d. Evaluate H:
H(F_rv)=H(v)+d=w+d, whereas A^rH(v)+c=w. Thus d=0 and F_r fixes the two distinct u,v. The preceding
bounded-homotopy/index argument applies to this lift because its Q-coordinate action is A^r plus a
bounded deck-periodic correction, giving the contradiction. No source group translations,
differentiability of q, fibre injectivity, or period-q lifting are used. The argument therefore
gives full nonwandering set and dense periodic points on B, conditional on the stated spectral/count
inputs. Projecting these periodic points through the finite continuous onto smooth covering gives
dense periodic points on the original M (the preimage of any nonempty open set is nonempty open),
hence the original NW(f)=M. No orientation of the original unstable bundle is silently assumed.

20. Global products of the original lifted foliations
Apply g9.hps_anosov_global_lamination directly to the ORIGINAL smooth real M,f and input Riemannian
metric, with the unchanged invariant splitting and all-n estimates. It supplies connected native
intrinsic smooth injectively immersed stable/unstable leaves j:L→M, their intrinsic open plaque
charts b:V→L, coherent state derivatives, original-f transport and the exact downstairs
forward/backward asymptotic membership criteria. No Hermitian input, global Euclidean leaf
parametrization or transverse smoothness is required.

CONSTRUCT THE SELECTED NATIVE LIFTED CARRIER through x∈P using the original Step3 smooth cover
p:P→M. For the downstairs leaf L through p(x), form C_L={(ℓ,z)∈L×P:j(ℓ)=p(z)} with the PRODUCT of
the native intrinsic L topology and the existing P topology, then its subspace topology. At every
actual plaque chart b and evenly covered open U⊂M, restrict to the intrinsic OPEN set b⁻¹(j⁻¹(U)).
For an actual sheet W over U, Lee2003 Lemma2.10 pp41–42 supplies the smooth inverse section s_W:U→W
from Step3. The lifted chart is v↦(b(v),s_W(j(b(v)))); its inverse is the native coordinate b⁻¹ of
the first projection. Thus C_L→L is locally a covering and its chart map into the EXISTING P is
s_W∘j∘b. Smoothness is the written local-section composition of Lee2.13 p44 applied to the actual
smooth native immersion, not a new ambient-subspace leaf structure. On actual connected pointed
overlaps, two such continuous lifts of the SAME j∘b agree by Hatcher AT Proposition1.34 p62 and
mathlib.isCoveringMap_eqOn_of_comp_eqOn; using the original downstairs chart transition gives the
literal lifted transition. There is no arbitrary common global sheet or equality inferred from
ambient leaf membership alone. The carrier is locally path connected in these intrinsic charts. Its
PATHCOMPONENT through the marked (ℓ_x,x) is intrinsically open, connected and smooth; take its image
under the second projection, with this transported native topology, as the selected lifted leaf
through x. Since j is injective, that projection is injective. The chart derivatives satisfy
Dp∘D(s_W∘j∘b)=D(j∘b), so its tangent is the original lifted E^s or E^u and its tangent norm is the
ORIGINAL pullback gtilde norm. This does not assign the ambient subspace topology, define the leaf
by asymptotic membership, or assert global R^n leaf coordinates.

The ORIGINAL F and F⁻¹ carry THESE constructed charts and pathcomponents to the corresponding native
lifted charts and pathcomponents: p∘F=f∘p and the original native f leaf action give the projected
parametrization, and the actual image of the marked point selects its inverse-covering sheet. The
same pointed lift uniqueness on connected intrinsic overlaps proves agreement, and the inverse
equation gives the inverse transport. In pullback pairs the map is (ℓ,z)↦(f_L(ℓ),F(z)) with inverse
(f_L⁻¹(ℓ),F⁻¹(z)). For any existing deck homeomorphism δ and its inverse, p∘δ=p gives the analogous
(ℓ,z)↦(ℓ,δ(z)) transport, with the same pointed-sheet argument. Therefore transport/invariance of
THESE selected continuation pathcomponents is source-covered; identification with any different
historical maximal-leaf model or a separate receiving germ in the later global tail is not assumed.

For two endpoints in a selected connected native smooth lifted stable leaf, choose ONE finite
intrinsic piecewise-SMOOTH path by the written reachable-set argument of Lee2003 Lemma6.17
pp139–140. The reachable set is nonempty and open by appending a straight coordinate segment, and is
closed by the same coordinate-ball concatenation at a closure point. Thus connectedness gives such a
finite path without completeness of the intrinsic leaf or smoothing a C¹ path. Each smooth piece has
an extension near its closed interval. Compose its native immersion into P with F^k. The unchanged
ORIGINAL gtilde derivative estimate gives speed at most Cλ^k times the original speed on each piece;
integrate and sum the finitely many pieces. The selected Petersen ambient distance of Steps7–8 is
DEFINED as the infimum of these finite piecewise-SMOOTH path lengths, so endpoint distance is at
most this particular length and tends to0. The inverse-time argument is identical on a selected
unstable leaf. The separate intrinsic d_L remains its original piecewise-C¹ infimum: no equality
with that infimum or a C¹ ambient riemannianEDist is used.

UNIFORM SAME-FIBRE SEPARATION in this ORIGINAL metric follows from the actual Petersen proof, not an
orbit-local graph capture. Corollary5.5.2 pp157–158 applies to K=M compact and the original smooth
g. Its proof obtains, near each base point, a local diffeomorphism domain for the total exponential;
a local linear frame and continuity of g compare the original fibre-norm balls with a fixed frame
ball. A finite subcover gives one R>0 for which exp_m:B(0,R)⊂T_mM→M is a diffeomorphism onto its
image for EVERY m∈M. Choose e=R/2>0 strictly. Step8's Petersen Proposition5.6.3 p164 already
supplies all-time geodesics upstairs by lifting the complete base geodesics. For every u∈P,
Proposition5.6.1(2) p163 gives p(exp_u v)=exp_(p(u))(Dp_u v), and Dp_u is the original norm
isometry. The right side is a diffeomorphism on B(0,R); hence exp_u is injective there, is a local
diffeomorphism and is a diffeomorphism onto its open image. Theorem5.5.4 pp158–159 applies to BOTH
original metrics: Gauss's radial norm1 identity gives length at least radial distance for curves
staying in the exponential domain; a first exit costs at least the radius, while a radial curve
supplies the opposite inequality. Consequently these exponential images on B(0,e) are precisely the
actual ambient metric balls, for the SAME finite piecewise-SMOOTH infimum used in Steps7–8. Thus
p:B_P(u,e)→B_M(p(u),e) is a diffeomorphism for EVERY u, as in the individual-ball argument of
Lemma5.6.4 pp164–165. In particular p(u)=p(v) and d_P(u,v)<e imply u=v, since both lie in B_P(u,e).
No compactness of an upstairs ball or complete intrinsic leaf metric is assumed; n=0 is the earlier
connected singleton branch.

CONVERSE ON THE SELECTED NATIVE LIFTED LEAVES. Suppose d_P(F^k x,F^k z)→0. A projected finite
piecewise-smooth path has exactly the same length because p is the original smooth local isometry.
Taking infima gives d_M(p(a),p(b))≤d_P(a,b), the written Petersen5.6.1(3) distance comparison. Hence
the projected orbits are asymptotic and the original g9 downstairs criterion puts p(z) in the native
stable leaf L through p(x). Lee6.17 gives a finite intrinsic piecewise-SMOOTH path γ in L from ℓ_x
to ℓ_z, with j(ℓ_z)=p(z). Apply mathlib.covering_exists_path_lifts to j∘γ marked at x. Hatcher AT
Theorem1.7 pp30–31 gives its concrete finite evenly-covered subdivision and unique pointed lift Γ.
Refine this subdivision by ALL smooth breakpoints of γ. On each closed subinterval, Γ=s_W∘j∘γ in the
actual selected sheet; since γ's smooth piece extends near that interval and the receiving U is
OPEN, shrink that extension inside U. The lift is therefore the SAME finite piecewise-SMOOTH path,
with no derivative required at junctions. The continuous pair (γ,Γ) is a path in C_L from (ℓ_x,x),
so z′=Γ(1) belongs to the SELECTED native lifted pathcomponent and p(z′)=p(z).
The preceding original derivative/length estimate yields d_P(F^k x,F^k z′)≤Cλ^k length(Γ)→0. The
triangle inequality with the assumed asymptotic relation gives d_P(F^k z,F^k z′)→0. The covering
equations imply p(F^k z)=p(F^k z′) for every k. Uniform e therefore forces F^k z=F^k z′ for all
sufficiently large k, and the ORIGINAL diffeomorphism F is bijective, so z=z′. Apply the SAME proof
to F⁻¹ and the unstable splitting for the backward converse. Thus the images of these selected
native lifted pathcomponents have exactly the upstairs asymptotic membership criterion. Franks1970
Proposition1.4 p66 prints the same-fibre/asymptotic/uniform-e late-equality mechanism for
injectivity of a leaf restriction. The full converse here is the HUMAN COMPOSITE of native g9
membership, Lee/Hatcher smooth path lifting, Petersen uniform separation and that Franks mechanism;
it is not the literal theorem of Proposition1.4 or the narrower Euclidean-leaf theorem1.1. The
printed final distance in Proposition1.4 repeats x; its two-point argument is read as the pair x,y.
DIRECT H UNIFORM CONTINUITY on the ORIGINAL lifted Riemannian metric, not on a metric transported
through Q. Follow ONLY the written small-scale inverse-ball composition and modulus estimate of
Pilgrim–Thurston2026 Lemma2.8 printed987, with the two actual small-ball inputs bound below. Its
full compact-CW/pullback-length theorem and large-scale geodesic subdivision are not applied
wholesale. Here h:M→T^n is the existing continuous semiconjugacy, p0∘H=h∘p, and HF=AH; h need not be
a homeomorphism and no inverse of H is used.

Bind the target to the EXISTING canonical T^n=Fin n→UnitAddCircle of Step0. In E=Fin n→R with its
existing norm, let D be the coordinate integer translation subgroup. The actual Step0 continuous
open quotient p0 has p0(v)=p0(w) iff v−w∈D. mathlib.isQuotientMap_homeomorph_g8 therefore identifies
its kernel quotient, equivalently the additive quotient E/D, homeomorphically with that SAME native
T^n, by [v]↦p0(v). This puts the canonical quotient-norm metric on the already given torus topology;
it changes neither the target carrier/topology nor the ORIGINAL metric on M or P. D is discrete by
the Step0 coordinate integer cover and its finite product, hence closed by
mathlib.add_subgroup_closed_of_discrete_g8. The quotient norm is thus separated. Lang Length
Spaces4.1(1),(3) printed11–12 supplies the written orbit-distance and proper free translation
local-cover argument. Choose η>0 with ||d||≥η for every nonzero d∈D; discreteness at0 gives this
uniform lattice gap. Translates of B(v,η/4) are disjoint, so the norm translations satisfy Lang's
proper/free local condition. For ρ=η/8 and ||w−v||<ρ, every nonzero translate satisfies
||w−v+d||≥η−||w−v||>||w−v||. Consequently the quotient distance from p0(v) to p0(w) equals ||w−v||
on this SAME centered ball. The strict quotient-representative lemma
mathlib.quotient_add_group_exists_norm_mk_lt_g2 gives p0(B(v,t))=B_T(p0(v),t) for 0<t≤ρ: choose a
representative with norm less than the quotient norm plus an error smaller than t minus that norm.
Together with the open quotient and disjoint translates this gives the actual inverse
s_v:B_T(p0(v),ρ)→B_E(v,ρ), continuous and satisfying ||s_v(z)−v||=d_T(z,p0(v)). Only this centered
identity is needed, not an unproved all-pairs isometry on a larger ball. In dimension0 both spaces
are singletons and the argument is direct; no nonzero lattice vector or positive rank is assumed
there.

The native prefix already supplies a UNIFORM original normal radius e>0 with p:B_P(a,e)→B_M(p(a),e)
a smooth inverse-sheet homeomorphism and d_M(p(a),p(b))=d_P(a,b) for b in this centered ball.
Smaller positive balls are preconnected: the original exponential chart identifies them with the
image of a convex tangent norm ball, using mathlib.convex_ball, mathlib.convex_isPreconnected and
mathlib.isPreconnected_image. This is the original geodesic/exponential construction, not a chart
derived by differentiating q or Q. For ε>0, compact ORIGINAL M and continuity of h give a uniform
δ>0, chosen δ<e, such that d_M(x,y)<δ implies d_T(h(x),h(y))<min(ε,ρ/2). The precise existing inputs
are mathlib.isCompact_uniformContinuousAt_of_continuousAt_g2 with K=M and the target metric
entourage, and mathlib.metric_mem_uniformity_dist; compactness uses the ORIGINAL Riemannian topology
already identified in Steps7–8. For each a∈P, both H and s_{H(a)}∘h∘p are continuous lifts through
the EXISTING p0 on the preconnected ball B_P(a,δ), and agree at a. Their projections agree; the
original covering and mathlib.isCoveringMap_eqOn_of_comp_eqOn give equality on this ball. Hence for
d_P(a,b)<δ,
||H(b)−H(a)||=d_T(h(p(b)),h(p(a)))<ε.
The same δ works for every a. mathlib.metric_uniformContinuous_iff now gives uniform continuity of H
from the original lifted metric to the existing norm on E. This is precisely the source's
small-scale inverse-ball/modulus mechanism with the actual source and receiver balls; it requires no
global regularity of q/Q, no smooth h, no uniform continuity of Q or H^{-1}, and no new
identification of length/C1-infimum metrics.

FULL-DECAY AFFINE LEAF INCLUSIONS, INTO only. Apply the exact source export
linear.hyperbolic_decay_space_complement_g9 to this hyperbolic real A on E: S={v:A^n v→0},
U={v:A^(−n)v→0} are complementary. This is the full decay-space statement proved in Alves2014
Definition5.4 printed15 and Theorem5.5 written16–17; no proof-private characterization or fresh
spectral converse is imported from linear.hyperbolic_real_splitting. For b in the SAME selected
native stable leaf of a, the prefix's finite intrinsic smooth-path estimate already gives
d_P(F^n(a),F^n(b))→0. Uniform continuity of H and HF=AH give A^n(H(b)−H(a))→0, hence H(b)−H(a)∈S by
its literal definition. The analogous native unstable path under F^{-n} gives H(b)−H(a)∈U. Thus
H(s(a))⊂H(a)+S and H(u(a))⊂H(a)+U for THESE original native pathcomponent leaves. This asserts no
leafwise surjectivity/injectivity, no block rate and no Euclidean parametrization of a native leaf.
Define ambient linear projections ΠS and ΠU from the source complement.
mathlib.submodule_projectionOnto_comp_subtype_g8 and
mathlib.submodule_projectionOnto_comp_subtype_eq_zero_g8 give their identity/zero restrictions;
mathlib.submodule_projection_add_projection_eq_self_g8 gives ΠS+ΠU=id;
mathlib.linear_map_continuous_finite_dimension_g8 gives their continuity in this actual
finite-dimensional real E. These are the actual linear relations used in the continuation below,
independent of any adapted-norm operator estimate.

These native charts, transport and converse do not prove intersections of arbitrary opposite lifted
leaves or identify arbitrary different maximal-leaf models. Conditional on ORIGINAL Step19 dense
Per(f) and Step17 fixed-lift uniqueness, the source sequence component below reduces two
intersections to a marked homoclinic compact K and constructs a distinct periodic point by a cyclic
splice, contradicting uniqueness. This bypasses the separate lifted nonwandering/periodic-density
route. For existence, saturate a fixed stable leaf by unstable leaves. For the LOCAL bracket/product
component, instantiate g9 directly with this original arbitrary REAL smooth M,f, its SAME original
Riemannian metric g and the given all-n hyperbolic splitting/estimates. Use only its public
original-f source-selected native intrinsic-open smooth plaque parametrizations, compatible
unbranched boxes, jointly continuous coordinate values/FIRST disc derivatives and enlarged local
embedding domains. No complex surface, Hermitian premise, whole complex stable_foliations theorem or
global Euclidean leaf model is used. The following inlines the already written real human-source
ALGORITHM used in G4 SF27/G8: Glöckner2007v2 Theorem5.3/Remark5.6 pp41–43 and5.10(a–c) pp45–46,
Fisher–Hasselblatt12.5.18p602/12.1.3pp578–579, then Shub1987 Proposition10.10pp126–127. Their whole
differently scoped geometric theorems are not imported as premises. The selected native lifted
pathcomponents, their smooth sheet charts and transport, and their asymptotic membership converse
are now supplied by the source composite above. Identification with arbitrary different historical
maximal-leaf models or a separate global-tail receiving germ and the remaining global classification
applications retain their boundaries; the at-most-one conclusion below is conditional on
Step19/Step17 inputs.

Fix an upstairs point p̃₀ and use the EXISTING Step3 evenly covered O around its base point p₀ and
smooth inverse sheet s_W:O→W⊂P. Choose the ORIGINAL base ambient chart below inside O. Write 𝒫 for
the local CENTER neighborhood to distinguish it from the already constructed total covering space P.
For each σ∈{s,u}, the g9 public native family supplies a fixed real finite-dimensional model and
genuine intrinsic-open original leaf embeddings. Their native inverses and tangencies are actual
source data. All coordinate-state derivatives and finite-order regularity below are on these
parametrizations; no differentiability in the center is assumed. Set d_s=rank_R Eˢ,d_u=rank_R Eᵘ.
The SAME original source metric, smooth map and all-n estimates are retained, not a transferred
smooth torus structure.

First handle zero ranks before any inverse operator-norm reciprocal. If d_s=0, native stable charts
are points and native unstable charts have full ambient rank. Apply the following SAME Glöckner
fixed-projection/common-image argument to that ONE positive full-rank family: its fixed derivative
is invertible, its jointly continuous first disc derivatives give the common two-point bound, and
the common ellipsoid lies in every selected chart image for all centers in a smaller 𝒫. Shrink 𝒫
inside that ellipsoid, so every retained center p lies in every retained unstable chart through q.
The fixed-state inverse theorem supplies state regularity there. Set B(p,q)=p (stable point through
p meets that unstable chart through q). The ordered product F(s,u)=B(u,s) on {p₀}×D_u is u, with
inverse (p₀,u). If d_u=0 apply the SAME common-image argument ONLY to the positive full-rank stable
family and restrict all centers inside its common ellipsoid; the roles reverse, giving B(p,q)=q and
F(s,p₀)=s on D_s×{p₀}. These are direct local singleton/full-chart products, with no division by the
zero operator norm. If both ranks vanish, n=0; the connected M homeomorphic to T⁰ is a singleton, so
its local product and the selected covering-sheet product are that singleton. This parent is
nonempty because Tⁿ is nonempty, so no empty-center branch is needed. No reciprocal or positive
unit-sphere estimate is used on a zero factor. For the remaining proof assume both d_s,d_u>0; each
fixed projection derivative is an isomorphism in its own positive rank, with different dimensions
allowed between the two families.
Fix a reference center p₀ and choose the original ambient smooth chart c centered at p₀, so
c(p₀)=(0,0), with the complementary reference stable and unstable tangent planes as its coordinate
planes. This is a translation and fixed linear coordinate change of an original smooth chart, not
transport of the smooth structure. Treat each plaque family separately. Write Φ^σ_p for the native
smooth plaque parametrization supplied by g9.hps_anosov_global_lamination public native finite-C¹
family output, and π for the fixed projection of the ambient chart onto that family's reference
tangent plane, identified with its fixed real model ℝ^d_σ. Set q(p,v)=π(c(Φ^σ(p,v))). This uses
those SAME native plaque parametrizations, not a new leaf or a normal tube. The public API supplies
one common OPEN embedding domain B(0,R_σ), joint values and FIRST disc-parameter derivatives, and
one ambient chart containing all these values after local restriction. Take a closed inner model
disc and a still smaller common OPEN model ball B=ball_ℝ^d_σ(0,r) inside that disc and the enlarged
embedding domain, and an open neighborhood 𝒫 of p₀ inside U_σ. Restrict these genuine center/disc
domains so their original values remain inside the chosen ambient chart and Step3 evenly covered O;
joint value continuity at (p₀,0) provides this ordinary local restriction. Use the fixed original
Euclidean norms on both reference stable and unstable real models ℝ^d_s,ℝ^d_u throughout; no
adaptation of the original Riemannian metric is made. Only the v variable is differentiated.
At (p₀,0), the smooth embedding Φ^σ_p₀ has injective derivative of real rank d_σ. Its image is
exactly E^σ_p₀ because it is a native chart in the supplier's leaf tangent to E^σ. The ambient
derivative D c is an isomorphism, and π restricts to an isomorphism on D c(E^σ_p₀). Therefore ONE
fixed A=D_vq(p₀,0):ℝ^d_σ→ℝ^d_σ is invertible. This requires no equality of D_vΦ with a separately
chosen frame map. Put 0<σ<||A⁻¹||⁻¹, for example σ=||A⁻¹||⁻¹/2. Joint first disc-parameter
derivative continuity from g9.hps_anosov_global_lamination public native finite-C¹ family output
permits restriction of 𝒫 and r, still inside the SAME native open disc/chart, so ||D_vq(p,v)−A||≤σ
for every (p,v)∈𝒫×B. This is the ordinary product-neighborhood restriction at (p₀,0) of an already
jointly continuous finite-dimensional derivative, not a new compact-tube or whole-core construction.
For y,z∈B the closed segment y+t(z−y), 0≤t≤1, lies in the open convex B. Apply the existing real
segment derivative estimate to h(t)=q(p,y+t(z−y))−tA(z−y): the chain/subtraction/linear derivative
rules give h′(t)=(D_vq(p,y+t(z−y))−A)(z−y), of norm≤σ||z−y||. The ambient state derivatives restrict
to derivativeWithin on Icc(0,1), including both endpoints. Hence ||q(p,z)−q(p,y)−A(z−y)||≤σ||z−y||
for every p,y,z. For y=z this is zero; for distinct points it is exactly the uniform two-point bound
(72) with supremum at most σ<||A⁻¹||⁻¹.
The parameter 𝒫 is merely topological. Joint continuity of q and the preceding common-ball/fixed-A
bound meet Glöckner Theorem5.10(a)–(c), printed pp.45–46; follow its actual proof through
Theorem5.3/Remark5.6, pp.41–43. Put κ=σ||A⁻¹||<1 and α=1−κ>0. The triangle inequality applied after
A⁻¹ gives ||q_p(z)−q_p(y)||≥(||A⁻¹||⁻¹−σ)||z−y||. Thus q_p is injective and its inverse on the image
is Lipschitz with constant (||A⁻¹||⁻¹−σ)⁻¹. For y∈B and 0<s≤r−||y||, let c_*∈q_p(y)+A(ball(0,αs)).
Choose 0<t<1 with ||A⁻¹(c_*−q_p(y))||<tαs. The closed ball D=closedBall(y,ts) is strictly inside B.
It is nonempty and complete: ℝ^d_σ is complete by the existing finite-dimensional completeness leaf;
an ambient limit of a Cauchy sequence in D remains in D by continuity of the norm. On D set
T(v)=v−A⁻¹(q_p(v)−c_*). The two-point bound gives Lip(T)≤κ and
||T(v)−y||≤κ||v−y||+||A⁻¹(c_*−q_p(y))||≤κts+tαs=ts. Apply g9.mathlib_contracting_exists_fixedPoint
to the induced self-map on this complete nonempty D, using its actual MapsTo bound, κ<1 and the
finite original distance from starting point y to its image. The distinguished
ContractingWith.fixedPoint is fixed by mathlib.contracting_fixedPoint_isFixedPt_g10, and
mathlib.contracting_fixedPoint_unique_g10 identifies it with the existed fixed point/Picard limit.
Thus the fixed-point identity is used only after actual existence; the source closed-ball proof does
not assume an unknown solution. Its fixed point v satisfies q_p(v)=c_* and ||v−y||≤ts<s, so it lies
in the OPEN ball ball(y,s). This is the source's strictly interior closed-ball contraction proof of
equation(66): q_p(y)+A(ball(0,αs))⊂q_p(ball(y,s)). It proves openness of q_p(B); together with
injectivity and the inverse bound this makes q_p:B→q_p(B) a homeomorphism.
Now take an arbitrary (p,w) in W=⋃_(p∈𝒫){p}×q_p(B), with y=q_p⁻¹(w). For any sufficiently small ε>0
with ε≤r−||y||, continuity of q at the fixed y gives an open neighborhood Q of p with
||A⁻¹(q_q(y)−w)||<αε/2 for q∈Q. Equation(66) then implies Q×(w+A(ball(0,αε/2)))⊂W; every inverse
there lies in ball(y,ε). Thus W is open and ψ(p,w)=q_p⁻¹(w) is jointly continuous on W, exactly the
argument written on pp.45–46. Consequently (p,v)↦(p,q_p(v)) is a homeomorphism 𝒫×B→W with inverse
(p,w)↦(p,ψ(p,w)). This is the inverse of those SAME restrictions, not a separately chosen local
branch. In particular equation(66) at y=0,s=r gives q_p(0)+A(ball(0,αr))⊂q_p(B). Shrink 𝒫 once more
so ||A⁻¹(q_p(0)−q_p₀(0))||<αr/2. Then the fixed reference-centered ellipsoid
V=q_p₀(0)+A(ball(0,αr/2)) lies in every q_p(B), by the triangle inequality. It contains an ordinary
Euclidean ball about q_p₀(0) of any positive radius smaller than αr/(2||A⁻¹||). This is the local
image-shift argument actually written on p.46, not a global inverse core. On 𝒫×V, c(Φ^σ(p,ψ(p,w)))
is a jointly continuous regraph of the original chart plaque with π-coordinate w. Apply this
independently to both families and intersect their center neighborhoods. Write L_s,L_u>0 for the
fixed inverse Lipschitz constants, π_s,π_u for the reference coordinate projections, and ψ^s,ψ^u for
the SAME continuous inverses. At (p₀,0) the transverse derivative of each native family is zero,
because its tangent is the corresponding reference coordinate plane. Joint FIRST disc-derivative
continuity allows restriction of the native convex balls and common OPEN center neighborhood 𝒫 so
||D_v(π_u cΦ^s_p)||≤η_s and ||D_v(π_s cΦ^u_p)||≤η_u throughout, with positive η_s,η_u chosen so
η_sL_s≤1/4 and η_uL_u≤1/4. No division by an actual zero slope occurs. The same segment estimate
makes these cross coordinates η_σ-Lipschitz on the native convex balls. Composing with ψ^σ gives
regraph slopes at most 1/4. No center derivative or metric adaptation is used.
After these restrictions choose ONE r>0 such that the projection balls B_s(0,2r),B_u(0,2r) lie in
the respective common ellipsoids and their closed radius-r cores lie strictly inside. Every ψ^σ(p,w)
for these projection balls lies in the SAME native convex ball where all derivative/image estimates
were proved. Define the stable graph U_p(x)=π_u cΦ^s_p(ψ^s(p,x)), x∈B_s(0,2r), and unstable graph
S_q(y)=π_s cΦ^u_q(ψ^u(q,y)), y∈B_u(0,2r). Their evaluations are jointly continuous. Their state
regularity is C¹ by the ORDINARY real implicit-function theorem: at each state the inverse Lipschitz
estimate implies ||D_vq_p h||≥L_σ⁻¹||h|| by difference quotients, hence this derivative is an
isomorphism in equal finite dimensions. Apply mathlib.contDiffAt_implicitFunction to q_p(v)−w with p
FIXED. Its equation and local uniqueness identify its C¹ solution with ψ^σ(p,·);
mathlib.contDiffAt_one_contDiffOn_nhds_g1 gives an open C¹ neighborhood at each state. This gives
pointwise state C¹ of the literal regraph, not center C¹ from Glöckner5.10.
Both regraph intercepts vanish at p₀. Joint continuity therefore permits shrinking 𝒫 so
||U_p(0)||<r/4 and ||S_p(0)||<r/4 for all p∈𝒫, and both coordinates of c(p) have norm<r/4. By
continuity at (p₀,0), retain the native center/domain products inside the original ambient chart and
the selected stable and unstable unbranched boxes. Each retained graph is a restriction of its
original intrinsically OPEN leaf chart, not a whole-leaf intersection with an ambient set. The boxes
keep the local plaque germs and transversals coherent. Other global-leaf returns are not substituted
for the selected sheets.
On the nonempty complete carrier D=closedBall_s(0,r), ||U_p(x)||<r/4+(1/4)r=r/2. Thus
U_p(D)⊂B_u(0,r/2)⊂B_u(0,2r), and Q_(p,q)=S_q∘U_p is defined on all D. Further
||Q_(p,q)(x)||<r/4+(1/4)(r/2)=3r/8<r, and Lip Q≤1/16. Hence Q(D)⊂B_s(0,3r/8)⊂int D. These are proved
common-domain/self-map margins on the SAME original localized plaques, with no extension to entire
Euclidean coordinate spaces.
Follow the written composition mechanism of Fisher–Hasselblatt Lemma12.5.18, printed p.602/PDF609:
stable-through-p/unstable-through-q intersection satisfies y=U_p(x), x=S_q(y), equivalently
x=Q_(p,q)(x). Apply the actual iterative proof of Proposition12.1.3, pp.578–579/PDF585–586, on this
verified complete carrier, and instantiate g9.mathlib_contracting_exists_fixedPoint with NNReal1/16
and the finite-distance start0; fixed-point identity and uniqueness are the same exact primitives
just bound above. Start x₀=0, set x_(n+1)=Q(x_n), and use ||x_m−x_n||≤(1/16)^n||x₁−x₀||/(1−1/16).
All iterates remain in D, so completeness gives a limit in D; continuity gives the fixed-point
identity, and the contraction inequality gives uniqueness. Set B(p,q)=c⁻¹(x_(p,q),U_p(x_(p,q))).
This is exactly the chosen STABLE plaque through p intersecting the chosen UNSTABLE plaque through
q, at strict interior coordinates. The printed lemma uses whole graphs; only its actual composition
proof is specialized here, after verifying the complete local self-map. No whole-space graph or new
cutoff is introduced. The source residual estimate ||x_t−x_t₀||≤(1−1/16)⁻¹||Q_t(x_t₀)−Q_t₀(x_t₀)||
gives joint continuity of B from joint evaluation. The center parameters lie in an original local
manifold chart, hence in a metric parameter space as the printed proposition requires. Its
differentiable-parameter clause is not used.
Before nested brackets, establish the exact intrinsic re-centering guard. Suppose two selected
stable regraphs, with BOTH centers in 𝒫, ACTUALLY meet at an interior projection coordinate. Their
meeting point belongs to the same injectively immersed intrinsic leaf because the leaves partition
M, and both graphs are intrinsically open leaf charts. Their intrinsic plaque germs at that ACTUAL
point therefore coincide. On the connected common projection ball B_s(0,2r) the set of x where their
U-values coincide is nonempty at that meeting, relatively closed by continuous evaluation, and open
by the coincident intrinsic germs and local projection-chart uniqueness. Convexity of the ball gives
preconnectedness by mathlib.convex_isPreconnected; hence the equality set is the whole ball. Repeat
for unstable graphs on B_u(0,2r). This proves equality of their common graph restrictions ONLY after
an actual meeting, not from membership in a global leaf or equality of a box label. The strict 3r/8
and r/2 intersection margins place the meetings below in those open projection domains. No globally
embedded-leaf or global-intersection uniqueness assertion is made.
Now follow Shub1987 Proposition10.10, printed pp.126–127/PDF139–140, central projections and open
preimages. Its local bracket existence/continuity assumption is supplied FIRST by the preceding
construction, so the theorem is not used circularly for existence. On 𝒫 define π^s(z)=B(p₀,z),
π^u(z)=B(z,p₀). Their targets are the central stable and unstable graph plaques respectively.
Continuity is INTRINSIC in those plaques: their ambient values are continuous, their fixed
projection coordinates are continuous, and the central graph/native inverse chart transports these
to the intrinsic topology. This is not identification with the topology of a whole ambient leaf
image. Since B(p₀,p₀)=p₀, continuity permits a smaller OPEN ambient neighborhood V of p₀ with
closure in 𝒫 and contained in the chosen O such that V and both projection images lie in 𝒫, with
their projection coordinates strictly inside the corresponding radius-r ball. Retain V in the two
original boxes. This is Shub's bracket-center control localized at p₀. All later centers and meeting
points belong to 𝒫; a local compact center restriction suffices, without a global radius assertion.
Choose connected intrinsic OPEN discs D_s,D_u through p₀ in the central stable and unstable graphs,
contained in V and the guarded projection cores. Joint continuity allows both discs to be small
enough that B(D_u,D_s)⊂V. Set F(s,u)=B(u,s). Thus the stable graph is U_u, the unstable graph S_s:
UNSTABLE through stable s meets STABLE through unstable u, exactly as stated. For z=F(s,u), the
unstable graphs centered at z and s ACTUALLY meet at z, and the stable graphs centered at z and u
ACTUALLY meet there. All centers lie in 𝒫, and all coordinates are interior. Re-centering identifies
their common graph restrictions. Since s is on the central stable graph and its own unstable graph,
uniqueness gives π^s(z)=s; since u is on its own stable graph and the central unstable graph,
uniqueness gives π^u(z)=u.
Conversely, let z∈V with s=π^s(z)∈D_s and u=π^u(z)∈D_u. The unstable graphs centered at s and z meet
AT s=B(p₀,z), and the stable graphs centered at u and z meet AT u=B(z,p₀). These are actual interior
meeting anchors with every center in 𝒫. Re-centering identifies the respective restrictions. The
center z itself has both coordinates of norm<r/4 and therefore belongs to the stable graph through u
and unstable graph through s on their common domains. Their unique intersection is z=F(s,u). These
prove BOTH literal inverse identities. Consequently F(D_s×D_u)=V∩(π^s)⁻¹(D_s)∩(π^u)⁻¹(D_u), an OPEN
neighborhood in the original manifold because both projections are continuous into their central
intrinsic plaques: mathlib.isOpen_preimage binds these preimages, and mathlib.metric_isOpen_ball
binds the earlier projection-ball and ambient-neighborhood restrictions. The literal inverse is
(π^s,π^u), so F is a homeomorphism onto this open set. This is the actual Shub open-preimage
mechanism, with SAME-sheet identities proved before use. The slices with u fixed lie on the selected
stable plaque through u, and the slices with s fixed on the selected unstable plaque through s. The
inverse restrictions give intrinsic local plaque charts on those slices. Stable is horizontal,
unstable vertical. The real derivative-to-segment computation above uses mathlib.hasFDerivAt_comp,
mathlib.hasFDerivAt_comp_hasDerivAt, mathlib.hasFDerivAt_sub and
mathlib.continuousLinearMap_hasFDerivAt on the actual coordinate maps and real segment; the existing
mathlib.norm_image_sub_le_of_norm_deriv_le_segment_prime then gives the two-point bound including
derivativeWithin at interval endpoints. Every closed local ball is complete in its ORIGINAL
finite-dimensional model: mathlib.finite_dimensional_complete supplies ambient completeness, and a
Cauchy limit stays in that closed ball by norm continuity. Compactness/properness of a Banach ball
is not assumed. State C¹ inverse certificates are the actual mathlib.contDiffAt_implicitFunction n=1
and mathlib.contDiffAt_one_contDiffOn_nhds_g1 on their open equation/uniqueness restrictions,
identifying the SAME continuous inverse. The closed/open equality-set argument uses
mathlib.convex_isPreconnected on the actual common convex projection ball; openness of the product
image uses mathlib.isOpen_preimage and mathlib.metric_isOpen_ball on those native domains.

REALIZE THIS LOCAL product on the existing P by ONE smooth covering sheet only. The selected base
image Ω=F(D_s×D_u) is open and lies in O after the above restrictions. Put D̃_s=s_W(D_s),
D̃_u=s_W(D_u), using the intrinsic plaque topologies transported through that selected native chart
and smooth inverse sheet, and define F̃(s̃,ũ)=s_W(F(p(s̃),p(ũ))). Its image is s_W(Ω), open in W
and hence in the EXISTING P topology. Its literal inverse is (s_W∘πs∘p,s_W∘πu∘p). The two base
product inverse identities and the already proved identities p∘s_W=id_O,s_W∘p=id_W give BOTH
upstairs inverse identities on these exact restrictions. The stable/unstable slices are the SAME
selected local lifted native germs, since their parametrizations are the original native
parametrizations composed with s_W; smoothness of this sheet was proved in Step3. This local chart
statement needs no identification with arbitrary maximal lifted leaves, no deck/orbit history
matching and no global opposite-leaf intersection. The selected native pathcomponent transport and
lifted-asymptotic converse above no longer need an orbit-local capture premise. Orbit-local ε
identification outside the chosen native chart domains, identification with arbitrary different
lifted models or separate global-tail receiving germs and finite intrinsic μ retain their precise
OPEN applicability boundaries. The new conditional sequence/cyclic-splice component below supplies
at-most-one for THESE selected native leaves relative to Step19/Step17 inputs; it bypasses the
independent homoclinic/NW and broad upstairs periodic-density routes. The written
parameter-square/global-product application remains conditional on those unchanged inputs and its
original native domain guards. The bracket orientation here is
B(p,q)=stable-through-p∩unstable-through-q and F(s,u)=B(u,s); no inverse orientation is silently
substituted. The chart-based local construction is complete ONE LEVEL relative to g9 and its named
lower suppliers. Current cutoff extension, Corollary5.4 and parameter-graph suppliers are ALL
source/split/complete at their OWN ONE LEVEL; their named lower dependencies and this consumer’s
global applicability guards remain independent/open. Finite-r cutoff fibre-jet guards are inherited
as supplied, not strengthened to ambient C^r T_f/G or a transversely C¹ foliation. This is one
conditional source CONSUMER integration, with no G4/G8/G3 mechanism-discovery or whole Franks
classification credit.

SOURCE PARTIAL: PERIODIC-BASE DOUBLE-INTERSECTION REDUCTION ONLY. Follow the FIRST paragraph of
Franks1969 Lemma1.5, printedp120/PDF4, on THESE original selected native lifted stable/unstable
leaves. Assume for contradiction that x≠y lie in S∩U. The empty/connected dimension0 case has no
such pair; if either foliation rank is zero its connected native leaf is a singleton, also excluding
such a pair. For the remaining case choose one of the genuine upstairs native local-product boxes
already constructed above about x, and restrict its two factors so its image N is an OPEN
neighborhood of x with closure not containing y. This restriction is possible in the ORIGINAL P
metric: first choose a ball about x with closed radius strictly less than d_P(x,y), then restrict
the continuous local product inside that ball. No new global leaf-intersection map, compact leaf or
ambient leaf-subspace topology is asserted.

Write Sat_s(N)={z∈P:Lˢ_z∩N≠∅} and Sat_u(N)={z∈P:Lᵘ_z∩N≠∅}. Expand Franks's cited elementary
foliation property on the ACTUAL native product boxes. In such a box h:D_s×D_t→Ω with stable plaques
h(D_s×{t}), the partial stable saturation of an ambient OPEN A is h(D_s×pr_t(h⁻¹(A∩Ω))). The
preimage is open in the product, its coordinate projection is open, and h is the original box
homeomorphism; hence this partial saturation is OPEN in Ω and in P. For the unstable direction
interchange the factors/projections. Starting with N, take the union of these partial saturations
over ALL boxes, include the previous set, and repeat finitely many times; the union over all finite
stages is open. It is exactly the full selected-leaf saturation: every stage stays in the same
native leaf, and in a fixed connected native leaf the equivalence classes generated by finite chains
of these open plaque pieces are intrinsically open. Their complements are unions of such classes and
are intrinsically open as well. Connectedness of that native leaf gives only one class, so every
point on a leaf meeting N is reached by a finite chain. Thus Sat_s(N) and Sat_u(N) are genuinely
ambient OPEN. This is the finite plaque-chain expansion of the source's “basic properties of
foliations,” not an alternate global product or unique-intersection proof.

Both saturations contain y because their leaves meet N at x. Since y is outside closure(N), the set
O=(Sat_s(N)∩Sat_u(N))\closure(N) is a nonempty OPEN neighborhood of y. Its openness is precisely
mathlib.isOpen_sdiff_g8, applied to the open intersection and the closed closure. Use the
conditional ORIGINAL downstairs density Per(f)⊂M from Step19; this remains conditional on that
step's spectral/count and other named inputs and is not a new target hypothesis or an assertion of
upstairs periodic density. The ORIGINAL covering p:P→M is open:
mathlib.isCoveringMap_isLocalHomeomorph_g2 applied to Step3 makes this same p a local homeomorphism,
and its local inverse-sheet images show it is an open map. mathlib.dense_preimage_of_isOpenMap_g2
therefore makes p⁻¹(Per(f)) dense in the original P topology. Since O is nonempty open, choose y′∈O
with p(y′) periodic for ORIGINAL f.

The selected stable and unstable leaves through y′ both meet N. Choose a∈Lˢ_(y′)∩N and b∈Lᵘ_(y′)∩N.
In the ACTUAL full product coordinates on N, write a=h(s_a,t_a), b=h(s_b,t_b), with stable
coordinate plaques varying s and unstable coordinate plaques varying t. Recombine the two
coordinates to x′=h(s_b,t_a)∈N. It lies on the selected local stable plaque through a and the
selected local unstable plaque through b, hence on BOTH global selected leaves through y′.
Equivalently with the earlier stable-first bracket B, x′=B(a,b). Because y′∉closure(N), x′≠y′. We
have therefore reduced any initial double intersection to TWO distinct intersections x′,y′ whose
downstairs base point p(y′) is periodic. The chosen y′ is NOT asserted periodic for the fixed lift
F. HISTORICAL first-paragraph boundary: that preceding reduction alone supplies no marked lift or
homoclinic preparation. The separately installed next component now binds those two preparations;
nonwandering/closing and a unique-fixed-lift contradiction remain unsupplied.

BOUNDARY OF THE FIRST-PARAGRAPH SOURCE PARTIAL. That component installs only the periodic-base
reduction; its former exclusion of the marked-lift/homoclinic preparation is historical for the
subsequent new component only. Its conditional original Per(f)-density and actual native
local-product inputs are named above. The separate homoclinic→nonwandering, broad upstairs
periodic-density and Franks1970 D0 closed-cell/image-coverage/projection/stable-trapping routes are
not proved by this first-paragraph component; the later conditional sequence component bypasses them
for at-most-one. Step19/Step17 lower inputs, parameter-square native applicability and finite
intrinsic μ retain their exact conditions. The conditional written parameter-square component and
all preceding/following global proof text below are preserved, not discharged by this reduction.

SOURCE PARTIAL: MARKED LIFT, HOMOCLINIC ORBIT AND COMPACT HYPERBOLIC CARRIER ONLY. Continue the
marked-lift preparation in the SECOND paragraph of Franks1969 Lemma1.5, printedp120/PDF4, using the
x′≠y′ selected above. Let r≥1 be a genuine period of the ORIGINAL downstairs point p(y′), so
f^r(p(y′))=p(y′). Then F^r(y′) and y′ lie in the SAME original p-fibre. The regular universal-cover
deck action from Step3 is transitive on each fibre, so choose its actual deck transformation δ with
δ(F^r(y′))=y′, and set G=δ∘F^r. This is a smooth diffeomorphism of the EXISTING P and G(y′)=y′. The
original smooth deck and F/F⁻¹ native transport already proved above carry the selected lifted
stable/unstable leaves to their corresponding selected leaves; because G fixes y′, it preserves BOTH
selected leaves through y′. Their inverses are preserved as well. No new native atlas, different
maximal-leaf model or application of g9 to noncompact P is introduced. The
empty/dimension0/zero-rank double-intersection cases have already been excluded in the preceding
reduction.

Use the ORIGINAL pullback metric gtilde of Step6, with Dp an isometry in the actual source and
receiving fibres. The deck equation pδ=p and covering equation pF^r=f^r p give pG=f^r p. Induction
gives pG^n=f^(rn)p for every n≥0; applying the inverse equation gives pG⁻ⁿ=f^(−rn)p. One must NOT
replace G^n by δF^(rn): deck factors generally do not commute that way. Differentiate THESE actual
composition identities with mathlib.mfderiv_comp. For every z∈P,
 Dp_(G^n z) D(G^n)_z = D(f^(rn))_(p(z)) Dp_z,
and similarly with −n. The lifted original splitting is (Dp_z)⁻¹(Eˢ_(p(z)))⊕(Dp_z)⁻¹(Eᵘ_(p(z))).
These derivative identities prove its G-invariance and give the exact original-fibre estimates
 ||D(G^n)_z v_s||_gtilde ≤ C(λ^r)^n ||v_s||_gtilde,
 ||D(G⁻ⁿ)_z v_u||_gtilde ≤ C(λ^r)^n ||v_u||_gtilde
for every n≥0, since both Dp endpoint maps are isometries and the ORIGINAL downstairs all-n
estimates apply at rn. Here 0<λ^r<1 follows from r≥1 and 0<λ<1. The same identities hold at the
fixed point y′; no new metric or Anosov theorem on noncompact P is assumed. Step6 also gives δ an
isometry by differentiating pδ=p, consistent with this direct composition proof.

The two points y′,x′ lie in BOTH connected selected native smooth lifted leaves. Apply the already
installed Lee finite-piecewise-SMOOTH path argument separately in these two intrinsic leaves: choose
one such path γ_s from y′ to x′ in the stable leaf and one γ_u in the unstable leaf, each of finite
original gtilde length ℓ_s,ℓ_u. The actual G/inverse leaf restrictions are smooth and preserve these
selected leaves. For each smooth piece of γ_s, the preceding derivative estimate and the same
original norm-speed/chain-rule integration argument already installed above give
length_gtilde(G^n∘γ_s)≤C(λ^r)^nℓ_s after summing the finitely many pieces. Its endpoints are
G^n(y′)=y′ and G^n(x′); the ORIGINAL ambient finite-piecewise-SMOOTH distance is bounded by the
length of this explicit path. Hence d_P(G^n(x′),y′)≤C(λ^r)^nℓ_s→0. Reverse time with γ_u to obtain
d_P(G⁻ⁿ(x′),y′)≤C(λ^r)^nℓ_u→0. No derivative at a path junction, complete intrinsic leaf distance,
Euclidean leaf model, shadowing or new orbit-membership converse is used. Thus x′≠y′ is a homoclinic
point for THIS marked lift G fixing y′, by these actual two convergence statements; this is not
periodicity of y′ for the old F.

Set K={y′}∪{G^j(x′):j∈ℤ} in the ORIGINAL P topology and metric. It is compact by the elementary
convergent-tail open-cover proof: in an open cover of K choose a member containing y′; convergence
of BOTH tails puts all sufficiently positive and sufficiently negative orbit terms in that member.
Only finitely many middle terms remain, and one cover member per remaining term gives a finite
subcover. No properness, bounded-set compactness or compact nonempty ball is needed for this
argument. G and G⁻¹ shift the orbit and fix y′, so G(K)=K. Restrict the ORIGINAL continuous
complementary pullback splitting to K. It is invariant under DG by the displayed composition
identity, and the SAME uniform constants C and λ^r give all-n stable and inverse-unstable estimates
on K, including the fixed point. Consequently K is a compact invariant hyperbolic set for G with
respect to the SAME original gtilde. This is the explicit compact-carrier preparation for a
potential later closing argument, not an application of a closing theorem.

BOUNDARY OF THIS PREPARATION. Franks's marked lift and the two homoclinic convergence statements are
now bound on the original selected native leaves; the elementary compact K/invariant splitting
restriction is spelled out. This compact-K preparation alone makes no nonwandering/periodic/closing
or uniqueness assertion. The following independently written Merry sequence construction now
supplies one periodic point and the conditional at-most-one contradiction. The separate long-return
D0 closed-cell/image-coverage/projection/stable-trapping and broad upstairs periodic-density routes
are bypassed, not proved. Step19/Step17 named lower inputs, native parameter-square applicability
and finite intrinsic μ remain independent. All old conditional continuation text below keeps its
exact mathematical scope.

CONDITIONAL AT-MOST-ONE APPLICATION: MERRY AUTHOR-NOTE SEQUENCE ALGORITHM ON THE ORIGINAL COMPACT
CARRIER. Keep the marked smooth G=δ∘F^r, its fixed p_*=y′, the distinct homoclinic q=x′ and
K={p_*}∪Orb_G(q) just constructed. The ORIGINAL Step19 dense Per(f) conclusion used to reach this
configuration remains conditional on its original spectral/count inputs. Everything below is an
inline application of Merry, Sixty Lectures of Dynamical Systems(2020 AUTHOR NOTES), not an
application of his whole compact-manifold shadowing theorem to the noncompact P. It uses compact K
and the unchanged original gtilde exponential/distance, and gives a contradiction relative to the
Step17 fixed-lift index conclusion and its named lower inputs.

(1) ORIGINAL COMPACT-BASE ADAPTATION, BEFORE SEQUENCE NORMS. Put T=f^r on the original compact M and
μ=λ^r∈(0,1). Its original stable/inverse-unstable all-n bounds are Cμ^n; enlarge C to max(C,1) for
this auxiliary construction if necessary. Follow the finite-sum proof of Merry37.15,
PDF261–262/local37pp5–6: choose L_ad≥1 with Cμ^(L_ad)<1 and on the ORIGINAL full tangent set
 |v|_hat²=Σ_(j=0)^(L_ad−1)||D(T^j)v||_g²,  α=Σ_(j=0)^(L_ad−1)C²μ^(2j).
The j=0 term makes this a positive fibre inner-product norm; its coefficients are continuous in the
original frames. For v_s stable, shifting the finite sum gives |DT
v_s|_hat²=|v_s|_hat²−||v_s||_g²+||D(T^L_ad)v_s||_g²≤[1−(1−C²μ^(2L_ad))/α]|v_s|_hat². For v_u
unstable the source's reverse shift gives
|DT⁻¹v_u|_hat²=|v_u|_hat²+||DT⁻¹v_u||_g²−||D(T^(L_ad−1))v_u||_g². The original inverse bound at
T^(L_ad−1)x yields ||DT⁻¹v_u||_g≤Cμ^(L_ad)||D(T^(L_ad−1))v_u||_g, while applying the earlier inverse
bounds to each finite-sum term yields |v_u|_hat²≤α||D(T^(L_ad−1))v_u||_g². The SAME squared
contraction factor therefore works for the inverse unstable direction. Take its SQUARE ROOT
θ=sqrt(1−(1−C²μ^(2L_ad))/α)∈(0,1). The printed final line's unexplained exponent2m is read as the
chosen2L_ad, and its squared-norm factor requires this square root for a norm bound; these two
source notation slips are disclosed, not propagated.

Use Merry29.13/29.14 and38.1–38.2 to box-adjust by the ORIGINAL continuous splitting:
|v|_b=max(|v_s|_hat,|v_u|_hat). The stable DT and unstable DT⁻¹ bounds are≤θ. This continuous box
norm is an auxiliary fibre norm, NOT a Riemannian metric and NOT the metric used for exp/log or path
lengths. Continuous original projections, finite frame cores and compactness of the original base
give uniform constants 0<m_norm≤M_norm, with M_norm≥1, such that m_norm||v||_g≤|v|_b≤M_norm||v||_g;
compact unit-sphere/homogeneity proves both inequalities, and no global frame is chosen. Pull back
this norm/splitting by the ORIGINAL Dp isometries. Then the actual pG=T p identity gives one-step G
stable and inverse-unstable bounds≤θ in |·|_b on P. All comparisons still refer to the original
gtilde norm. The previously excluded zero-rank/dimension0 double intersection needs none of this
construction; connected original M has fixed ranks, or the same finite invariant rank pieces are
treated in their original local frames.

(2) GENUINE NEAR-GRAPH LINEAR PAIRS. On compact K choose a common OPEN original moving exp/log
neighborhood, with its inverse identities, using the original metric and the existing
local-addition/normal-ball construction. After shrinking, log_y(G exp_x(v)) is defined for all x,y∈K
with d_P(Gx,y)≤δ₀ and v in a common original fibre neighborhood. Its OWN derivative at v=0 is
 L_(x,y)=D(log_y)_(Gx)∘DG_x:T_xP→T_yP,
not DG_x with an unbound receiving fibre. It depends continuously on (x,y) in actual original
source/receiving frames; at y=Gx it is DG_x. Its inverse is continuous near that graph. Fix θ<λ_b<1
and ε_b>0 with λ_b+ε_b<1. At the exact graph the direct blocks in order(u,s) and inverse blocks in
order(s,u) are diagonal with inverse expanding-block and contracting-block norms≤θ and off-diagonal
blocks0. Compactness of the graph over K and finite original splitting frames allow δ₀>0 small
enough that BOTH direct and inverse maps have
 ||A⁻¹||,||D||<λ_b,  ||B||,||C||<ε_b.
For the direct A block, in matching finite frames it is a small perturbation of the original
invertible A₀; factor A=A₀(Id+A₀⁻¹(A−A₀)) and apply mathlib.isUnit_one_sub_of_norm_lt_one to the
negative error, using its norm<1 in the complete original endomorphism ring. This gives actual
invertibility BEFORE a bound on ||A⁻¹|| is used. Do the same for the inverse-order block. The
scalar/matrix operator continuity then gives the displayed strict bounds. All these constants are
fixed BEFORE the nonlinear derivative radius; no pointwise splitting, unidentified nearby fibres or
global frame is inferred.

(3) COHERENT TWO-SIDED LINEAR GRAPHS. Let (x_k)_(k∈ℤ) be ANY δ₀-pseudo-orbit in K and set
L_k=L_(x_k,x_(k+1)). Implement Merry38.5 PDF264–265/local38pp2–3 with its RECEIVING index, using the
full written31.9 PDF224–225 estimate. The carrier is bounded families Ψ_k:Eᵘ_(x_k)→L Eˢ_(x_k), with
original |·|_b operator norms≤1. Every real finite-dimensional fibre is complete;
mathlib.continuousLinearMap_instCompleteSpace binds the real/id semilinear operator-norm uniformity
and complete receiving fibre, and mathlib.lp_infty_banach_sup_norm_g4 gives completeness over the
arbitrary index ℤ. Norm≤1 is a closed constraint by the norm reverse-triangle inequality;
mathlib.isClosed_completeSpace_coe_g7 makes this CLOSED UNIT carrier complete. It contains zero, and
no compactness of ℤ or of an infinite-dimensional closed ball is used.

For these actual blocks define
 (XΨ)_(k+1)=(C_k+D_kΨ_k)(A_k+B_kΨ_k)⁻¹.
The inverse is a whole-fibre inverse: ||A_k⁻¹B_kΨ_k||<λ_bε_b<1 gives a Neumann unit, equivalently
the actual31.7 whole-fibre contraction argument. The source31.7 lower estimate gives
||(A_k+B_kΨ_k)⁻¹||≤τ, where τ=(1/λ_b−ε_b)⁻¹<1. Set r_*=(λ_b+ε_b)τ<1. Thus ||(XΨ)_(k+1)||≤r_*. The
FULL31.9 subtraction identity, with the same receiving index, is
 (XΨ)_(k+1)−(XΩ)_(k+1)=(D_k−(XΩ)_(k+1)B_k)(Ψ_k−Ω_k)(A_k+B_kΨ_k)⁻¹.
Its norm is≤(λ_b+ε_b)τ||Ψ_k−Ω_k||=r_*||Ψ_k−Ω_k||. Taking the genuine bounded-family supremum gives
self-mapping and a strict contraction. The existing g9.mathlib_contracting_exists_fixedPoint
supplies its unique fixed family; graph invariance is the fixed equation with the actual whole-fibre
inverse, so L_kΓᵘ_k=Γᵘ_(k+1), not merely an inclusion or independent pointwise graphs. Apply the
identical complete-carrier argument to L_k⁻¹ in order(s,u), shifted in the reverse direction,
obtaining Γˢ with L_kΓˢ_k=Γˢ_(k+1). Explicitly, write the barred blocks of
L_k⁻¹:T_(x_(k+1))P→T_(x_k)P in order(s,u); the reverse RECEIVING-index transform is
(YΞ)_k=(Cbar_k+Dbar_kΞ_(k+1))(Abar_k+Bbar_kΞ_(k+1))⁻¹. Its fixed equation gives L_k⁻¹Γˢ_(k+1)=Γˢ_k,
equivalently L_kΓˢ_k=Γˢ_(k+1). Both graph slopes are≤r_* and L_k expands Γᵘ_k by≥1/τ, while L_k⁻¹
expands Γˢ_(k+1) by≥1/τ. This is the source38.5 receiving-index algorithm on ℤ, not its compact-base
theorem or the unproved38.10 exercise.

(4) ONTO GRAPH SUM AND UNIFORM NEW NORMS. In the ORIGINAL splitting, the sum map from the two
graph-base coordinates to the actual tangent fibre is Id+R_k, where R_k has off-diagonal entries the
two graph slopes. Its |·|_b operator norm is≤r_*<1. The original fibre endomorphism ring is
complete, and mathlib.isUnit_one_sub_of_norm_lt_one applied to −R_k makes Id+R_k a UNIT, hence ONTO;
transversality alone would be insufficient. Merry31.7 PDF221–222 writes the corresponding
whole-fibre inverse argument, v↦w−R_kv, and its lower triangle estimate |(Id+R_k)v|_b≥(1−r_*)|v|_b.
Apply that estimate to the actual unit inverse: its norm is≤c=(1−r_*)⁻¹≥1. In the unique graph
decomposition v=v_u+v_s define |v|_k=max(|v_u|_b,|v_s|_b), with graph norms equal to their base
norms because the slopes are≤1. The graph-sum and inverse bounds give c⁻¹|v|_b≤|v|_k≤c|v|_b, using
1+r_*≤c. Its two projections Pᵘ_k,Pˢ_k have norm≤1, and the restrictions Lᵘ_k:Γᵘ_k→Γᵘ_(k+1),
Lˢ_k:Γˢ_k→Γˢ_(k+1) satisfy ||(Lᵘ_k)⁻¹||≤τ and ||Lˢ_k||≤τ. Completeness of each new fibre norm
follows from the actual finite-dimensional real normed-space theorem (or this equivalence). The
constants c,τ are UNIFORM and independent of the chain; the individual graph norms need not be
assumed periodic.

(5) UNIFORM NONLINEAR REMAINDER, WITH ITS OWN LINEARIZATION. For each actual close pair define
F_(x,y)(v)=log_y(G exp_x(v)) and Φ_(x,y)=F_(x,y)−L_(x,y)v. Then D_vΦ_(x,y)(0)=0 for EVERY pair,
although Φ_(x,y)(0)=log_y(Gx) can be nonzero. Follow the WRITTEN Merry39.7 PDF271/local39p3
compact-pair derivative/mean-value proof: the closed close-pair set in K×K is compact, original
exp/log and DG derivatives are jointly continuous on its common domain, and all zero-section
derivatives of Φ vanish. Choose β>0 so ℓ=c²β<1−τ. A common old |·|_b radius r_old>0 then bounds
||D_vΦ_(x,y)(v)||_old≤β for every pair and every |v|_b≤r_old, inside the actual exp/log domain. No
new norm is used to define this original smooth map. For two such vectors integrate its actual
derivative along the convex segment v+t(w−v), using the existing real-segment derivative bound leaf
and chain rule; this gives Lip_old Φ≤β. The comparison at BOTH endpoint fibres yields Lip_new
Φ_k≤c²β=ℓ. Choose a common CLOSED new radius R>0 with cR<r_old and inside the original
derivative/log uniqueness domain; then its whole segment stays in the OLD domain before applying
that estimate.

The ORIGINAL normal-ball/log-length identity gives ||log_y(Gx)||_gtilde=d_P(Gx,y) on the retained
small radius (an upper bound would suffice). Consequently |Φ_k(0)|_(k+1)≤c M_norm d_P(Gx_k,x_(k+1)).
For a final pseudo-orbit threshold δ_sh≤δ₀, put a₀=c M_norm δ_sh. Shrink it so a₀≤(1−τ−ℓ)R. All
derivative/graph constants and domains above were chosen BEFORE this last displacement threshold, so
there is no smallness circle. For any prescribed original-metric error η>0 it can further be chosen
so [c/m_norm]a₀/(1−τ−ℓ)<η. Original exp at a vector has radial length its original norm on this
normal domain, giving the corresponding actual ambient distance bound; no box norm or sequence norm
is called a Riemannian distance.

(6) ACTUAL SECTION FIXED POINT AND TRUE ORBIT. Use the dependent lp∞ carrier of bounded
σ_k∈(T_(x_k)P,|·|_k), closed by ||σ||∞≤R. Each receiving fibre is complete, the generic dependent
lp∞ leaf applies, the norm constraint is closed, and the existing closed-subtype-complete leaf makes
Γ_R complete. Zero belongs, with finite displacement. Implement the FULL written Merry39.8
PDF272–274 and44.13 PDF298/reference299 component equations:
 (X_sσ)_k=Lˢ_(k−1)σˢ_(k−1)+Pˢ_k Φ_(k−1)(σ_(k−1)),
 (X_uσ)_k=(Lᵘ_k)⁻¹[σᵘ_(k+1)−Pᵘ_(k+1)Φ_k(σ_k)].
Every summand has the indicated receiving fibre; no forward/inverse index is suppressed. The stable
difference is bounded by (τ+ℓ)||σ−ζ||∞, and the unstable difference by τ(1+ℓ)||σ−ζ||∞≤(τ+ℓ)||σ−ζ||∞.
The new box norm therefore gives contraction factor τ+ℓ<1. Since ||X0||∞≤a₀, the bound a₀+(τ+ℓ)R≤R
gives MapsTo Γ_R. The existing contracting-exists-fixedPoint leaf now supplies an ACTUAL unique σ,
not merely a chosen fixed-point property. At it, ||σ||∞≤a₀+(τ+ℓ)||σ||∞, hence ||σ||∞≤a₀/(1−τ−ℓ).

Rearranging the two component fixed equations gives σ_(k+1)=L_kσ_k+Φ_k(σ_k)=F_(x_k,x_(k+1))(σ_k).
Both vectors lie in the ORIGINAL inverse-exp domains; their exact inverse identities give
G(exp_(x_k)σ_k)=exp_(x_(k+1))σ_(k+1). Since G is a diffeomorphism, the points form its TRUE
two-sided orbit through z=exp_(x_0)σ_0. The preceding radial-length and norm comparisons give
d_P(G^kz,x_k)≤(c/m_norm)||σ||∞<η for ALL integers k. Thus this source sequence construction shadows
every sufficiently small chain in compact K; it has not invoked a whole compact-manifold theorem on
P.

(7) FIXED ORIGINAL UNIQUENESS RADIUS AND PERIODICITY. Choose ONE ν₀>0 below the common ORIGINAL log
radius and with c M_norm ν₀<R, independent of the chain and of any requested smaller error. Any true
orbit with d_P(G^kw,x_k)<ν₀ for every k has its ORIGINAL logs σ^w_k=log_(x_k)(G^kw) in the SAME Γ_R,
because |σ^w_k|_k≤c M_normν₀<R. The exact orbit equations make it a fixed section of the SAME
operator X. Uniqueness on Γ_R proves w=z. This uses the original uniform comparison, not periodicity
of the graph norm. For a periodic chain of period m≥1, choose the constructed error η≤ν₀ with a
strict bound as above. The orbit of G^mz also has d_P(G^k(G^mz),x_k)=d_P(G^(k+m)z,x_(k+m))<η≤ν₀. Its
logs therefore enter the SAME Γ_R even if that norm family was not identified with its m-shift.
Uniqueness gives G^mz=z. This is exactly the WRITTEN Merry45.1 PDF301 uniqueness/shift proof; no
unproved compact-P periodic-density theorem is used.

(8) WRITTEN CYCLIC HOMOCLINIC SPLICE AND INDEX CONTRADICTION. Use Merry48.3's closing proof
PDF325–326 only as its literal cyclic-splice mechanism; no theorem about two DISTINCT hyperbolic
fixed points or inclination lemma is applied. Here p_* is the single marked fixed point and q≠p_*
has BOTH tails converging to it. Choose η≤ν₀ with η<d_P(q,p_*)/3 and the corresponding δ_sh>0
from(5)–(7). Choose k≥1 so G^kq and G⁻kq are both within δ_sh/3 of p_*. The finite string
G⁻kq,G^(−k+1)q,…,G^(k−1)q, repeated periodically, is a δ_sh-chain in K: every step is exact except
its closing jump, whose error d_P(G^kq,G⁻kq)<2δ_sh/3<δ_sh. Cyclically index it so x_0=q. The
preceding ACTUAL section construction and shift uniqueness give a periodic point z with G^mz=z for
some m=2k≥1 and d_P(z,q)<η. Hence z≠p_*. G^m also fixes p_* and is an ORIGINAL smooth lift of f^(rm)
by the actual iterated covering identity. The Step17 fixed-lift index conclusion, with its original
splitting/orientation/local-index and named lower prerequisites, applies to this lift just as to any
other lift of that original iterate and allows exactly one fixed point. It contradicts these two
distinct points. No false power formula for the deck factor, new smooth structure on a toral target
or independent global periodic-density claim is used.

Therefore, CONDITIONAL on ORIGINAL Step19 dense Per(f) and Step17 fixed-lift uniqueness with their
unchanged named lower inputs, ANY two THESE selected native opposite leaves have AT MOST ONE
intersection. The local product alone never proved this. The subsequent parameter-square algorithm
may consume this conditional conclusion; it no longer has an independent unproved at-most-one
premise. This route BYPASSES, rather than proves, the separate homoclinic→NW/upstairs
periodic-density argument, Franks1970 D0 long-return
closed-cell/image-coverage/projection/stable-trapping and FH inclination route. Step19
spectral/count/cyclic obligations, other native-model/receiving-germ applications, finite intrinsic
μ and whole original-smooth classification remain OPEN.

CONDITIONAL written PARAMETER-SQUARE CONTINUATION: Franks1969 Lemma1.6 printed120–122 and
Corollary1.7 printed122. Use the just established conditional at-most-one conclusion for THESE
original selected native stable/unstable leaves, relative to ORIGINAL Step19 dense Per(f), Step17
fixed-lift uniqueness and their unchanged named lower inputs. It is proved by the preceding
sequence/cyclic-splice source component, not by a local bracket or an independently assumed global
theorem. The native connected carriers, lifted transport, local product charts, direct H uniform
continuity/INTO linear relations and properness of H are already bound above and in Step18. No
global intersection map is presupposed.

Fix a stable leaf s and put Q_s={x:u(x)∩s≠∅}. This saturation is open by the retained native local
products. If w∈closure(Q_s), Franks's initial local-product projection gives x∈Q_s∩s(w) arbitrarily
close to w: project a nearby point of Q_s along its local unstable plaque to the stable plaque
through w, keeping its unstable leaf and hence its membership in Q_s. Let y be the unique point
u(x)∩s. Choose finite intrinsic continuous paths γ:[0,1]→u(x) from x to y and ρ:[0,1]→s(x)=s(w) from
x to w; the native connected smooth carrier and existing Lee6.17 paths supply these, without
Euclidean leaf coordinates. Attempt θ(r,t)=s(γ(r))∩u(ρ(t)) only WHERE this intersection exists. The
axes θ(r,0)=γ(r) and θ(0,t)=ρ(t) exist. The at-most-one premise makes every local continuation agree
with any previously defined value. The retained local product and intrinsic chart continuity
therefore give an open relative domain of existence and continuous θ there. Follow Franks's
filled-strip supremum τ=sup{t:θ exists on [0,1]×[0,t]}, then the top-edge supremum r0=sup{r:θ exists
on [0,r]×{τ}}. This is a construction from the axes by local continuation, not use of a global θ
before it is proved to exist.

For every defined (r,t), the actual INTO relations give ΠU H(θ(r,t))=ΠU H(γ(r)) and ΠS H(θ(r,t))=ΠS
H(ρ(t)): θ lies in the stable leaf through γ and the unstable leaf through ρ, and the opposite
projections vanish on S and U. Therefore H(θ(r,t)) belongs to the compact set K={ΠU H(γ(r))+ΠS
H(ρ(t)):r,t∈[0,1]}. The existing compact-product/image and continuous-add APIs apply to these SAME
continuous paths and projections. Properness of the original H from Step18 confines all defined
values to the compact subset H^{-1}(K) of the EXISTING P. No compact intrinsic ball, finite μ,
smooth Q, norm transported through Q, or properness of an infinite-dimensional ball is used.

Here is the actual SIDE/CORNER extension in Franks printed121, rather than an assertion that ambient
compactness alone gives a leaf-valued corner limit. Choose an increasing approach (r_n,t_n) from the
filled domain to (r0,τ), with θ(r_n,t_n)→v after a compact subsequence. Select a native product
neighborhood N of v and a fixed earlier (r1,t1) whose value a=θ(r1,t1) is in N; shrink to its strict
product core as in the retained local construction. The local stable/unstable brackets with a and
θ(r_n,t_n), and global AT-MOST-ONE intersection, identify the two side values
θ(r1,t_n)=B(a,θ(r_n,t_n)) and θ(r_n,t1)=B(θ(r_n,t_n),a), where B(p,q)=s(p)∩u(q) is the convention
fixed above. Hence these sides converge respectively to B(a,v) and B(v,a), defining θ(r1,τ) and
θ(r0,t1) inside N. Now for ANY defined approach (r'_n,t'_n)→(r0,τ), continuity of the two fixed-side
continuations puts θ(r1,t'_n) and θ(r'_n,t1) in N eventually. Its local bracket is
θ(r'_n,t'_n)=B(θ(r'_n,t1),θ(r1,t'_n));
the equality again follows from the SAME leaf identities and the at-most-one premise, not from a
global holonomy or prior θ. Local bracket continuity gives the limit B(B(v,a),B(a,v))=v, using the
local product corner identities. This proves a unique continuous extension at the missing corner.
The source's axis/edge cases use the already defined axes or the corresponding one-sided interval;
the zero-dimensional case is the singleton. The same local product then extends past any unfinished
top-edge/strip supremum, so Franks's supremum argument reaches (1,1) and defines θ on the entire
parameter square. The actual visual Franks1969 PDFpp5–6, printedpp121–122, has '(r₀,t₀)' in BOTH the
corner and final sentence; t₀ is τ in the present notation. The extracted '(r0,r0)' is an OCR error
ONLY, not a printed-source typo or an additional diagonal restriction.

Now θ(1,1)∈s∩u(w), so Q_s is closed. Connectedness of the ORIGINAL P gives Q_s=P. Combined with the
preceding source-proved at-most-one conclusion CONDITIONAL on Step19/Step17 inputs, every opposite
native pair has exactly one intersection. Franks Corollary1.7 then uses fixed leaves u0,s0 and
Ψ(x)=(s(x)∩u0,u(x)∩s0). Its inverse is the opposite intersection of the two specified leaves. The
preceding continuation in native factor paths and the local product neighborhoods give continuity of
these projections/intersection inverse in the SAME intrinsic factor topologies; no Euclidean leaf
parametrization is needed for this product assertion. This is the printed side/corner algorithm
applied conditionally to the already constructed original native data, not a whole standard-smooth
Franks theorem applied to M. ONLY the earlier unbound linear-image/compact-confinement and
parameter-square sketch is superseded by these written components. Original Step19
spectral/count/cyclic/density and Step17 index/local-sign lower prerequisites remain conditional;
the at-most-one conclusion is no longer a separate missing theorem. The sequence route bypasses the
independent NW/closing/D0/inclination applications without certifying them or whole classification.
The next finite equal-H intrinsic bound is supplied by the conditional original-native source
application in Step21, relative to these same Step20/Step19/Step17 inputs and named lower guards.

21. Conditional finite equal-H intrinsic bound on original native leaves
GUARDED SINGLE-NATIVE-PLAQUE LENGTH BOUND, separate from the global μ claim below. Use the g9 native
finite-C¹ family Φ:U×B_E(0,R)→M, for one original stable or unstable foliation and its actual
finite-dimensional REAL normed model E. Fix compact C⊂U and 0<r<R, with D=closedBall_E(0,r), such
that ALL Φ(C×D) lie in ONE original smooth ambient coordinate domain and ONE evenly covered open O
for the original smooth covering p:P→M. Choose ONE existing smooth inverse sheet s_W:O→W. Define
ψ(a,v)=s_W(Φ(a,v)) ONLY on the actual OPEN preimage of O and the coordinate domain inside
U×B_E(0,R); no lift of the whole enlarged B_R through this sheet is asserted. The compact core lies
in this open domain. At fixed a these are the selected lifted native plaque charts of the preceding
step: the marked center s_W(a) and native plaque paths select their original pullback-leaf
pathcomponent. Smooth-sheet composition gives smooth state parametrizations and jointly continuous
state derivatives in fixed original ambient tangent coordinates. Dp∘D_vψ=D_vΦ, and the ORIGINAL
gtilde=p*g makes their downstairs/upstairs tangent norms equal. No center, bracket, transversal or
holonomy derivative is used.

Follow ONLY Lee2003 Lemma11.19 p278/PDF294's written compact-unit-sphere upper-bound/homogeneity
calculation and Proposition11.20 p279/PDF295's coordinate-segment speed integration. This is a
direct application of those operative computations, not their entire metric-topology theorem or a
transverse local-boundedness theorem. Empty C gives a vacuous assertion; dim E=0 gives singleton
state discs and constant joins. Otherwise finite_dimensional_proper_real_g8, isCompact_sphere and
isCompact_closedBall make the NATIVE model unit sphere S_E and D compact; S_E is nonempty by
normalizing a nonzero vector. No Euclidean L² norm is identified with the native norm.
isCompact_prod makes (C×D)×S_E compact. continuous_clm_apply evaluates the jointly continuous
coordinate state derivative at e. With the original smooth tangent norm at its actual base ψ(a,v),
this makes N(a,v,e)=||D_vψ(a,v)e||_gtilde a continuous nonnegative scalar on that product.
isCompact_bddAbove_image supplies a real upper bound; enlarge it to B=max(1,|bound|)≥0. For nonzero
z∈E normalize e=(1/||z||)•z, using norm_smul on this real normed model. Linearity and the genuine
ORIGINAL inner-product tangent norm's absolute homogeneity give ||D_vψ(a,v)z||=||z||N(a,v,e)≤B||z||.
For z=0 the estimate is immediate. Metric homogeneity is not inferred from an arbitrary continuous
scalar function.

For a∈C and v,w∈D, norm-triangle convexity keeps ℓ(t)=v+t(w−v) in D for 0≤t≤1. Set κ(t) to the real
value of Set.projIcc 0 1 (zero_le_one) t and define GLOBAL γ:Real→P by γ(t)=ψ(a,v+κ(t)(w−v)). The
projection's actual interval membership puts EVERY evaluation in the same core/sheet domain.
set_projIcc_of_mem fixes endpoints and equals t on [0,1]. For t∈Ioo(0,1) the clamp equals the
identity on a neighborhood. The continuous affine ℓ is smooth by continuousAffineMap_contDiff and
has derivative w−v by the zero-remainder identity. In the original chart,
has_fderiv_at_congr_of_eventually_eq followed by mfderiv_comp identifies (mfderiv γ
t)(1)=D_vψ(a,ℓ(t))(w−v). Its original tangent ENorm is therefore≤ENNReal.ofReal(B||w−v||). No
endpoint derivative or global C¹ regularity of κ is asserted.

Apply manifold_path_elength_eq_lintegral_mfderiv_Ioo to this GLOBAL γ with the ORIGINAL gtilde
tangent ENorm. The open real interval Ioo(0,1) is measurable. set_lintegral_mono_prime bounds the
integral by the constant speed; setLIntegral_const and real.volume_Ioo give
pathELength≤ENNReal.ofReal(B||w−v||), whose upper bound is finite. On [0,1], γ is the SAME native
affine coordinate segment. Its compact image lies in the actual open plaque/sheet domain; the
enlarged native B_R supplies state smoothness, and openness at this fixed a gives a smooth extension
to a slightly larger parameter interval. Thus this restriction is a genuine intrinsic smooth, hence
piecewise-C¹, join. Under its native immersion and original pullback leaf metric its speed is
exactly the tangent speed just computed. Here is the explicit SAME-measure real-length bridge. Let
σ(t) be the ordinary ORIGINAL gtilde speed of the native affine smooth extension on an open interval
containing [0,1], totalized by0 elsewhere. Its actual speed is nonnegative and ContinuousOn
Icc(0,1). For μ=volume.restrict Icc(0,1), continuousOn_integrableOn_compact supplies Integrable σ μ:
the real source is Hausdorff, its open sets are measurable, this interval is compact and volume is
finite on compact sets. norm_nonneg gives μ-almost-everywhere nonnegativity.
measureTheory_ofReal_integral_eq_lintegral_ofReal identifies ofReal of the ORIGINAL ordinary segment
length ∫_(Icc0,1)σ with ∫⁻_(Icc0,1)ofReal(σ). The exact measure_restrict_Ioo_eq_restrict_Icc
specializes to real Lebesgue volume, which has null singletons, and rewrites the latter integral
over Ioo(0,1). On that measurable open interval the already proved derivative identity gives
pointwise equality of ofReal(σ) with the ENorm of (mfderiv γ t)(1). setLIntegral_congr_fun therefore
identifies their restricted lower integrals, and manifold_path_elength_eq_lintegral_mfderiv_Ioo
makes this integral the pathELength of the GLOBAL clamp γ. The established pathELength upper bound
yields ofReal of this ONE ordinary intrinsic admissible length≤ofReal(B||w−v||). With right operand
B||w−v||≥0, ennreal_ofReal_le_ofReal_iff gives real length≤B||w−v||. No equality of ambient and
intrinsic distance infima is asserted. The real set of admissible intrinsic piecewise-C¹ lengths is
bounded below by0; this same native segment is a member. csInf_le therefore binds the defining
Franks intrinsic infimum and gives
 d_(selected native leaf)(ψ(a,v),ψ(a,w))≤B||w−v||≤2Br.
The last inequality follows from ||v||,||w||≤r. For v=w the constant path gives0 directly. This
proves ONLY the guarded numerical single-plaque bound. It does not transport finite chains across
varying global leaves, identify arbitrary returning sheets, prove compactness of intrinsic balls, or
establish the global μ supremum.

HISTORICAL SOURCE ASSERTION AND CURRENT CONDITIONAL APPLICATION. Franks1969 §1.8 p122, after
Corollary1.7, introduces intrinsic balls B(u;r), B(s;r), their product-coordinate set D(r), and a
displayed supremum μ over same-leaf pairs in D(r). The printed paragraph treats that supremum as
finite without proving it. We retain that statement as a historical source assertion, and do NOT
prove or use finiteness of the D(r) supremum or compactness of intrinsic balls. Instead apply the
following written Munkres finite-subdivision/finite-open-neighborhood/finite-cover mechanisms and
Lee native length computations to the ORIGINAL P and the conditional global product Ψ already
constructed in Step20. This is a consumer source application on the original native data, not the
whole agent-written local-distance helper or a standard-Euclidean-cover theorem.

(A) BIND THE ACTUAL NATIVE CENTRAL BOXES. Fix one of Step20's original local product neighborhoods
N, restricted to its ONE original evenly covered chart O and smooth inverse section s_W. For the
unstable family let c_U:N→D_S be the actual intrinsic-continuous central stable projection from the
proved product inverse, and take an intrinsic smooth open chart u:T→D_S on that central stable
plaque. Use the SAME source-selected native plaque family and SAME projection regraph inverse q/ψ in
Step20: b(v,t)=s_W(Φ^u_(p(u(t)))(v)). Restrict the open parameter domains around the chosen center
so every b(v,t) stays in N, the original smooth sheet, the common regraph/state domains, and their
strict meeting cores. Here v is an original finite-dimensional unstable state coordinate; t
parametrizes the opposite central plaque, not a globally chosen frame. Let E_χ⊂N be the original
OPEN domain where the selected central projection and ambient coordinate are defined and the pair
(p(c_U(z)),π_u(c(p(z)))) belongs to the original q/ψ inverse domain. Define
χ(z)=ψ^u(p(c_U(z)),π_u(c(p(z)))) on E_χ, where c is Step20's ambient coordinate and π_u its fixed
unstable projection. The retained b-values lie in E_χ. The actual meeting-germ re-centering proved
in Step20 identifies the selected unstable restriction through z with the restriction through
c_U(z). Thus b(χ(z),u⁻¹(c_U(z)))=z, and the SAME q/ψ inverse gives χ(b(v,t))=v and c_U(b(v,t))=u(t).
These are both inverse identities, proved on these matched original restrictions before using the
box. Consequently, after choosing state/transverse open domains V,T within them, its image is
exactly {z∈E_χ:c_U(z)∈u(T), χ(z)∈V}. This is OPEN, since the central projection, ambient projection
and SAME ψ are continuous. Hence b is a homeomorphism onto that original open box.
For each fixed t, v↦b(v,t) is the ORIGINAL intrinsic smooth plaque inclusion/immersion. Its state
derivative is supplied by g9's jointly continuous state jet and the original smooth sheet, with
Dp∘D_vb=D_vΦ^u. It follows that its original pullback-metric speed is exactly the speed used in the
guarded prefix. No derivative of ψ, c_U, the bracket, holonomy or a transverse parameter is taken.
Moreover b(0,t)=u(t) lies on ONE selected opposite central leaf. Interchanging stable and unstable
gives the other family. All restrictions are native intrinsic-open charts, not the ambient-subspace
topology of a whole leaf. A zero state rank contributes singleton plaques and zero joins; a zero
transverse rank contributes the unique transverse coordinate. No zero reciprocal is used.

(B) FINITELY MANY ORIGINAL CORES ALONG ONE NATIVE PATH. Fix x,y on the same selected global unstable
leaf U. Lee2003 Lemma6.17 pp139–140 supplies a finite intrinsic piecewise-smooth path γ from x to y,
by its explicit coordinate-segment/connected reachable-set proof. Use the native boxes from (A)
along γ, with concentric longitudinal balls whose CLOSED outer core remains in the state domain and
transverse closed coordinate cores whose INTERIORS contain the relevant central labels. The closures
lie in finite-dimensional coordinate domains, so are compact; all original sheet, meeting and
derivative domains are retained. These cores and all associated derivative bounds are chosen BEFORE
moving the endpoints or anchors. The inverse images of their inner open boxes cover the compact
parameter interval. Apply the CLOSED-subinterval subdivision used in Munkres Lemma54.1 p342/PDF359,
justified there by Lemma27.5 pp175–176/PDF192–193: choose 0=t_0<⋯<t_m=1 so each γ([t_(j−1),t_j])
lies in one chosen inner box, refining the finite smooth breakpoints if necessary. Put p_j=γ(t_j).
The closed subpath, not only its endpoints, lies in the chosen box, so its local transverse label is
constant. Both anchors therefore belong to the same local plaque and lie strictly within that box's
fixed state/transverse cores. No possibly returning second sheet is substituted. In addition,
whenever a transported anchor in this box belongs to the same global U-leaf as the others, its
central point is the SAME: the two local central points lie on the ONE opposite central leaf of this
box, and the conditional global at-most-one intersection of Step20 forces their equality. This is
the required same-LOCAL-plaque conclusion; global same-leaf membership alone does not imply it.

(C) MOVE FINITELY MANY ANCHORS THROUGH ORIGINAL OPEN CORES. Use Step20's actual conditional global
product Ψ=(a,b), with a(z)=s(z)∩u_0 and b(z)=u(z)∩s_0. Thus U-leaves are the slices b=t. Write
Ψ(p_j)=(a_j,t_0). The transported anchors p_j(t)=Ψ⁻¹(a_j,t) are continuous in the genuine intrinsic
factor topology and satisfy p_j(t_0)=p_j. For each anchor and each of the finitely many adjacent
boxes, take the inverse image under p_j(t) of the OPEN core interior containing p_j. Intersect these
finitely many open neighborhoods to obtain one open W of t_0 on which ALL anchors remain in their
respective core interiors. This is the finite open-intersection step actually written in Munkres26.7
Step1 p167/PDF184 and26.8 p168/PDF185; no entire intrinsic factor is asserted compact. The
transverse parameter images can be restricted to the already fixed compact transverse coordinate
cores. Also restrict first and last endpoints to their original inner boxes. Precisely, define
O_(x,y)⊂P×P by exactly four open conditions: b(x̃)∈W, b(ỹ)∈W, x̃ in the first inner box, and ỹ in
the last inner box. All four are continuous open preimages; the previously fixed core conditions are
already enforced by those inner boxes and W. This contains (x,y). The same-U relation itself is NOT
asserted open. For a pair (x̃,ỹ)∈O_(x,y) which IS on the same global U-leaf, let t=b(x̃)=b(ỹ). By
the global unique-intersection argument in (B), x̃ and p_0(t) belong to the same first LOCAL plaque,
each successive p_(j−1)(t),p_j(t) pair to the same chosen local plaque, and p_m(t),ỹ to the same
last local plaque. Thus all the joins below are defined in those original boxes.

(D) ONE FINITE NATIVE PATH AND A UNIFORM LOCAL BOUND. Apply the protected single-plaque prefix to
each of these joins in its fixed original compact transverse core and closed convex state-ball core.
For the jth box let B_j be its finite original state-speed bound and r_j its state-core radius;
every corresponding straight state join has real intrinsic length ≤2B_jr_j. Include the initial and
final joins, repeating the first/last core constants if necessary, and let c_(x,y) be the finite sum
of these nonnegative bounds. Concatenate the finitely many native joins at the matching anchors into
ONE continuous piecewise-C¹ admissible path from x̃ to ỹ; each piece has its original native
state-smooth extension near its closed interval. Lee11.20 p279 writes exactly the finite
concatenation/speed-integral argument. In the PathELength implementation, use one global
piecewise-defined path (extended constantly outside its compact parameter interval), apply the
prefix to its restriction on each piece, and use mathlib.manifold_pathELength_add on that SAME
global function and ordered breakpoints. The endpoint-null identities already bound in the prefix
avoid differentiability at junctions. Ordinary finite real integral addition gives the same finite
total native length. The admissible original intrinsic piecewise-C¹ length set is nonempty by this
path and bounded below by0. Therefore mathlib.csInf_le gives d_U(x̃,ỹ)≤c_(x,y)<∞ for every SAME-U
pair in O_(x,y). This proves the needed uniform local bound by actual paths; it neither asserts
continuity of d_U on varying leaves nor transports paths through the topological Q.

(E) COMPACT RELATIONS OF PAIRS, NOT INTRINSIC BALLS. Let K_0=[0,1]^n in the ORIGINAL finite real
target of H. It is compact: the canonical finite Pi sup norm induces the ORIGINAL finite real target
product topology, and in that norm K_0 is the closed ball of radius1/2 about the constant1/2 vector,
by mathlib.pi_norm_le_iff_of_nonneg_g8 and |r−1/2|≤1/2 iff0≤r≤1. The finite-dimensional proper-space
and compact-closed-ball leaves therefore give compactness in that original target topology, without
identifying this auxiliary target norm with any other target norm. This also includes n=0. No
Euclidean/Pi metric identification on P is made. Step18's ORIGINAL properness gives compact
C=H⁻¹(K_0). Each intrinsic factor of Ψ is Hausdorff, since it is an original native smooth leaf
(also its continuous injective immersion into Hausdorff P separates distinct points). Thus
R_U={(x,y)∈C×C:b(x)=b(y)} and R_S={(x,y)∈C×C:a(x)=a(y)} are compact: projections are continuous by
mathlib.continuous_fst/continuous_snd_g8, composition with a or b is continuous,
mathlib.isClosed_eq_g8 gives the ambient equality loci, and mathlib.isCompact_prod plus
mathlib.isCompact_of_isClosed_subset gives their compact intersections with C×C. Cover R_U by the
original ambient open sets O_(x,y) from (C)–(D). mathlib.isCompact_elim_finite_subcover_g2 extracts
finitely many of those SAME neighborhoods. Their finite set of nonnegative constants has a finite
real upper bound by mathlib.set_finite_bddAbove_g10; take its maximum with0, or equivalently the
maximum of the nonempty finite set obtained by adjoining0, to obtain μ_U≥0. Then every pair in R_U
satisfies d_U≤μ_U. If R_U is empty choose μ_U=0. Repeat the identical native construction with S/U
exchanged to obtain μ_S≥0 on R_S. Neither intrinsic balls nor D(r) are used as compact carriers.

(F) NORMALIZE BOTH ENDPOINTS BY ONE ORIGINAL DECK MAP. If H(x)=H(y)=z and x,y are on the same
selected U-leaf, choose the integer vector k_j=−⌊z_j⌋. mathlib.int_floor_bounds_g8 gives
0≤z_j+k_j<1, hence z+k∈K_0. The original equivariance H(δ_k w)=H(w)+k sends BOTH endpoints by this
ONE deck map into C. Step20's pointed native sheet transport preserves the selected U-leaf, so the
translated pair lies in R_U. The original smooth deck maps and their inverses are gtilde-isometries
by Step6 and topo.franks_intrinsic_leaf_metric_bounds_g8: they carry the SAME finite native
piecewise-C¹ admissible paths to such paths with exactly the same speed integrals. Taking the two
infimum inequalities proves equality of intrinsic distances. Therefore d_U(x,y)=d_U(δ_kx,δ_ky)≤μ_U.
The same argument gives the global equal-H same-S-leaf bound μ_S. No properness of a leaf,
topological-Q length transport or standard R^n smooth-leaf theorem enters.

(G) POSITIVITY FOR THE UNCHANGED EXPANSION CONTRADICTION. For distinct points p,q on one selected
native leaf, choose an intrinsic smooth coordinate chart χ about p whose domain avoids q, with
χ(0)=p and a closed positive-radius model ball of radius ρ inside its OPEN domain. Its image is
compact in the intrinsic Hausdorff leaf and lies inside the larger chart. On that closed ball times
the model unit sphere, N(z,e)=||D(j∘χ)_z e||_gtilde is continuous and strictly positive, because the
ORIGINAL native immersion j has injective derivative and the original tensor is positive.
mathlib.isCompact_exists_isMinOn gives a positive minimum c; homogeneity gives ||D(j∘χ)_z
v||≥c||v||, including v=0. For EVERY admissible intrinsic piecewise-C¹ path from p to q, native
continuity gives its first exit from χ(openBall(0,ρ)), at the coordinate sphere of radius ρ, before
reaching q. Refine its finite C¹ partition at this exit. The larger OPEN native chart provides
coordinate C¹ extensions on all the closed pieces up to that exit. On each piece apply
mathlib.norm_sub_le_integral_of_norm_deriv_le_of_le to the coordinate curve, with B the continuous
nonnegative norm of its derivative: continuity on the closed interval, real differentiability on its
interior and interval integrability follow from that C¹ extension, and the derivative bound is
equality. Finite endpoint triangle inequalities show the sum of coordinate-speed integrals is at
least ρ. The original metric speed lower bound then gives the length of this initial subpath, hence
the whole path, at least cρ. This quantifies ALL admissible paths. Lee6.17 makes their length set
nonempty, and mathlib.le_csInf gives d_L(p,q)≥cρ>0. This is the written Lee11.19/11.20 FIRST-EXIT
mechanism on the original intrinsic piecewise-C¹ definition; no smooth/C¹ infimum equality, ambient
EDist, completeness or compact intrinsic metric ball is used. For rank0 there are no distinct points
on a connected leaf. Thus Step22's positive-distance premise for distinct points is explicit.

CURRENT CONDITIONAL BOUNDARY. The finite equal-H bounds are now this source-bound consumer
application relative to Step20's original selected native global product Ψ and its conditional
Step19 ORIGINAL downstairs periodic-density/Step17 fixed-lift-index inputs and named lower
prerequisites. Franks's literal D(r) supremum remains an unproved historical source assertion which
is bypassed. The generic agent-written local-distance helper is not invoked, relabelled or retired.
Identification with arbitrary historical leaf models/separate receiving germs, the independent
spectral/count/cyclic/native/formal applications and whole classification remain guarded/open. This
component is not a whole Franks replacement, a new source-foundation discovery, or Lean/transitive
closure.

22. Injectivity uses intrinsic lengths, not Euclidean smooth coordinates
In Franks1969 §1.8 pp122–123, suppose H(x)=H(y), and take z=Wu(x)∩Ws(y). Using the preceding
conditional original-native global-product and linear-leaf-image source applications, complementary
linear leaf relations give H(z)=H(x)=H(y). Conditional on the same Step20/Step19/Step17 inputs and
named lower guards, use the preceding source-proved finite equal-H intrinsic bounds μ_u,μ_s. A
common integer deck translate moves the common H-image into [0,1]^n, so both endpoints lie in
K=H^−1([0,1]^n). The deck maps preserve original intrinsic leaf distances by
topo.franks_intrinsic_leaf_metric_bounds_g8 and the tensor/path proof above. Therefore every
equal-image same-unstable-leaf pair has distance≤μ_u. If x≠z, expansion d_(F^k Wu)(F^k x,F^k z)≥C^−1
λ^−k d_Wu(x,z) contradicts this bound, since H(F^k x)=H(F^k z) for every k. Inverse-time stable
expansion similarly gives z=y. Thus H is injective. If h(x)=h(y) downstairs, alter one lift by the
integer difference of its H-image, using the explicit canonical fibre lattice, so its H-image agrees
with the other; H injectivity then proves x=y downstairs.

23. Topological conclusion and zero-dimensional check
The preceding exact named-provider applications give onto and injective h at this node’s OWN ONE
LEVEL; therefore compactness of the given M and the Hausdorff torus turn this continuous bijection
into a homeomorphism with unchanged underlying function, by the named compact-to-Hausdorff
homeomorphism theorem. Its proved semiconjugacy equation is exactly the required conjugacy with the
same induced hyperbolic integral A. For n=0, M is homeomorphic to the singleton T^0, f is its unique
self-map, GL(0,Z) is trivial and eigenvalue exclusion is vacuous; the given q already supplies the
conjugacy, so none of the positive-dimensional index/Markov arguments is required. In positive
dimension this mixed-human source/API proof is complete at this node’s OWN ONE LEVEL relative to the
exact named dependencies. Their lower proof obligations and formal/kernel/Lean/GOAL completion
remain independent and are not certified by this disposition; no transitivity or standard smooth
structure is added.
-/
theorem franks_manning
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    [CompactSpace M] [ConnectedSpace M] [T2Space M] [SecondCountableTopology M]
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (Es Eu : ContinuousRealTangentSubbundle
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M)
    (metric : Bundle.ContMDiffRiemannianMetric
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞
      (EuclideanSpace ℝ (Fin n))
      (fun x : M ↦ TangentSpace (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) x))
    (C lam : ℝ) (h_torus : Nonempty (M ≃ₜ UnitAddTorus (Fin n))) :
    let I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨metric.toRiemannianMetric⟩
    0 < C → 0 < lam → lam < 1 →
    (∀ x, IsCompl (Es.toDistribution x) (Eu.toDistribution x)) →
    (∀ x, (Es.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Es.toDistribution (f x)) →
    (∀ x, (Eu.toDistribution x).map (mfderiv I I f x).toLinearMap =
      Eu.toDistribution (f x)) →
    (∀ x k (v : TangentSpace I x), v ∈ Es.toDistribution x →
      ‖mfderiv I I ((f : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    (∀ x k (v : TangentSpace I x), v ∈ Eu.toDistribution x →
      ‖mfderiv I I ((f.symm : M → M)^[k]) x v‖ ≤ C * lam ^ k * ‖v‖) →
    HyperbolicRealToralConjugacy n M f := by
  by_cases hn : n = 0
  · subst n
    intros
    exact hyperbolicRealToralConjugacy_zero f h_torus
  · classical
    intro I hC hlam hlam1 hcompl hEs hEu hs hu
    let : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨metric.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (fun x : M ↦ TangentSpace I x) :=
      ⟨metric.inner, metric.contMDiff.continuous, fun _ _ _ ↦ rfl⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    have hfinite : ∀ x y : M, edist x y ≠ ⊤ :=
      fun x y ↦ franks_manning_edist_ne_top x y
    let : MetricSpace M := EMetricSpace.toMetricSpace hfinite
    have hR : IsRiemannianManifold I M := ⟨fun _ _ ↦ rfl⟩
    let : IsRiemannianManifold I M := hR
    let : IsContMDiffRiemannianBundle I ∞ (EuclideanSpace ℝ (Fin n))
        (fun x : M ↦ TangentSpace I x) := inferInstance
    let S : InvariantRealTangentSplitting f := ⟨Es, Eu, hcompl, hEs, hEu⟩
    have hBounds : BundleAnosovBounds f S :=
      ⟨C, lam, hC, hlam, hlam1, fun k x v hv ↦ hs x k v hv,
        fun k x v hv ↦ hu x k v hv⟩
    obtain ⟨q⟩ := h_torus
    obtain ⟨B, hB, h, hinj, hsem, H, ⟨K, hK, hbound⟩, hlift⟩ :=
      franks_manning_lift_data hn f S hBounds q
    have hsurj : Function.Surjective h :=
      Topology.surjective_of_bounded_real_lift
        (fun v ↦ q.symm (Topology.coordinateProjection n v)) h H K hK hbound hlift
    exact package_hyperbolicRealToralConjugacy f B hB h h.continuous ⟨hinj, hsurj⟩ hsem


end HolomorphicAnosov


namespace HolomorphicAnosov.FranksFibreInjectivity

open Set

/-- The finite-subcover step of the current Franks–Manning source proof, Step21(E).
A locally bounded function on a compact relation has a finite uniform upper bound.
No continuity of the intrinsic-distance function is required. The empty relation
is allowed, and the finite sum of positive parts supplies a nonnegative bound. -/
theorem compact_bound_of_local_bound {X : Type*} [TopologicalSpace X]
    (R : Set X) (d : X → ℝ) (hR : IsCompact R)
    (hloc : ∀ p ∈ R, ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
      ∃ b : ℝ, ∀ q ∈ R, q ∈ U → d q ≤ b) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ p ∈ R, d p ≤ b := by
  classical
  choose U hU hp B hB using fun p : R ↦ hloc p p.property
  have hcover : R ⊆ ⋃ p : R, U p := by
    intro p hpR
    exact mem_iUnion.mpr ⟨⟨p, hpR⟩, hp ⟨p, hpR⟩⟩
  obtain ⟨t, ht⟩ := hR.elim_finite_subcover U hU hcover
  refine ⟨∑ p ∈ t, max 0 (B p), Finset.sum_nonneg (fun _ _ ↦ le_max_left _ _), ?_⟩
  intro p hpR
  obtain ⟨i, hit, hpi⟩ := mem_iUnion₂.mp (ht hpR)
  exact (hB i p hpR hpi).trans ((le_max_right 0 (B i)).trans
    (Finset.single_le_sum (fun j _ ↦ le_max_left 0 (B j)) hit))

/-- Every real coordinate vector admits the SAME integer translate into the closed
unit cube. This is the literal floor normalization used in Franks (1969), §1.8,
p.122, and Step21(F); n=0 gives the singleton cube. -/
theorem exists_integer_translate_mem_unitCube {n : ℕ} (v : Fin n → ℝ) :
    ∃ z : Fin n → ℤ, v + (fun i ↦ (z i : ℝ)) ∈ Icc 0 1 := by
  refine ⟨fun i ↦ -⌊v i⌋, ?_⟩
  constructor
  · intro i
    change 0 ≤ v i + ((-⌊v i⌋ : ℤ) : ℝ)
    simpa only [Int.cast_neg, sub_eq_add_neg, Int.fract] using Int.fract_nonneg (v i)
  · intro i
    change v i + ((-⌊v i⌋ : ℤ) : ℝ) ≤ 1
    simpa only [Int.cast_neg, sub_eq_add_neg, Int.fract] using (Int.fract_lt_one (v i)).le

/-- Step21(E–F) of the source proof of Franks–Manning, applied to the actual
proper lift and selected global-product leaf label. A compact relation of pairs
in the inverse image of the closed unit cube replaces any assertion that an
intrinsic leaf ball is compact. One deck translate normalizes BOTH endpoints of
an equal-H pair. Local path bounds, properness, continuous leaf labels and deck
isometry are explicit provider inputs, never consequences assumed for free. -/
theorem equal_image_bound_of_proper_deck_local_bound
    {n : ℕ} {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q] [T2Space Q]
    (H : P → (Fin n → ℝ)) (hH : IsProperMap H)
    (leaf : P → Q) (hleaf : Continuous leaf) (d : P → P → ℝ)
    (deck : (Fin n → ℤ) → P → P)
    (hequiv : ∀ z x, H (deck z x) = H x + (fun i ↦ (z i : ℝ)))
    (hdeck_leaf : ∀ z x y, leaf x = leaf y → leaf (deck z x) = leaf (deck z y))
    (hdeck_dist : ∀ z x y, leaf x = leaf y → d (deck z x) (deck z y) = d x y)
    (hloc : ∀ x y, leaf x = leaf y → ∃ U : Set (P × P), IsOpen U ∧ (x, y) ∈ U ∧
      ∃ b : ℝ, ∀ p ∈ U, leaf p.1 = leaf p.2 → d p.1 p.2 ≤ b) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ x y, leaf x = leaf y → H x = H y → d x y ≤ b := by
  let K : Set P := H ⁻¹' Icc 0 1
  have hK : IsCompact K := hH.isCompact_preimage isCompact_Icc
  let R : Set (P × P) := {p | p.1 ∈ K ∧ p.2 ∈ K ∧ leaf p.1 = leaf p.2}
  have hR : IsCompact R := by
    have he : R = (K ×ˢ K) ∩ {p : P × P | leaf p.1 = leaf p.2} := by
      ext p
      simp only [R, mem_ofPred_eq, mem_inter_iff, mem_prod, and_assoc]
    rw [he]
    exact (hK.prod hK).inter_right
      (isClosed_eq (hleaf.comp continuous_fst) (hleaf.comp continuous_snd))
  have hRloc : ∀ p ∈ R, ∃ U : Set (P × P), IsOpen U ∧ p ∈ U ∧
      ∃ b : ℝ, ∀ q ∈ R, q ∈ U → d q.1 q.2 ≤ b := by
    intro p hp
    obtain ⟨U, hU, hpU, b, hb⟩ := hloc p.1 p.2 hp.2.2
    exact ⟨U, hU, hpU, b, fun q hq hqU ↦ hb q hqU hq.2.2⟩
  obtain ⟨b, hb0, hb⟩ := compact_bound_of_local_bound R (fun p ↦ d p.1 p.2) hR hRloc
  refine ⟨b, hb0, ?_⟩
  intro x y hxy hHxy
  obtain ⟨z, hz⟩ := exists_integer_translate_mem_unitCube (H x)
  have hxK : deck z x ∈ K := by
    change H (deck z x) ∈ Icc 0 1
    rwa [hequiv]
  have hyK : deck z y ∈ K := by
    change H (deck z y) ∈ Icc 0 1
    rwa [hequiv, ← hHxy]
  have hpR : (deck z x, deck z y) ∈ R := ⟨hxK, hyK, hdeck_leaf z x y hxy⟩
  rw [← hdeck_dist z x y hxy]
  exact hb _ hpR

end HolomorphicAnosov.FranksFibreInjectivity


