import HolomorphicAnosov.Topology.MonodromyDeckOfOne
import HolomorphicAnosov.Topology.FixedPointTransfer
import HolomorphicAnosov.Topology.PullbackCoordinateLiftIdentity
import HolomorphicAnosov.Topology.ConjugatedMonodromyEndpoint
import HolomorphicAnosov.Topology.BoundedPiDisplacementFixedPoint
import HolomorphicAnosov.Topology.HyperbolicPowerNotOne
import HolomorphicAnosov.Topology.RealDisplacementEquivalence
import HolomorphicAnosov.Topology.IntegralMatrixPowerRealCast
import HolomorphicAnosov.Topology.IntegralMatrixPowerComplexification
import HolomorphicAnosov.Topology.BoundedDisplacementFixedPoint
import HolomorphicAnosov.Topology.PeriodicDisplacementBounded
import HolomorphicAnosov.Topology.BoundedEuclideanFixedPoint
import HolomorphicAnosov.Topology.IterateCoordinateDeckCovariance
import HolomorphicAnosov.Linear.HyperbolicRealSplitting
import HolomorphicAnosov.Topology.InvertibleLinearLocalDegree
import HolomorphicAnosov.Topology.TorusStandardWinding
import HolomorphicAnosov.Topology.TorusCoordinateCover
import HolomorphicAnosov.Topology.EuclideanFixedPointIndex
import HolomorphicAnosov.Paper.Zhang.IntegralToralMap
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Homotopy.Path
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Fixed points of original torus lifts

Source: Franks, *Anosov Diffeomorphisms on Tori* (1969), Lemma 1.2,
pp. 118–119, existence portion of the bounded-displacement homotopy proof;
Corollary 1.3, p. 119. Dold, *Fixed point index and fixed point theorem for
Euclidean neighborhood retracts* (1965), §§1.1–1.3 p. 1 and §1.7 p. 2.
DAG node: `topo.original_torus_lift_fixed_point_existence_g8`.

Implementation route: the original eight-step source proof below is retained
verbatim as the Franks/Dold plan, including its homotopy to the linear endpoint
and sign-of-determinant calculation. The kernel proof takes a shorter
existence-only route after establishing the same native deck covariance and
bounded periodic displacement. For B the real action of A^m and L = I − B,
it forms the bounded continuous correction C(x) = L⁻¹(G(x) − B(x)). Dold's
constant-map normalization, empty-support law and compact-total-support
homotopy invariance, via the named `euclidean_fixed_point_index_basic_laws`,
give C a fixed point using H(t,x) = t C(x). Its full fixed locus lies in one
closed ball times [0,1]. Applying L to C(x) = x yields G(x) = x. This uses
no linear local-degree calculation and asserts no index value for G. This
algebraic bounded-correction reduction is the implementation argument, not a
claim that Franks writes this alternative homotopy. For the hyperbolic
specialization, Mathlib's `spectrum.map_pow_of_pos` and
`Module.End.hasEigenvalue_iff_mem_spectrum` give polynomial spectral mapping;
the kernel proof does not invoke the invariant-splitting argument recorded in
the original plan. The public hypotheses and conclusions are unchanged.
-/

universe u

noncomputable section

open scoped ContDiff

namespace HolomorphicAnosov.Topology

/-- The actual coordinate quotient from real n-space to the period-one torus.
Source: Hatcher pp. 29–34, coordinate real covering and finite products. -/
def originalTorusProjection (n : ℕ) : C((Fin n → ℝ), UnitAddTorus (Fin n)) where
  toFun v i := (v i : UnitAddCircle)
  continuous_toFun := continuous_pi fun i ↦
    continuous_quotient_mk'.comp (continuous_apply i)

/-- The positive coordinate-winding loop for an integral vector.
Source: Hatcher Theorem 1.7 pp. 29–31 and Example 1.13 p. 34.
It is the actual path t ↦ ([t z_i])_i, based at zero. -/
def originalTorusIntegerLoop {n : ℕ} (z : Fin n → ℤ) :
    Path (0 : UnitAddTorus (Fin n)) 0 where
  toFun t i := ((t : ℝ) * (z i : ℝ) : UnitAddCircle)
  continuous_toFun := continuous_pi fun i ↦
    continuous_quotient_mk'.comp (continuous_subtype_val.mul_const (z i : ℝ))
  source' := by ext i; simp
  target' := by
    ext i
    change (((1 : ℝ) * (z i : ℝ) : ℝ) : AddCircle (1 : ℝ)) = 0
    rw [one_mul, AddCircle.coe_eq_zero_iff]
    exact ⟨z i, by simp⟩

/-- The genuine pullback covering carrier, with its induced original topology.
Source: the pullback of the coordinate covering used in Franks pp. 118–119. -/
abbrev OriginalTorusPullback {n : ℕ} {M : Type u} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) :=
  {xv : M × (Fin n → ℝ) // q xv.1 = originalTorusProjection n xv.2}

/-- The actual pullback covering is homeomorphic to the coordinate space, by its
second coordinate.  Its inverse uses the original homeomorphism q, not smooth transport. -/
private def pullbackCoordinates {n : ℕ} {M : Type u} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) : OriginalTorusPullback q ≃ₜ (Fin n → ℝ) where
  toFun ξ := ξ.val.2
  invFun v := ⟨(q.symm (originalTorusProjection n v), v), q.apply_symm_apply _⟩
  left_inv ξ := by
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg q.symm ξ.property).symm.trans (q.symm_apply_apply _)
    · rfl
  right_inv v := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := ((q.symm.continuous.comp (originalTorusProjection n).continuous).prodMk
    continuous_id).subtype_mk _

/-- Integer translation is invisible under the coordinate torus projection. -/
private theorem torus_projection_integer_translation (n : ℕ)
    (v : Fin n → ℝ) (z : Fin n → ℤ) :
    originalTorusProjection n (v + fun i ↦ (z i : ℝ)) = originalTorusProjection n v := by
  ext i
  change ((v i + (z i : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (v i : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add]
  have hz : ((z i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨z i, by simp⟩
  rw [hz, add_zero]

/-- Covering uniqueness propagates the genuine normalized-loop endpoint increment
at zero to EVERY point of the chosen continuous lift. -/
private theorem deck_covariance_of_zero_increment (n : ℕ)
    (hp : IsCoveringMap (originalTorusProjection n))
    (g : UnitAddTorus (Fin n) → UnitAddTorus (Fin n))
    (G : C((Fin n → ℝ), (Fin n → ℝ)))
    (hG : ∀ v, originalTorusProjection n (G v) = g (originalTorusProjection n v))
    (z w : Fin n → ℤ)
    (hzero : G (fun i ↦ (z i : ℝ)) = G 0 + fun i ↦ (w i : ℝ)) :
    ∀ v, G (v + fun i ↦ (z i : ℝ)) = G v + fun i ↦ (w i : ℝ) := by
  have hcomp : originalTorusProjection n ∘ (fun v ↦ G (v + fun i ↦ (z i : ℝ))) =
      originalTorusProjection n ∘ (fun v ↦ G v + fun i ↦ (w i : ℝ)) := by
    funext v
    change originalTorusProjection n (G (v + fun i ↦ (z i : ℝ))) =
      originalTorusProjection n (G v + fun i ↦ (w i : ℝ))
    rw [torus_projection_integer_translation, hG, torus_projection_integer_translation, hG]
  have hh := hp.eq_of_comp_eq
    (G.continuous.comp (continuous_id.add continuous_const))
    (G.continuous.add continuous_const) hcomp 0 (by simpa using hzero)
  intro v
  exact congrFun hh v

/-- Two actual lifts of the same map differ by a constant integer translation;
covering uniqueness proves this on the original connected coordinate space. -/
private theorem two_coordinate_lifts_integer_translate (n : ℕ)
    (hp : IsCoveringMap (originalTorusProjection n))
    (G H : C((Fin n → ℝ), (Fin n → ℝ)))
    (hproj : ∀ v, originalTorusProjection n (G v) = originalTorusProjection n (H v)) :
    ∃ z : Fin n → ℤ, ∀ v, G v = H v + fun i ↦ (z i : ℝ) := by
  have hzero : originalTorusProjection n (G 0 - H 0) = 0 := by
    ext i
    change (((G 0 i - H 0 i) : ℝ) : AddCircle (1 : ℝ)) = 0
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr (congrFun (hproj 0) i)
  have hz : ∀ i, ∃ z : ℤ, (z : ℝ) = G 0 i - H 0 i := by
    intro i
    obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp (congrFun hzero i)
    exact ⟨z, by simpa using hz⟩
  choose z hz using hz
  refine ⟨z, ?_⟩
  have hcomp : originalTorusProjection n ∘ G =
      originalTorusProjection n ∘ (fun v ↦ H v + fun i ↦ (z i : ℝ)) := by
    funext v
    change originalTorusProjection n (G v) = originalTorusProjection n (H v + _)
    rw [torus_projection_integer_translation]
    exact hproj v
  have heq : G 0 = H 0 + fun i ↦ (z i : ℝ) := by
    ext i
    simp [hz i]
  have hh := hp.eq_of_comp_eq G.continuous (H.continuous.add continuous_const) hcomp 0 heq
  intro v
  exact congrFun hh v


/-- One-step normalized monodromy suffices for EVERY chosen iterate lift: lift
one step on the simply-connected coordinate space, iterate it, and use covering
uniqueness to compare the supplied iterate lift with an integer translate. -/
private theorem arbitrary_iterate_lift_covariance (n : ℕ)
    (hp : IsCoveringMap (originalTorusProjection n))
    (hsurj : Function.Surjective (originalTorusProjection n))
    (g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hzero : ∀ H : C((Fin n → ℝ), (Fin n → ℝ)),
      (∀ v, originalTorusProjection n (H v) = g (originalTorusProjection n v)) →
      ∀ z : Fin n → ℤ, H (fun i ↦ (z i : ℝ)) = H 0 + fun i ↦ (A.mulVec z i : ℝ))
    (m : ℕ) (G : C((Fin n → ℝ), (Fin n → ℝ)))
    (hG : ∀ v, originalTorusProjection n (G v) = g^[m] (originalTorusProjection n v)) :
    ∀ v (z : Fin n → ℤ), G (v + fun i ↦ (z i : ℝ)) =
      G v + fun i ↦ ((A.mulVecLin ^ m) z i : ℝ) := by
  obtain ⟨e₀, he₀⟩ := hsurj (g (originalTorusProjection n 0))
  obtain ⟨H, hH, _⟩ := hp.existsUnique_continuousMap_lifts
    (g.comp (originalTorusProjection n)) 0 e₀ he₀
  have hHproj : ∀ v, originalTorusProjection n (H v) = g (originalTorusProjection n v) :=
    fun v ↦ congrFun hH.2 v
  have hHdeck : ∀ v (z : Fin n → ℤ), H (v + fun i ↦ (z i : ℝ)) =
      H v + fun i ↦ (A.mulVec z i : ℝ) := by
    intro v z
    exact deck_covariance_of_zero_increment n hp g H hHproj z (A.mulVec z) (hzero H hHproj z) v
  let Hm : C((Fin n → ℝ), (Fin n → ℝ)) := ⟨H^[m], H.continuous.iterate m⟩
  have hsemi : Function.Semiconj (originalTorusProjection n) H g := hHproj
  have hHm : ∀ v, originalTorusProjection n (Hm v) = g^[m] (originalTorusProjection n v) :=
    hsemi.iterate_right m
  obtain ⟨w, hw⟩ := two_coordinate_lifts_integer_translate n hp G Hm
    (fun v ↦ (hG v).trans (hHm v).symm)
  intro v z
  rw [hw, show Hm (v + fun i ↦ (z i : ℝ)) =
    Hm v + fun i ↦ ((A.mulVecLin ^ m) z i : ℝ) from
      iterate_coordinate_deck_covariance n H A hHdeck m v z, hw]
  abel









/-- Once the actual chosen lift has its genuine deck-covariance law, the source
bounded-displacement argument applies directly on its ORIGINAL pullback carrier. -/
private theorem fixed_lift_of_deck_covariance {n : ℕ} {M : Type u} [TopologicalSpace M]
    (q : M ≃ₜ UnitAddTorus (Fin n)) (f : M → M) (m : ℕ)
    (F : C(OriginalTorusPullback q, OriginalTorusPullback q))
    (hF : ∀ ξ, (F ξ).val.1 = f^[m] ξ.val.1)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ¬ Module.End.HasEigenvalue ((A.map (Int.castRingHom ℂ)).mulVecLin ^ m) 1)
    (hdeck : ∀ v (z : Fin n → ℤ),
      pullbackCoordinates q (F ((pullbackCoordinates q).symm (v + fun i ↦ (z i : ℝ)))) =
      pullbackCoordinates q (F ((pullbackCoordinates q).symm v)) +
        ((A.map (Int.castRingHom ℝ)).mulVecLin ^ m) (fun i ↦ (z i : ℝ))) :
    ∃ ξ, F ξ = ξ ∧ f^[m] ξ.val.1 = ξ.val.1 := by
  let G : C((Fin n → ℝ), (Fin n → ℝ)) :=
    ⟨fun v ↦ pullbackCoordinates q (F ((pullbackCoordinates q).symm v)),
      (pullbackCoordinates q).continuous.comp
        (F.continuous.comp (pullbackCoordinates q).symm.continuous)⟩
  let B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ((A.map (Int.castRingHom ℝ)).mulVecLin ^ m).toContinuousLinearMap
  let e : C((Fin n → ℝ), (Fin n → ℝ)) :=
    ⟨fun v ↦ G v - B v, G.continuous.sub B.continuous⟩
  have he : ∀ v (z : Fin n → ℤ), e (v + fun i ↦ (z i : ℝ)) = e v := by
    intro v z
    change G (v + fun i ↦ (z i : ℝ)) - B (v + fun i ↦ (z i : ℝ)) = G v - B v
    rw [show G (v + fun i ↦ (z i : ℝ)) = G v + B (fun i ↦ (z i : ℝ)) from hdeck v z,
      map_add]
    abel
  obtain ⟨K, hK, hbound⟩ := periodic_displacement_bounded n e he
  obtain ⟨L, hL⟩ := real_displacement_equivalence n A m hA
  obtain ⟨v, hv⟩ := bounded_pi_displacement_fixed_point n G B L hL K hK hbound
  exact fixed_point_transfer_homeomorph (pullbackCoordinates q) (fun ξ => ξ.val.1) f m F hF v hv

/-- Exact assembly on the original carrier from the native projection-cover and
one-step normalized monodromy operands; no property of a smooth torus transport is used. -/
private theorem original_fixed_lift_from_monodromy {n : ℕ} {M : Type u}
    [TopologicalSpace M] (q : M ≃ₜ UnitAddTorus (Fin n))
    (f : M → M) (hf : Continuous f)
    (A : Matrix (Fin n) (Fin n) ℤ)
    (hp : IsCoveringMap (originalTorusProjection n))
    (hsurj : Function.Surjective (originalTorusProjection n))
    (hzero : ∀ H : C((Fin n → ℝ), (Fin n → ℝ)),
      (∀ v, originalTorusProjection n (H v) =
        q (f (q.symm (originalTorusProjection n v)))) →
      ∀ z : Fin n → ℤ, H (fun i ↦ (z i : ℝ)) = H 0 + fun i ↦ (A.mulVec z i : ℝ))
    (m : ℕ)
    (hA : ¬ Module.End.HasEigenvalue ((A.map (Int.castRingHom ℂ)).mulVecLin ^ m) 1)
    (F : C(OriginalTorusPullback q, OriginalTorusPullback q))
    (hF : ∀ ξ, (F ξ).val.1 = f^[m] ξ.val.1) :
    ∃ ξ, F ξ = ξ ∧ f^[m] ξ.val.1 = ξ.val.1 := by
  let g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
    ⟨fun x ↦ q (f (q.symm x)), q.continuous.comp (hf.comp q.symm.continuous)⟩
  let G : C((Fin n → ℝ), (Fin n → ℝ)) :=
    ⟨fun v ↦ pullbackCoordinates q (F ((pullbackCoordinates q).symm v)),
      (pullbackCoordinates q).continuous.comp
        (F.continuous.comp (pullbackCoordinates q).symm.continuous)⟩
  have hG : ∀ v, originalTorusProjection n (G v) = g^[m] (originalTorusProjection n v) :=
    pullback_coordinate_lift_identity_homeomorph (pullbackCoordinates q) q
      (fun ξ => ξ.val.1) (originalTorusProjection n) (fun ξ => ξ.property.symm)
      f m F hF
  have hdeck := arbitrary_iterate_lift_covariance n hp hsurj g A hzero m G hG
  apply fixed_lift_of_deck_covariance q f m F hF A hA
  intro v z
  change G (v + fun i ↦ (z i : ℝ)) = G v + _
  rw [hdeck v z, integral_matrix_power_real_cast]

open Filter Function



/-- Integral vectors, as actual points of the projection kernel. -/
private def integerKernelMap (n : ℕ) : (Fin n → ℤ) →+ (coordinateProjection n).ker where
  toFun z := ⟨fun i ↦ (z i : ℝ), by
    change coordinateProjection n _ = 0
    ext i
    exact (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨z i, by simp⟩⟩
  map_zero' := by ext; simp
  map_add' z w := by ext; simp

/-- The genuine straight integral lift in the native real-coordinate space. -/
private def straightIntegralPath (n : ℕ) (z : Fin n → ℤ) :
    Path (0 : Fin n → ℝ) (fun i ↦ (z i : ℝ)) where
  toFun t i := (t : ℝ) * (z i : ℝ)
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by ext; simp

/-- Projection of the actual straight integral path, with its quotient-zero endpoint casts. -/
private def integralLoop (n : ℕ) (z : Fin n → ℤ) : Path (0 : UnitAddTorus (Fin n)) 0 :=
  ((straightIntegralPath n z).map (coordinateProjection_cover n).continuous).cast
    (by ext; simp [coordinateProjection]) (by
      ext i
      exact ((AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mpr ⟨z i, by simp⟩).symm)

/-- The projected straight path has the literal positive quotient-circle formula by reduction. -/
private theorem integralLoop_formula (n : ℕ) (z : Fin n → ℤ) (t : unitInterval)
    (i : Fin n) : integralLoop n z t i = (((t : ℝ) * (z i : ℝ) : ℝ) : UnitAddCircle) := rfl


/-- The original zero point as an element of the actual quotient projection fibre. -/
private def zeroFiber (n : ℕ) :
    (coordinateProjection n) ⁻¹' {0} := ⟨0, by simp⟩

/-- Mathlib `IsCoveringMap.monodromy_eq_of_map_eq` applied to the straight integral lift. -/
private theorem integralLoop_monodromy (n : ℕ) (z : Fin n → ℤ) :
    (coordinateProjection_cover n).isCoveringMap.monodromy
      ⟦integralLoop n z⟧ (zeroFiber n) =
      ⟨(integerKernelMap n z).val, (integerKernelMap n z).property⟩ := by
  apply (coordinateProjection_cover n).isCoveringMap.monodromy_eq_of_map_eq
    (⟦straightIntegralPath n z⟧)
  rfl



/-- Positive integral winding translates every point of the actual zero fibre
by the same integer vector. Source: Hatcher, Theorem 1.7, pp.29–31, and
Propositions 1.30–1.34, pp.60–63. The straight-path endpoint calculation and
Mathlib's monodromy/deck commutation extend it from zero to every fibre point;
commutativity is supplied by the actual additive integer kernel. -/
private theorem integralLoop_monodromy_all (n : ℕ) (z : Fin n → ℤ) :
    ∀ e : (coordinateProjection n) ⁻¹' {0},
      (coordinateProjection_cover n).isCoveringMap.monodromy ⟦integralLoop n z⟧ e =
      (coordinateProjection_cover n).toMultiplicative.toPermFiber 0
        (integerKernelMap n z) e := by
  apply monodromy_deck_of_one (coordinateProjection_cover n) _ _ (zeroFiber n)
  rw [integralLoop_monodromy]
  apply Subtype.ext
  change (integerKernelMap n z).val = (integerKernelMap n z).val + 0
  simp


/-- The actual chosen-lift zero increment, from the original based-change loop homotopy.
Source: Hatcher path and homotopy lifting (Theorem1.7 pp.29–31), with the actual
monodromy composition and deck-translation laws. No basedness of `g` is assumed.
-/
private theorem chosen_lift_zero_increment {n : ℕ}
    (g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)))
    (c : Path (0 : UnitAddTorus (Fin n)) (g 0))
    (G : (Fin n → ℝ) → (Fin n → ℝ)) (hG : Continuous G)
    (hLift : ∀ v, coordinateProjection n (G v) = g (coordinateProjection n v))
    (z w : Fin n → ℤ)
    (hLoop : (c.trans (((integralLoop n z).map g.continuous).trans c.symm)).Homotopic
      (integralLoop n w)) :
    G (fun i ↦ (z i : ℝ)) = G 0 + (fun i ↦ (w i : ℝ)) := by
  let hp := coordinateProjection_cover n
  let ex : (coordinateProjection n) ⁻¹' {g 0} := ⟨G 0, by simpa using hLift 0⟩
  let ey : (coordinateProjection n) ⁻¹' {g 0} :=
    ⟨G (fun i ↦ (z i : ℝ)), by
      change coordinateProjection n (G (fun i ↦ (z i : ℝ))) = g 0
      rw [hLift]
      have hz : coordinateProjection n (fun i ↦ (z i : ℝ)) = 0 :=
        (integerKernelMap n z).property
      rw [hz]⟩
  have hMapped :
      Path.Homotopic.Quotient.map (⟦(straightIntegralPath n z).map hG⟧ : Path.Homotopic.Quotient ex.val ey.val)
        ⟨coordinateProjection n, hp.continuous⟩ =
      (Path.Homotopic.Quotient.map (⟦integralLoop n z⟧ : Path.Homotopic.Quotient (0 : UnitAddTorus (Fin n)) 0) g).cast ex.property ey.property := by
    change ⟦((straightIntegralPath n z).map hG).map hp.continuous⟧ =
      ⟦((integralLoop n z).map g.continuous).cast ex.property ey.property⟧
    congr 1
    ext t i
    exact congrFun (hLift (straightIntegralPath n z t)) i
  have hEnd := hp.isCoveringMap.monodromy_eq_of_map_eq
    (⟦(straightIntegralPath n z).map hG⟧ : Path.Homotopic.Quotient ex.val ey.val) hMapped
  have hClass :
      Path.Homotopic.Quotient.trans (⟦c⟧ : Path.Homotopic.Quotient (0 : UnitAddTorus (Fin n)) (g 0))
        (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.map (⟦integralLoop n z⟧ : Path.Homotopic.Quotient (0 : UnitAddTorus (Fin n)) 0) g) ⟦c.symm⟧) =
      ⟦integralLoop n w⟧ := by
    exact Path.Homotopic.Quotient.eq.mpr hLoop
  have hAll : ∀ e0, hp.isCoveringMap.monodromy
      (Path.Homotopic.Quotient.trans (⟦c⟧ : Path.Homotopic.Quotient (0 : UnitAddTorus (Fin n)) (g 0))
        (Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.map (⟦integralLoop n z⟧ : Path.Homotopic.Quotient (0 : UnitAddTorus (Fin n)) 0) g) ⟦c.symm⟧)) e0 =
      hp.toMultiplicative.toPermFiber 0 (integerKernelMap n w) e0 := by
    rw [hClass]
    exact integralLoop_monodromy_all n w
  have he := conjugated_monodromy_endpoint hp ⟦c⟧
    (Path.Homotopic.Quotient.map (⟦integralLoop n z⟧ : Path.Homotopic.Quotient (0 : UnitAddTorus (Fin n)) 0) g)
    (integerKernelMap n w) hAll ex
  rw [hEnd] at he
  have hev := congrArg Subtype.val he
  change G (fun i ↦ (z i : ℝ)) = (fun i ↦ (w i : ℝ)) + G 0 at hev
  simpa only [add_comm] using hev


/-- Every eligible positive iterate of the original diffeomorphism has a fixed
point in every continuous lift to the actual pullback cover.

Source: Franks (1969), Lemma 1.2 pp. 118–119 (existence homotopy only),
Corollary 1.3 p. 119; Dold (1965), Definitions 1.1–1.2, Proposition 1.3 and
Homotopy Invariance 1.7, pp. 1–2. The nonzero linear local degree is the
arbitrary-dimensional degree of I−A^m, not a derivative of a topological conjugate.

The map q is only a homeomorphism; the manifold atlas is the original one.
The self-model real chart gives the boundaryless convention. Compactness,
Hausdorffness and second countability express a closed smooth manifold.
The path c makes the basepoint change explicit. The condition hA says precisely
that the original downstairs map induces A in coordinate winding numbers:
its conjugated image of each integral loop ℓ_z is homotopic to ℓ_(Az).
All loop classes have these normalized representatives by Hatcher pp. 29–34;
thus this condition neither chooses an unrelated group identification nor
assumes deck covariance of the supplied lift. The chosen basepoint path has
no effect because the torus fundamental group is abelian.

The complex matrix is the complexification of the real action of the integral
matrix. The first clause uses exactly absence of eigenvalue 1 for A^m; the
second retains the stated unit-circle-free specialization. The projection
fixed-point equation is included in each conclusion. There is no uniqueness,
Anosov, invariant splitting, or smoothness assumption on q or the lift.
For n=0 the torus and pullback are singletons; no positive-dimensional premise
is added. No index value is exported by the DAG statement.

Complete natural-language proof of the current DAG node (Stage2 defers its
formal proof, relative to the named source and Mathlib prerequisites):

1. Coordinate covering over the original manifold
Write p0:R^n→T^n for the coordinate quotient map. The map Q:P→R^n, Q(x,v)=v, is a homeomorphism
with inverse v↦(q^(−1)(p0(v)),v). Its deck translations are δ_z(x,v)=(x,v+z). For the given
continuous lift F of f^m, put G=Q∘F∘Q^(−1), so p0∘G=(q∘f^m∘q^(−1))∘p0. All maps here are
continuous. Smoothness of q or G is neither assumed nor used. If n=0, T⁰, M, P and R⁰ are
singletons by q and Q; the given lift fixes their unique point. Treat this case directly before
the positive-dimensional coercivity and local orientation calculation below.

2. The same induced action gives deck covariance
For z∈Z^n, start at v∈R^n and project the straight path t↦v+t z. In winding coordinates its based
loop class is z. Apply the downstairs map q∘f^m∘q^(−1); its induced action is A^m, independent of
the basepoint path since π1(T^n) is abelian. G applied to that straight path is a lift starting at
G(v), so its endpoint is G(v)+A^m z by the winding/monodromy characterization. Thus
G(v+z)=G(v)+A^m z for every v,z. The endpoint calculation may first be done at one basepoint and
extended to all v by uniqueness of continuous lifts on the connected Euclidean cover. It uses the
matrix induced by f, not a separately chosen linear model.

3. A bounded periodic displacement
Let B be the real linear action of the integral matrix A^m, and put e(v)=G(v)−Bv. The preceding
identity gives e(v+z)=e(v). Each v can be translated by minus its coordinate floors into [0,1]^n,
including negative coordinates. This cube lies in the closed Euclidean ball of radius sqrt(n),
whose compactness follows from finite-dimensional properness. The continuous function ‖e‖ is
bounded above on that ball by some K≥0, and periodicity gives ‖e(v)‖≤K for every v∈R^n. This is
the bounded-displacement input in Franks1.2 p.118; it holds for every chosen lift, including a
lift changed by an arbitrary deck translation, with a possibly different finite K. It uses neither
isolation nor hyperbolicity of the smooth dynamics.

4. The published homotopy has one compact fixed support
Assume n>0 and write L=I−B. If L had a nonzero real kernel vector, its complexification would have
eigenvalue1 for B=A^m, contrary to the hypothesis. Finite-dimensional injectivity therefore gives
a linear inverse L⁻¹ and a continuous linear inverse by the named finite-dimensional leaf. Its
operator norm c is positive: norm zero would make the inverse map zero, impossible on nonzero R^n.
Let μ=1/c>0. Since v=L⁻¹(Lv), the operator norm inequality gives ‖Lv‖≥μ‖v‖ for all v. Choose R>0
with μR>K. Follow Franks p.119 literally: H(t,v)=tBv+(1−t)G(v)=Bv+(1−t)e(v), t∈[0,1]. This is
jointly continuous and ‖v−H(t,v)‖≥‖Lv‖−(1−t)‖e(v)‖≥μ‖v‖−K. In particular it never vanishes when
‖v‖≥R, uniformly at every time. The total fixed set Z={(t,v):H(t,v)=v} is the closed equality
locus of two continuous maps into the Hausdorff R^n, and is contained in the compact product
[0,1]×closedBall(0,R); thus Z is compact. Its projected union C={v:H(t,v)=v for some t} is compact
too. Each slice Fix(H_t) is closed and contained in the compact ball, so is compact, including if
empty. All fixed points are strictly inside the ball. This proves Dold1.7’s literal
common-compact-support hypothesis and the stronger compact-total-fixed-set hypothesis of the
existing G9 provider. Pointwise compactness of time slices alone is not substituted for that
guard. The argument has not assumed that Fix(G) is finite or isolated.

5. The linear endpoint has nonzero homological index
The linear map v↦Bv has fixed set {0}, because L=I−B is invertible. Dold Definitions1.1–1.2 p.1
define its Euclidean index by L_* on the positive local fundamental generator of
H_n(R^n,R^n\{0};Z). This is exactly the normalization used by Franks p.118. The existing
arbitrary-dimensional linear local-degree theorem gives I(B,R^n)=sign(det L)∈{−1,1}. In particular
it is nonzero; its sign is immaterial for existence. The determinant is that of I−A^m, not the
derivative of a topological conjugate. This calculation uses no derivative of Q, smoothness of G,
Anosov splitting or local isolated-fixed-point formula for G.

6. Dold homotopy invariance forces a fixed point
Use Dold1.7 p.2 on the original full open Euclidean domain V=R^n and the homotopy H from the
preceding step. Its two endpoints are H_0=G and H_1=B, with compact union of fixed supports C. For
clarity, Dold’s written proof uses Proposition1.3 to compute every endpoint index on the common
support class o_C in H_n(R^n,R^n\C;Z); v↦v−H(t,v) is a continuous homotopy of that fixed pair into
(R^n,R^n\{0}), so its induced homomorphism is independent of t. Therefore I(G,R^n)=I(B,R^n)=±1. If
Fix(G) were empty, the relative support group H_n(R^n,R^n;Z) would be zero, and Dold Definition1.2
would give I(G,R^n)=0, equivalently the empty-fixed-set law in the G9 provider. This contradicts
the nonzero endpoint index, hence Fix(G) is nonempty. This is the existence consequence of
Franks’s published homotopy/index argument. Franks subsequently uses Anosov isolation, finite
additivity and equal local signs to prove uniqueness; none of those subsequent hypotheses or
conclusions is invoked here. The homological index on R^n permits a nonisolated compact Fix(G). No
Brouwer self-map construction or Lefschetz trace normalization is used.

7. Transfer existence through the actual pullback cover
Choose v with G(v)=v. Since G=Q∘F∘Q⁻¹ and Q is a homeomorphism, ξ=Q⁻¹(v) satisfies F(ξ)=ξ. The
literal lift identity p∘F=f^m∘p gives f^m(pξ)=pξ. This is the projection argument of Franks
Corollary1.3 p.119 for the present actual pullback cover. Only the fixed-point equation is
transferred through Q; no smooth atlas, derivative, Anosov property or orientation is transported
through the merely topological q. No ENR conjugacy-invariance theorem is needed, since the index
was used solely on the topological Euclidean coordinate map G.

8. Hyperbolic and zero-dimensional cases
If A has no complex eigenvalue of modulus one, apply linear.hyperbolic_real_splitting. If A^m v=v
for m≥1, the all-integer A-orbit of v is the finite set {v,Av,…,A^(m−1)v}, hence bounded, so the
source bounded-orbit consequence gives v=0. Thus I−A^m has zero real kernel and is invertible;
equivalently its complexification has no eigenvalue 1. This proves the hyperbolic specialization
for every positive iterate without relying on unrecorded spectral mapping. For n=0 the torus, P
and R^0 are singletons, so every lift fixes the unique point and the construction has its literal
zero-dimensional meaning. The conclusion is existence only; it does not assert uniqueness or that
hyperbolicity follows from the topological assumptions.

-/
theorem original_torus_lift_fixed_point_existence
    (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [CompactSpace M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ∞ M]
    (q : M ≃ₜ UnitAddTorus (Fin n))
    (f : Diffeomorph (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) M M ∞)
    (A : Matrix.GeneralLinearGroup (Fin n) ℤ)
    (c : Path (0 : UnitAddTorus (Fin n)) (q (f (q.symm 0))))
    (hA : ∀ z : Fin n → ℤ,
      (c.trans (((originalTorusIntegerLoop z).map
        (q.continuous.comp (f.continuous.comp q.symm.continuous))).trans c.symm)).Homotopic
        (originalTorusIntegerLoop ((A : Matrix (Fin n) (Fin n) ℤ).mulVec z))) :
    let AC := ((A : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℂ)).mulVecLin
    (∀ m : ℕ, 1 ≤ m → ¬ Module.End.HasEigenvalue (AC ^ m) 1 →
      ∀ F : C(OriginalTorusPullback q, OriginalTorusPullback q),
        (∀ ξ, (F ξ).val.1 = (f : M → M)^[m] ξ.val.1) →
        ∃ ξ, F ξ = ξ ∧ (f : M → M)^[m] ξ.val.1 = ξ.val.1) ∧
    ((∀ μ : ℂ, Module.End.HasEigenvalue AC μ → ‖μ‖ ≠ 1) →
      ∀ m : ℕ, 1 ≤ m →
        ∀ F : C(OriginalTorusPullback q, OriginalTorusPullback q),
          (∀ ξ, (F ξ).val.1 = (f : M → M)^[m] ξ.val.1) →
          ∃ ξ, F ξ = ξ ∧ (f : M → M)^[m] ξ.val.1 = ξ.val.1) := by
  classical
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (OriginalTorusPullback q) := ⟨fun x y ↦
      (pullbackCoordinates q).injective (Subsingleton.elim _ _)⟩
    have hfix : ∀ (m : ℕ) (F : C(OriginalTorusPullback q, OriginalTorusPullback q)),
        (∀ ξ, (F ξ).val.1 = (f : M → M)^[m] ξ.val.1) →
        ∃ ξ, F ξ = ξ ∧ (f : M → M)^[m] ξ.val.1 = ξ.val.1 := by
      intro m F hF
      let ξ := (pullbackCoordinates q).symm 0
      have hfξ : F ξ = ξ := Subsingleton.elim _ _
      exact ⟨ξ, hfξ, by simpa only [hfξ] using (hF ξ).symm⟩
    exact ⟨fun m _ _ F hF ↦ hfix m F hF, fun _ m _ F hF ↦ hfix m F hF⟩
  · have hfirst : ∀ m : ℕ, 1 ≤ m →
        ¬ Module.End.HasEigenvalue
          (((A : Matrix (Fin n) (Fin n) ℤ).map (Int.castRingHom ℂ)).mulVecLin ^ m) 1 →
        ∀ F : C(OriginalTorusPullback q, OriginalTorusPullback q),
          (∀ ξ, (F ξ).val.1 = (f : M → M)^[m] ξ.val.1) →
          ∃ ξ, F ξ = ξ ∧ (f : M → M)^[m] ξ.val.1 = ξ.val.1 := by
      intro m hm hspec F hF
      let g : C(UnitAddTorus (Fin n), UnitAddTorus (Fin n)) :=
        ⟨fun x ↦ q (f (q.symm x)),
          q.continuous.comp (f.continuous.comp q.symm.continuous)⟩
      have hp : IsCoveringMap (originalTorusProjection n) :=
        (coordinateProjection_cover n).isCoveringMap
      have hsurj : Function.Surjective (originalTorusProjection n) :=
        (coordinateProjection_cover n).toIsQuotientMap.surjective
      have hloop (z : Fin n → ℤ) : integralLoop n z = originalTorusIntegerLoop z := by
        ext t i
        rfl
      apply original_fixed_lift_from_monodromy q f f.continuous
        (A : Matrix (Fin n) (Fin n) ℤ) hp hsurj ?_ m hspec F hF
      intro H hH z
      apply chosen_lift_zero_increment g c H H.continuous hH z
        ((A : Matrix (Fin n) (Fin n) ℤ).mulVec z)
      simpa only [hloop] using hA z
    exact ⟨hfirst, fun hhyper m hm F hF ↦
      hfirst m hm (hyperbolic_power_not_one n _ hhyper m (by omega)) F hF⟩


end HolomorphicAnosov.Topology
