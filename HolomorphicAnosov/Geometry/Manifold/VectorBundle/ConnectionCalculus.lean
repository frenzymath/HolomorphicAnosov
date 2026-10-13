import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.SmoothTangentFieldOfHolomorphic
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.LocalChartConjugacyDerivative
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.ScalarDifferentialChartTransportG12
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.PullbackCoordinateFormChartTransport
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.CompatibleDolbeaultRepresentation
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.LocalFrameConnectionForm
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.HolomorphicFrameRestrict
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.FiniteLocalConnectionCompatible
import Mathlib.Geometry.Manifold.PartitionOfUnity
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.BottInvolutiveOfCompatible
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.BottLiftIndependentOfCompatible
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.LocalCompatibleSeed
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.QuotientFrameMultiplierSmooth
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.ConcretePullbackConnectionExists
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.CurvatureRepresentativeUnique
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.CurvatureLocalPullbackFormula
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.CurvatureExistenceGluing
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.LocalSmoothLift
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.SmoothCompatibleDifferenceExistsUnique

import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.CovariantDerivativeSectionCongr
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.FiniteLocalFormsCoordinateSmooth
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.FrameDifferenceIndependent
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.PullbackScalarDifference
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ConnectionCalculus.HolomorphicFrameCover

/-! This file develops compatible connections on the quotient tangent line, including local lifts,
existence, scalar differences, pullbacks, and curvature. (Zhang, §2.1, Definition 2.1, (2)–(5),
pp.4–5 and p.6; Demailly, V §§1–3, pp.253–256, §11, p.267 and (14.1), p.273) -/

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace HolomorphicAnosov
namespace ConnectionCalculus

universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
  [T2Space X] [SecondCountableTopology X] [CompactSpace X]

/-- A holomorphic involutive tangent subbundle with quotient rank one on a compact complex manifold
admits smooth compatible quotient-line connections, with local lifts and lift-independent
Dolbeault and Bott operators. These connections satisfy the foliation-chart criterion, pullback
formulas, scalar-difference identities, and curvature formulas. (Zhang, §2.1, (2)–(5), pp.4–5
and p.6; Demailly, V §2, p.255, §3, p.256 and (14.1), p.273) -/
theorem zhang_connection_calculus
    (P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (hInv : ∀ (U : Opens X)
      (Y Z : (x : X) → TangentSpace (complexModel d) x),
      ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun x ↦ (⟨x, Y x⟩ : TangentBundle (complexModel d) X)) U →
      ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun x ↦ (⟨x, Z x⟩ : TangentBundle (complexModel d) X)) U →
      (∀ x ∈ U, Y x ∈ P x) → (∀ x ∈ U, Z x ∈ P x) →
      ∀ x ∈ U, QuotientLineConnection.bottBracket Y Z x ∈ P x) :
    let smoothSection := fun (U : Set X)
      (s : (x : X) → QuotientLineConnection.Fibre P x) ↦
      ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (c : OpenPartialHomeomorph X (ComplexModel d)),
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
        ContDiffOn ℝ ∞ (fun z ↦ e.coefficient s (c.symm z))
          (c.target ∩ c.symm ⁻¹' ((V : Set X) ∩ U))
    let smoothConnection := fun (D : QuotientLineConnection.Connection P) ↦
      ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (c : OpenPartialHomeomorph X (ComplexModel d)),
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
        ContDiffOn ℝ ∞ (QuotientLineConnection.coordinateForm D e c)
          (c.target ∩ c.symm ⁻¹' (V : Set X))
    let compatibleOn := fun (D : QuotientLineConnection.Connection P) (U : Set X) ↦
      (∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (x : X), x ∈ V → x ∈ U → ∀ v : TangentSpace (complexModel d) x,
        D.form V e x (complexTangentToReal d x (Complex.I • v)) =
          Complex.I * D.form V e x (complexTangentToReal d x v)) ∧
      ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (Y Z : (x : X) → TangentSpace (complexModel d) x),
        QuotientLineConnection.IsSmoothTangentField ((V : Set X) ∩ U) Y →
        QuotientLineConnection.IsSmoothTangentField ((V : Set X) ∩ U) Z →
        (∀ x ∈ (V : Set X) ∩ U, Y x ∈ P x) →
        ∀ x (hx : x ∈ V), x ∈ U →
          (1 / 2 : ℂ) •
            (QuotientLineConnection.covariantDerivative D e
              (fun y ↦ QuotientLineConnection.projection P y (Z y)) x hx
              (complexTangentToReal d x (Y x)) -
            Complex.I • QuotientLineConnection.covariantDerivative D e
              (fun y ↦ QuotientLineConnection.projection P y (Z y)) x hx
              (complexTangentToReal d x (Complex.I • Y x))) =
            QuotientLineConnection.projection P x
              (QuotientLineConnection.bottBracket Y Z x)
    let scalarSmooth := fun (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ) ↦
      ∀ (c : OpenPartialHomeomorph X (ComplexModel d)),
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
        ContDiffOn ℝ ∞ (fun z ↦ (α (c.symm z)).comp
          ((mfderiv (realModel d) (realModel d) c.symm z).comp
            (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap)) c.target
    let pullbackLaw := fun (Dp D : QuotientLineConnection.Connection P)
      (f : Biholomorph d d X X)
      (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
        mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x)) ↦
      ∀ (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (e' : QuotientLineConnection.HolomorphicFrame P W) (x : X),
        x ∈ V → f x ∈ W →
        Dp.form V e x =
          (QuotientLineConnection.imageFrameCoefficient f hf e e' x)⁻¹ •
            QuotientLineConnection.realDifferential
              (QuotientLineConnection.imageFrameCoefficient f hf e e') x +
          (D.form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x)
    let curvatureRepresents := fun (D : QuotientLineConnection.Connection P)
      (R : (x : X) → TangentSpace (realModel d) x →L[ℝ]
        (TangentSpace (realModel d) x →L[ℝ] ℂ)) ↦
      ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (c : OpenPartialHomeomorph X (ComplexModel d)),
        c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
        ∀ z ∈ c.target ∩ c.symm ⁻¹' (V : Set X), ∀ v w : ComplexModel d,
          R (c.symm z)
            (mfderiv (realModel d) (realModel d) c.symm z
              ((NormedSpace.fromTangentSpace z).symm v))
            (mfderiv (realModel d) (realModel d) c.symm z
              ((NormedSpace.fromTangentSpace z).symm w)) =
            fderiv ℝ (QuotientLineConnection.coordinateForm D e c) z v w -
              fderiv ℝ (QuotientLineConnection.coordinateForm D e c) z w v
    
    (∀ x : X, ∃ V : Opens X, x ∈ V ∧
      Nonempty (QuotientLineConnection.HolomorphicFrame P V)) ∧
    (∀ (U : Opens X) (s : (x : X) → QuotientLineConnection.Fibre P x),
      smoothSection U s → ∀ x ∈ U, ∃ W : Opens X, x ∈ W ∧ W ≤ U ∧
        ∃ T : (y : X) → TangentSpace (complexModel d) y,
          QuotientLineConnection.IsSmoothTangentField W T ∧
          ∀ y ∈ W, QuotientLineConnection.projection P y (T y) = s y) ∧
    
    (∀ (U : Opens X) (Y Z : (x : X) → TangentSpace (complexModel d) x),
      QuotientLineConnection.IsSmoothTangentField U Y →
      QuotientLineConnection.IsSmoothTangentField U Z →
      (∀ x ∈ U, Y x ∈ P x) → (∀ x ∈ U, Z x ∈ P x) →
      ∀ x ∈ U, QuotientLineConnection.bottBracket Y Z x ∈ P x) ∧
    (∀ (U : Opens X) (Y T T' : (x : X) → TangentSpace (complexModel d) x),
      QuotientLineConnection.IsSmoothTangentField U Y →
      QuotientLineConnection.IsSmoothTangentField U T →
      QuotientLineConnection.IsSmoothTangentField U T' →
      (∀ x ∈ U, Y x ∈ P x) →
      (∀ x ∈ U, QuotientLineConnection.projection P x (T x) =
        QuotientLineConnection.projection P x (T' x)) →
      ∀ x ∈ U, QuotientLineConnection.projection P x
        (QuotientLineConnection.bottBracket Y T x) =
        QuotientLineConnection.projection P x
          (QuotientLineConnection.bottBracket Y T' x)) ∧
    
    (∀ (U : Opens X) (T T' : (x : X) → TangentSpace (complexModel d) x),
      QuotientLineConnection.IsSmoothTangentField U T →
      QuotientLineConnection.IsSmoothTangentField U T' →
      (∀ x ∈ U, QuotientLineConnection.projection P x (T x) =
        QuotientLineConnection.projection P x (T' x)) →
      ∀ x ∈ U, ∀ v : TangentSpace (complexModel d) x,
        QuotientLineConnection.projection P x (vectorDolbeault T x v) =
          QuotientLineConnection.projection P x (vectorDolbeault T' x v)) ∧
    (∀ D : QuotientLineConnection.Connection P, QuotientLineConnection.IsCompatible D →
      ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (T : (x : X) → TangentSpace (complexModel d) x),
        QuotientLineConnection.IsSmoothTangentField V T →
        ∀ x (hx : x ∈ V) (v : TangentSpace (complexModel d) x),
          (1 / 2 : ℂ) •
            (QuotientLineConnection.covariantDerivative D e
              (fun y ↦ QuotientLineConnection.projection P y (T y)) x hx
              (complexTangentToReal d x v) +
            Complex.I • QuotientLineConnection.covariantDerivative D e
              (fun y ↦ QuotientLineConnection.projection P y (T y)) x hx
              (complexTangentToReal d x (Complex.I • v))) =
            QuotientLineConnection.projection P x (vectorDolbeault T x v)) ∧
    
    (∃ D : QuotientLineConnection.Connection P,
      smoothConnection D ∧ QuotientLineConnection.IsCompatible D) ∧
    
    (∀ (c : OpenPartialHomeomorph X (ComplexModel d)) (j : Fin d),
      c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      (∀ x ∈ c.source, P x = LinearMap.ker
        (((ContinuousLinearMap.proj j).comp
          ((tangentSpaceCastModel (complexModel d) (c x)).toContinuousLinearMap.comp
            (mfderiv (complexModel d) (complexModel d) c x))).toLinearMap)) →
      ∃ e : QuotientLineConnection.HolomorphicFrame P ⟨c.source, c.open_source⟩,
        (∀ x (hx : x ∈ c.source) (v : TangentSpace (complexModel d) x),
          e.coordinate x hx (QuotientLineConnection.projection P x v) =
            tangentSpaceCastModel (complexModel d) (c x)
              (mfderiv (complexModel d) (complexModel d) c x v) j) ∧
        ∀ D : QuotientLineConnection.Connection P, smoothConnection D →
          (compatibleOn D c.source ↔
            ∃ a : ComplexModel d → ℂ, ContDiffOn ℝ ∞ a c.target ∧
              ∀ z ∈ c.target, QuotientLineConnection.coordinateForm D e c z =
                a z • (ContinuousLinearMap.proj j : ComplexModel d →L[ℂ] ℂ).restrictScalars ℝ)) ∧
    
    (∀ (f : Biholomorph d d X X)
      (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
        mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x)),
      ∃ Q : (x : X) → QuotientLineConnection.Fibre P x ≃L[ℂ]
          QuotientLineConnection.Fibre P (f x),
        (∀ x, (Q x).toLinearMap = QuotientLineConnection.quotientDerivative f hf x) ∧
        ∀ D : QuotientLineConnection.Connection P, smoothConnection D →
          ∃ Dp : QuotientLineConnection.Connection P, smoothConnection Dp ∧
            pullbackLaw Dp D f hf ∧
            (QuotientLineConnection.IsCompatible D →
              QuotientLineConnection.IsCompatible Dp) ∧
            ∀ (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
              (e' : QuotientLineConnection.HolomorphicFrame P W)
              (s : (y : X) → QuotientLineConnection.Fibre P y),
              smoothSection V s → ∀ x (hx : x ∈ V) (hfx : f x ∈ W)
                (v : TangentSpace (realModel d) x),
                QuotientLineConnection.covariantDerivative Dp e s x hx v =
                  (Q x).symm (QuotientLineConnection.covariantDerivative D e'
                    (fun y ↦ Eq.mp (congrArg (QuotientLineConnection.Fibre P)
                      (f.apply_symm_apply y)) (Q (f.symm y) (s (f.symm y))))
                    (f x) hfx (mfderiv (realModel d) (realModel d) f x v))) ∧
    
    (∀ D D' : QuotientLineConnection.Connection P,
      smoothConnection D → smoothConnection D' →
      ∃! α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ,
        scalarSmooth α ∧
        (∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
          (x : X), x ∈ V → D'.form V e x = D.form V e x + α x) ∧
        (QuotientLineConnection.IsCompatible D → QuotientLineConnection.IsCompatible D' →
          ∀ x (v : TangentSpace (complexModel d) x),
            α x (complexTangentToReal d x (Complex.I • v)) =
              Complex.I * α x (complexTangentToReal d x v) ∧
            (v ∈ P x → α x (complexTangentToReal d x v) = 0))) ∧
    
    (∀ (f : Biholomorph d d X X)
      (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
        mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x))
      (D D' Dp Dp' : QuotientLineConnection.Connection P)
      (α : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ),
      pullbackLaw Dp D f hf → pullbackLaw Dp' D' f hf →
      (∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (x : X), x ∈ V → D'.form V e x = D.form V e x + α x) →
      ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (x : X), x ∈ V → Dp'.form V e x = Dp.form V e x +
          (α (f x)).comp (mfderiv (realModel d) (realModel d) f x)) ∧
    
    (∀ D : QuotientLineConnection.Connection P, smoothConnection D →
      ∃! R : (x : X) → TangentSpace (realModel d) x →L[ℝ]
          (TangentSpace (realModel d) x →L[ℝ] ℂ),
        curvatureRepresents D R ∧ ∀ x (v : TangentSpace (realModel d) x), R x v v = 0) ∧
    (∀ (f : Biholomorph d d X X)
      (hf : ∀ x (v : TangentSpace (complexModel d) x), v ∈ P x →
        mfderiv (complexModel d) (complexModel d) f x v ∈ P (f x))
      (D Dp : QuotientLineConnection.Connection P),
      smoothConnection D → smoothConnection Dp → pullbackLaw Dp D f hf →
      ∀ (R Rp : (x : X) → TangentSpace (realModel d) x →L[ℝ]
          (TangentSpace (realModel d) x →L[ℝ] ℂ)),
        curvatureRepresents D R → curvatureRepresents Dp Rp →
        ∀ x (v w : TangentSpace (realModel d) x),
          Rp x v w = R (f x) (mfderiv (realModel d) (realModel d) f x v)
            (mfderiv (realModel d) (realModel d) f x w)) := by
  classical
  intro smoothSection smoothConnection compatibleOn scalarSmooth pullbackLaw curvatureRepresents
  have hcover := holomorphic_frame_cover P hP hline
  
  
  obtain ⟨D₀, hD₀smooth, hD₀compatible⟩ :
      ∃ D : QuotientLineConnection.Connection P,
        smoothConnection D ∧ QuotientLineConnection.IsCompatible D := by
    
    
    
    obtain ⟨k, O, e₀, A, hO, hBs, hA, hBott⟩ :
        ∃ (k : ℕ) (O : Fin k → Opens X)
          (e₀ : ∀ i, QuotientLineConnection.HolomorphicFrame P (O i))
          (A : ∀ i : Fin k, (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ),
          (∀ x : X, ∃ i, x ∈ O i) ∧
          (∀ i (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
            (c : OpenPartialHomeomorph X (ComplexModel d)),
            c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
            ContDiffOn ℝ ∞ (fun z ↦ (localFrameConnectionForm (e₀ i) (A i) V e (c.symm z)).comp
              ((mfderiv (realModel d) (realModel d) c.symm z).comp
                (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap))
              (c.target ∩ c.symm ⁻¹' ((V : Set X) ∩ (O i : Set X)))) ∧
          (∀ i (x : X), x ∈ O i → ∀ v : TangentSpace (complexModel d) x,
            A i x (complexTangentToReal d x (Complex.I • v)) =
              Complex.I * A i x (complexTangentToReal d x v)) ∧
          (∀ i (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
            (Y Z : (x : X) → TangentSpace (complexModel d) x),
            QuotientLineConnection.IsSmoothTangentField V Y →
            QuotientLineConnection.IsSmoothTangentField V Z →
            (∀ x ∈ V, Y x ∈ P x) → ∀ x (hx : x ∈ V), x ∈ O i →
            let s := fun y ↦ QuotientLineConnection.projection P y (Z y)
            let D := fun v ↦ (e.coordinate x hx).symm
              (QuotientLineConnection.realDifferential (e.coefficient s) x v +
                e.coefficient s x * localFrameConnectionForm (e₀ i) (A i) V e x v)
            (1 / 2 : ℂ) • (D (complexTangentToReal d x (Y x)) -
              Complex.I • D (complexTangentToReal d x (Complex.I • Y x))) =
              QuotientLineConnection.projection P x
                (QuotientLineConnection.bottBracket Y Z x)) := by
      have hlocal : ∀ a : X, ∃ (O : Opens X)
        (e₀ : QuotientLineConnection.HolomorphicFrame P O)
        (A : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ),
        a ∈ O ∧
        (∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
          (c : OpenPartialHomeomorph X (ComplexModel d)),
          c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
          ContDiffOn ℝ ∞ (fun z ↦ (localFrameConnectionForm e₀ A V e (c.symm z)).comp
            ((mfderiv (realModel d) (realModel d) c.symm z).comp
              (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap))
            (c.target ∩ c.symm ⁻¹' ((V : Set X) ∩ (O : Set X)))) ∧
        (∀ (x : X), x ∈ O → ∀ v : TangentSpace (complexModel d) x,
          A x (complexTangentToReal d x (Complex.I • v)) =
            Complex.I * A x (complexTangentToReal d x v)) ∧
        (∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
          (Y Z : (x : X) → TangentSpace (complexModel d) x),
          QuotientLineConnection.IsSmoothTangentField V Y →
          QuotientLineConnection.IsSmoothTangentField V Z →
          (∀ x ∈ V, Y x ∈ P x) → ∀ x (hx : x ∈ V), x ∈ O →
          let s := fun y ↦ QuotientLineConnection.projection P y (Z y)
          let D := fun v ↦ (e.coordinate x hx).symm
            (QuotientLineConnection.realDifferential (e.coefficient s) x v +
              e.coefficient s x * localFrameConnectionForm e₀ A V e x v)
          (1 / 2 : ℂ) • (D (complexTangentToReal d x (Y x)) -
            Complex.I • D (complexTangentToReal d x (Complex.I • Y x))) =
            QuotientLineConnection.projection P x
              (QuotientLineConnection.bottBracket Y Z x)) := by
        intro a
        obtain ⟨s, hs⟩ := exists_local_compatible_seed P hP hline hInv a
        exact ⟨s.O, s.e₀, s.A, hs, s.smooth, s.typeOne, s.bott⟩
      choose O e A hxO hBs hA hBott using hlocal
      obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun a ↦ (O a : Set X))
        (fun a ↦ (O a).isOpen)
        (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hxO x⟩)
      let index : Fin (Fintype.card t) → X :=
        fun i ↦ ((Fintype.equivFin t).symm i).val
      refine ⟨Fintype.card t, (fun i ↦ O (index i)), (fun i ↦ e (index i)),
        (fun i ↦ A (index i)), ?_, (fun i ↦ hBs (index i)),
        (fun i ↦ hA (index i)), (fun i ↦ hBott (index i))⟩
      intro x
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
      obtain ⟨hat, hxa⟩ := Set.mem_iUnion.mp ha
      refine ⟨(Fintype.equivFin t) ⟨a, hat⟩, ?_⟩
      simpa [index] using hxa
    let B := fun i V e ↦ localFrameConnectionForm (e₀ i) (A i) V e
    have hproperties := fun i ↦
      local_frame_forms_gauge_and_type_one hP hline (e₀ i) (A i) (hA i)
    have hB := fun i ↦ (hproperties i).1
    have hDol := fun i ↦ (hproperties i).2
    obtain ⟨ρ, hρO⟩ := SmoothPartitionOfUnity.exists_isSubordinate (realModel d)
      isClosed_univ (fun i ↦ (O i : Set X)) (fun i ↦ (O i).isOpen)
      (by intro x _; obtain ⟨i, hi⟩ := hO x; exact mem_iUnion.mpr ⟨i, hi⟩)
    let w : Fin k → X → ℂ := fun i x ↦ (ρ i x : ℂ)
    have hwts : ∀ i, tsupport (w i) ⊆ O i := by
      intro i
      simpa [w, tsupport, Function.support] using hρO i
    have hws : ∀ i, Function.support (w i) ⊆ O i :=
      fun i ↦ (subset_closure).trans (hwts i)
    have hwsum : ∀ x, ∑ i, w i x = 1 := by
      intro x
      have hsum := ρ.sum_eq_one (x := x) (mem_univ x)
      simpa only [finsum_eq_sum_of_fintype, w, ← Complex.ofReal_sum,
        Complex.ofReal_one] using congrArg Complex.ofReal hsum
    refine ⟨finiteLocalConnection O w hws hwsum B hB, ?_,
      finiteLocalConnection_compatible O w hws hwsum B hB hDol hBott⟩
    intro V e c hc
    apply finite_local_forms_coordinate_smooth O V w hwts
      (fun i ↦ B i V e) c ?_ (fun i ↦ hBs i V e c hc)
    intro i
    have hcs : ContMDiffOn (realModel d) (realModel d) ∞ c.symm c.target := by
      intro z hz
      obtain ⟨hcont, hreg⟩ := contMDiffWithinAt_iff.mp
        ((contMDiffOn_symm_of_mem_maximalAtlas hc) z hz)
      exact contMDiffWithinAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩
    have hρc : ContDiffOn ℝ ∞ (fun z ↦ ρ i (c.symm z)) c.target := by
      simpa only [contMDiffOn_iff_contDiffOn, Function.comp_def] using
        (ρ i).contMDiff.comp_contMDiffOn hcs
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn hρc
  
  have hDol : (∀ D : QuotientLineConnection.Connection P, QuotientLineConnection.IsCompatible D →
      ∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (T : (x : X) → TangentSpace (complexModel d) x),
        QuotientLineConnection.IsSmoothTangentField V T →
        ∀ x (hx : x ∈ V) (v : TangentSpace (complexModel d) x),
          (1 / 2 : ℂ) •
            (QuotientLineConnection.covariantDerivative D e
              (fun y ↦ QuotientLineConnection.projection P y (T y)) x hx
              (complexTangentToReal d x v) +
            Complex.I • QuotientLineConnection.covariantDerivative D e
              (fun y ↦ QuotientLineConnection.projection P y (T y)) x hx
              (complexTangentToReal d x (Complex.I • v))) =
            QuotientLineConnection.projection P x (vectorDolbeault T x v)) := by
    exact compatible_dolbeault_representation hP hline
  refine ⟨hcover, local_smooth_lift hcover, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    smooth_compatible_difference_exists_unique hP hcover,
    pullback_scalar_difference hcover, ?_, ?_⟩
  · exact bott_involutive_of_compatible hcover D₀ hD₀compatible
  · exact bott_lift_independent_of_compatible hcover D₀ hD₀compatible
  · intro U T T' hT hT' hTT' x hx v
    obtain ⟨V, hxV, ⟨e⟩⟩ := hcover x
    let W : Opens X := U ⊓ V
    let eW : QuotientLineConnection.HolomorphicFrame P W :=
      holomorphicFrameRestrict e inf_le_right
    have hxW : x ∈ W := ⟨hx, hxV⟩
    rw [← hDol D₀ hD₀compatible W eW T (hT.mono inter_subset_left) x hxW v,
      ← hDol D₀ hD₀compatible W eW T' (hT'.mono inter_subset_left) x hxW v]
    have hcongr (w : TangentSpace (realModel d) x) :=
      covariantDerivative_section_congr D₀ W eW
        (fun y ↦ QuotientLineConnection.projection P y (T y))
        (fun y ↦ QuotientLineConnection.projection P y (T' y))
        (fun y hy ↦ hTT' y hy.1) x hxW w
    rw [hcongr, hcongr]
  · exact hDol
  · exact ⟨D₀, hD₀smooth, hD₀compatible⟩
  · intro c j hc hker
    have hcd : c.MDifferentiable (complexModel d) (complexModel d) := by
      constructor
      · intro x hx
        exact ((contMDiffAt_of_mem_maximalAtlas hc hx).mdifferentiableAt
          (by simp)).mdifferentiableWithinAt
      · intro z hz
        exact ((contMDiffAt_symm_of_mem_maximalAtlas hc hz).mdifferentiableAt
          (by simp)).mdifferentiableWithinAt
    let Tb (b : ComplexModel d) : (x : X) → TangentSpace (complexModel d) x :=
      VectorField.mpullback (complexModel d) (complexModel d) c (fun _ ↦ b)
    let T := Tb (Pi.single j 1)
    have hi (x : X) (hx : x ∈ c.source) :
        (mfderiv (complexModel d) (complexModel d) c x).IsInvertible :=
      ⟨hcd.mfderiv hx, rfl⟩
    have hTb (b : ComplexModel d) : ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun x ↦ (⟨x, Tb b x⟩ : TangentBundle (complexModel d) X)) c.source := by
      intro x hx
      have hconst : ContMDiffAt (complexModel d) (complexModel d).tangent ∞
          (fun y : ComplexModel d ↦
            (⟨y, b⟩ : TangentBundle (complexModel d) (ComplexModel d))) (c x) := by
        exact contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
      exact (hconst.mpullback_vectorField_preimage
        (contMDiffAt_of_mem_maximalAtlas hc hx) (hi x hx) (by simp)).contMDiffWithinAt
    have hT := hTb (Pi.single j 1)
    let θ (x : X) : TangentSpace (complexModel d) x →ₗ[ℂ] ℂ :=
      ((ContinuousLinearMap.proj j).comp
        ((tangentSpaceCastModel (complexModel d) (c x)).toContinuousLinearMap.comp
          (mfderiv (complexModel d) (complexModel d) c x))).toLinearMap
    have hθT (x : X) (hx : x ∈ c.source) : θ x (T x) = 1 := by
      change (mfderiv (complexModel d) (complexModel d) c x
        ((mfderiv (complexModel d) (complexModel d) c x).inverse (Pi.single j 1))) j = 1
      rw [(hi x hx).self_apply_inverse]
      simp
    let L (x : X) (hx : x ∈ c.source) : QuotientLineConnection.Fibre P x ≃ₗ[ℂ] ℂ :=
      LinearEquiv.ofBijective ((P x).liftQ (θ x) (hker x hx).le) (by
        constructor
        · apply LinearMap.ker_eq_bot.mp
          exact (P x).ker_liftQ_eq_bot (θ x) (hker x hx).le (hker x hx).ge
        · intro a
          refine ⟨(P x).mkQ (a • T x), ?_⟩
          change θ x (a • T x) = a
          simp [hθT x hx])
    let e : QuotientLineConnection.HolomorphicFrame P ⟨c.source, c.open_source⟩ :=
      { sectionValue := fun x ↦ (P x).mkQ (T x)
        holomorphic := fun x hx ↦
          ⟨c.source, T, c.open_source, hx, Subset.rfl, hT, fun _ _ ↦ rfl⟩
        coordinate := L
        normalized := hθT }
    refine ⟨e, (fun x hx v ↦ rfl), ?_⟩
    have hcr (x : X) (hx : x ∈ c.source) :
        ContMDiffAt (realModel d) (realModel d) ∞ c x := by
      obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp
        (contMDiffAt_of_mem_maximalAtlas hc hx)
      exact contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩
    have hder (x : X) (hx : x ∈ c.source) :
        mfderiv (realModel d) (realModel d) c x =
          (mfderiv (complexModel d) (complexModel d) c x).restrictScalars ℝ := by
      have hf := (contMDiffAt_of_mem_maximalAtlas hc hx).mdifferentiableAt (by simp)
      have hr := (hcr x hx).mdifferentiableAt (by simp)
      ext v
      apply (tangentSpaceCastModel (realModel d) (c x)).injective
      rw [hf.mfderiv_abuse, hr.mfderiv_abuse]
      have hd := hf.differentiableWithinAt_writtenInExtChartAt
      change (fderivWithin ℝ (writtenInExtChartAt (complexModel d) (complexModel d) x c)
        (range (complexModel d)) (extChartAt (complexModel d) x x)) v =
        (fderivWithin ℂ (writtenInExtChartAt (complexModel d) (complexModel d) x c)
        (range (complexModel d)) (extChartAt (complexModel d) x x)) v
      exact congrArg (fun L ↦ L v) (hd.restrictScalars_fderivWithin ℝ (by simp)).symm
    have hTbR (b : ComplexModel d) (x : X) (hx : x ∈ c.source) :
        complexTangentToReal d x (Tb b x) =
          VectorField.mpullback (realModel d) (realModel d) c (fun _ ↦ b) x := by
      simp only [Tb, VectorField.mpullback_apply, hder x hx]
      have hci := hi x hx
      have hir : ((mfderiv (complexModel d) (complexModel d) c x).restrictScalars ℝ).IsInvertible := by
        obtain ⟨a, ha⟩ := hci
        exact ⟨a.restrictScalars ℝ, congrArg (ContinuousLinearMap.restrictScalars ℝ) ha⟩
      apply hir.injective
      erw [hir.self_apply_inverse]
      change mfderiv (complexModel d) (complexModel d) c x
        ((mfderiv (complexModel d) (complexModel d) c x).inverse b) = b
      exact hci.self_apply_inverse b
    let : IsManifold (realModel d) (minSmoothness ℝ 2) X :=
      IsManifold.of_le (n := ∞) (by simp)
    have hbr (b b' : ComplexModel d) (x : X) (hx : x ∈ c.source) :
        QuotientLineConnection.bottBracket (Tb b) (Tb b') x = 0 := by
      have hb (a a' : ComplexModel d) :
          VectorField.mlieBracket (realModel d)
            (fun y ↦ complexTangentToReal d y (Tb a y))
            (fun y ↦ complexTangentToReal d y (Tb a' y)) x = 0 := by
        have hcst (a : ComplexModel d) : MDifferentiableAt (realModel d) (realModel d).tangent
            (fun y : ComplexModel d ↦
              (⟨y, a⟩ : TangentBundle (realModel d) (ComplexModel d))) (c x) :=
          (contMDiffAt_vectorSpace_iff_contDiffAt.mpr (contDiffAt_const (n := ∞))).mdifferentiableAt
            (by simp)
        have hh := VectorField.mpullback_mlieBracket (hcst a) (hcst a') (hcr x hx) (by simp)
        have he (a : ComplexModel d) :
            (fun y ↦ complexTangentToReal d y (Tb a y)) =ᶠ[𝓝 x]
              VectorField.mpullback (realModel d) (realModel d) c (fun _ ↦ a) := by
          filter_upwards [c.open_source.mem_nhds hx] with y hy
          exact hTbR a y hy
        rw [(he a).mlieBracket_vectorField_eq (he a')]
        rw [← hh]
        simp only [VectorField.mpullback_apply, VectorField.mlieBracket,
          VectorField.mlieBracketWithin_eq_lieBracketWithin, VectorField.lieBracketWithin_univ,
          VectorField.lieBracket]
        erw [fderiv_const, fderiv_const]
        change (mfderiv (realModel d) (realModel d) c x).inverse
          (0 - 0 : TangentSpace (realModel d) (c x)) = 0
        simp only [sub_self, map_zero]
      have hIb (a : ComplexModel d) (y : X) :
          Complex.I • Tb a y = Tb (Complex.I • a) y := by
        simp only [Tb, VectorField.mpullback_apply, map_smul]
      simp only [QuotientLineConnection.bottBracket, hIb, hb]
      simp
    let O : Opens X := ⟨c.source, c.open_source⟩
    have hcdR : c.MDifferentiable (realModel d) (realModel d) := by
      constructor
      · intro x hx
        exact ((hcr x hx).mdifferentiableAt (by simp)).mdifferentiableWithinAt
      · intro z hz
        obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp
          (contMDiffAt_symm_of_mem_maximalAtlas hc hz)
        exact ((contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩).mdifferentiableAt
          (by simp)).mdifferentiableWithinAt
    have hcoord (D : QuotientLineConnection.Connection P) (z : ComplexModel d)
        (hz : z ∈ c.target) (b : ComplexModel d) :
        QuotientLineConnection.coordinateForm D e c z b =
          D.form O e (c.symm z) (complexTangentToReal d (c.symm z) (Tb b (c.symm z))) := by
      change D.form O e (c.symm z) (mfderiv (realModel d) (realModel d) c.symm z b) = _
      congr 1
      rw [hTbR b _ (c.map_target hz)]
      apply (hcdR.mfderiv (c.map_target hz)).injective
      have hiR : (mfderiv (realModel d) (realModel d) c (c.symm z)).IsInvertible :=
        ⟨hcdR.mfderiv (c.map_target hz), rfl⟩
      have hcomp := congrArg (fun L ↦ L b) (hcdR.comp_symm_deriv hz)
      change _ = b at hcomp
      exact hcomp.trans (hiR.self_apply_inverse b).symm
    have hθb (b : ComplexModel d) (x : X) (hx : x ∈ c.source) :
        θ x (Tb b x) = b j := by
      change (mfderiv (complexModel d) (complexModel d) c x
        ((mfderiv (complexModel d) (complexModel d) c x).inverse b)) j = b j
      rw [(hi x hx).self_apply_inverse]
    have hcoeff (x : X) (hx : x ∈ c.source) :
        e.coefficient (fun y ↦ QuotientLineConnection.projection P y (T y)) x = 1 := by
      unfold QuotientLineConnection.HolomorphicFrame.coefficient
      split_ifs with hh
      · exact hθT x hx
      · exact False.elim (hh hx)
    have hdcoeff (x : X) (hx : x ∈ c.source) :
        QuotientLineConnection.realDifferential (d := d)
          (e.coefficient (fun y ↦ QuotientLineConnection.projection P y (T y))) x = 0 := by
      have heq : e.coefficient (fun y ↦ QuotientLineConnection.projection P y (T y))
          =ᶠ[𝓝 x] (fun _ ↦ (1 : ℂ)) := by
        filter_upwards [c.open_source.mem_nhds hx] with y hy
        exact hcoeff y hy
      unfold QuotientLineConnection.realDifferential
      rw [heq.mfderiv_eq]
      simp
    have hvanish (D : QuotientLineConnection.Connection P)
        (hI : ∀ x ∈ c.source, ∀ v : TangentSpace (complexModel d) x,
          D.form O e x (complexTangentToReal d x (Complex.I • v)) =
            Complex.I * D.form O e x (complexTangentToReal d x v))
        (hB : ∀ b : ComplexModel d, b j = 0 → ∀ x (hx : x ∈ c.source),
          (1 / 2 : ℂ) •
            (QuotientLineConnection.covariantDerivative D e
              (fun y ↦ QuotientLineConnection.projection P y (T y)) x hx
              (complexTangentToReal d x (Tb b x)) -
            Complex.I • QuotientLineConnection.covariantDerivative D e
              (fun y ↦ QuotientLineConnection.projection P y (T y)) x hx
              (complexTangentToReal d x (Complex.I • Tb b x))) = 0)
        (b : ComplexModel d) (hb : b j = 0) (x : X) (hx : x ∈ c.source) :
        D.form O e x (complexTangentToReal d x (Tb b x)) = 0 := by
      have hh := hB b hb x hx
      apply_fun e.coordinate x hx at hh
      simp only [map_smul, map_sub, map_zero, QuotientLineConnection.covariantDerivative,
        LinearEquiv.apply_symm_apply, hcoeff x hx, hdcoeff x hx, zero_apply, zero_add,
        one_mul, smul_eq_mul] at hh
      change (1 / 2 : ℂ) * (D.form O e x (complexTangentToReal d x (Tb b x)) -
        Complex.I * D.form O e x (complexTangentToReal d x (Complex.I • Tb b x))) = 0 at hh
      rw [hI x hx] at hh
      linear_combination (norm := (ring_nf; simp [Complex.I_sq])) hh
    have hTbP (b : ComplexModel d) (hb : b j = 0) :
        ∀ x ∈ c.source, Tb b x ∈ P x := by
      intro x hx
      rw [hker x hx]
      exact (hθb b x hx).trans hb
    have hnormalform (D : QuotientLineConnection.Connection P) (hD : smoothConnection D)
        (hI : ∀ x ∈ c.source, ∀ v : TangentSpace (complexModel d) x,
          D.form O e x (complexTangentToReal d x (Complex.I • v)) =
            Complex.I * D.form O e x (complexTangentToReal d x v))
        (hzero : ∀ b : ComplexModel d, b j = 0 → ∀ x ∈ c.source,
          D.form O e x (complexTangentToReal d x (Tb b x)) = 0) :
        ∃ a : ComplexModel d → ℂ, ContDiffOn ℝ ∞ a c.target ∧
          ∀ z ∈ c.target, QuotientLineConnection.coordinateForm D e c z =
            a z • (ContinuousLinearMap.proj j : ComplexModel d →L[ℂ] ℂ).restrictScalars ℝ := by
      let a := fun z ↦ QuotientLineConnection.coordinateForm D e c z (Pi.single j 1)
      refine ⟨a, ?_, ?_⟩
      · exact ((hD O e c hc).mono (fun z hz ↦ ⟨hz, c.map_target hz⟩)).clm_apply contDiffOn_const
      · intro z hz
        let A := QuotientLineConnection.coordinateForm D e c z
        have hAI (v : ComplexModel d) : A (Complex.I • v) = Complex.I * A v := by
          dsimp [A]
          rw [hcoord D z hz, hcoord D z hz]
          have hsm : Tb (Complex.I • v) (c.symm z) = Complex.I • Tb v (c.symm z) := by
            simp only [Tb, VectorField.mpullback_apply, map_smul]
          rw [hsm, hI _ (c.map_target hz)]
        have hAc (a : ℂ) (v : ComplexModel d) : A (a • v) = a * A v := by
          conv_lhs => rw [← Complex.re_add_im a]
          simp only [add_smul, mul_smul, Complex.coe_smul, map_add, map_smul,
            hAI, Complex.real_smul]
          rw [← mul_assoc, ← add_mul, Complex.re_add_im]
        ext v
        have h0 : A (v - v j • Pi.single j 1) = 0 := by
          rw [hcoord D z hz]
          apply hzero _ _ _ (c.map_target hz)
          simp
        rw [map_sub, hAc] at h0
        exact (sub_eq_zero.mp h0).trans (mul_comm _ _)
    have hBglobal (D : QuotientLineConnection.Connection P)
        (hD : QuotientLineConnection.IsCompatible D) :
        ∀ b : ComplexModel d, b j = 0 → ∀ x (hx : x ∈ c.source),
          (1 / 2 : ℂ) •
            (QuotientLineConnection.covariantDerivative D e
              (fun y ↦ QuotientLineConnection.projection P y (T y)) x hx
              (complexTangentToReal d x (Tb b x)) -
            Complex.I • QuotientLineConnection.covariantDerivative D e
              (fun y ↦ QuotientLineConnection.projection P y (T y)) x hx
              (complexTangentToReal d x (Complex.I • Tb b x))) = 0 := by
      intro b hb x hx
      have hh := hD.2 O e (Tb b) T
        (smoothTangentField_of_holomorphic c.open_source (hTb b))
        (smoothTangentField_of_holomorphic c.open_source hT) (hTbP b hb) x hx
      simpa only [T, hbr b (Pi.single j 1) x hx, map_zero] using hh
    obtain ⟨a₀, ha₀, hA₀⟩ := hnormalform D₀ hD₀smooth
      (fun x hx ↦ hD₀compatible.1 O e x hx)
      (hvanish D₀ (fun x hx ↦ hD₀compatible.1 O e x hx) (hBglobal D₀ hD₀compatible))
    intro D hD
    constructor
    · intro hcompat
      apply hnormalform D hD (fun x hx ↦ hcompat.1 O e x hx hx)
      apply hvanish D (fun x hx ↦ hcompat.1 O e x hx hx)
      intro b hb x hx
      have hh := hcompat.2 O e (Tb b) T
        ((smoothTangentField_of_holomorphic c.open_source (hTb b)).mono inter_subset_left)
        ((smoothTangentField_of_holomorphic c.open_source hT).mono inter_subset_left)
        (fun y hy ↦ hTbP b hb y hy.1) x hx hx
      simpa only [T, hbr b (Pi.single j 1) x hx, map_zero] using hh
    · intro hform
      obtain ⟨a, ha, hA⟩ := hform
      have hnative (D : QuotientLineConnection.Connection P) (a : ComplexModel d → ℂ)
          (hA : ∀ z ∈ c.target, QuotientLineConnection.coordinateForm D e c z =
            a z • (ContinuousLinearMap.proj j : ComplexModel d →L[ℂ] ℂ).restrictScalars ℝ)
          (x : X) (hx : x ∈ c.source) (v : TangentSpace (complexModel d) x) :
          D.form O e x (complexTangentToReal d x v) = a (c x) * θ x v := by
        let b : ComplexModel d := mfderiv (complexModel d) (complexModel d) c x v
        have hb : Tb b x = v := (hi x hx).inverse_apply_self v
        have hh : QuotientLineConnection.coordinateForm D e c (c x) b =
            a (c x) * b j := by rw [hA _ (c.map_source hx)]; rfl
        rw [hcoord D _ (c.map_source hx)] at hh
        rw [c.left_inv hx] at hh
        erw [hb] at hh
        exact hh
      have hdiff (V : Opens X) (E : QuotientLineConnection.HolomorphicFrame P V)
          (x : X) (hxV : x ∈ V) (hx : x ∈ c.source)
          (v : TangentSpace (complexModel d) x) :
          D.form V E x (complexTangentToReal d x v) =
            D₀.form V E x (complexTangentToReal d x v) + (a (c x) - a₀ (c x)) * θ x v := by
        have hh := congrArg (fun A ↦ A (complexTangentToReal d x v))
          (frame_difference_independent D₀ D V O E e x hxV hx)
        simp only [sub_apply, hnative D a hA x hx, hnative D₀ a₀ hA₀ x hx] at hh
        linear_combination hh
      refine ⟨?_, ?_⟩
      · intro V E x hxV hx v
        rw [hdiff V E x hxV hx, hdiff V E x hxV hx,
          hD₀compatible.1 V E x hxV, map_smul]
        simp only [smul_eq_mul]
        ring
      · intro V E Y Z hY hZ hYP x hxV hx
        let W : Opens X := V ⊓ O
        let EW := holomorphicFrameRestrict E (show W ≤ V from inf_le_left)
        have hxW : x ∈ W := ⟨hxV, hx⟩
        have hR (s : (y : X) → QuotientLineConnection.Fibre P y)
            (v : TangentSpace (realModel d) x) :
            QuotientLineConnection.covariantDerivative D₀ EW s x hxW v =
              QuotientLineConnection.covariantDerivative D₀ E s x hxV v := by
          have hcoeffeq : EW.coefficient s =ᶠ[𝓝 x] E.coefficient s := by
            filter_upwards [W.isOpen.mem_nhds hxW] with y hy
            unfold QuotientLineConnection.HolomorphicFrame.coefficient
            rw [dite_eq_left (show y ∈ W from hy), dite_eq_left (show y ∈ V from hy.1)]
            rfl
          have htransition : E.coefficient EW.sectionValue =ᶠ[𝓝 x] (fun _ ↦ (1 : ℂ)) := by
            filter_upwards [W.isOpen.mem_nhds hxW] with y hy
            unfold QuotientLineConnection.HolomorphicFrame.coefficient
            rw [dite_eq_left (show y ∈ V from hy.1)]
            exact E.normalized y hy.1
          have hd : QuotientLineConnection.realDifferential (d := d) (E.coefficient EW.sectionValue) x = 0 := by
            unfold QuotientLineConnection.realDifferential
            rw [htransition.mfderiv_eq]
            simp
          have hform : D₀.form W EW x = D₀.form V E x := by
            ext u
            have hh := congrArg (fun A ↦ A u) (D₀.gauge V W E EW x hxV hxW)
            change D₀.form W EW x u = D₀.form V E x u +
              (E.coefficient EW.sectionValue x)⁻¹ *
                QuotientLineConnection.realDifferential (E.coefficient EW.sectionValue) x u at hh
            rw [hd, zero_apply, mul_zero, add_zero] at hh
            exact hh
          have hdc : QuotientLineConnection.realDifferential (d := d) (EW.coefficient s) x =
              QuotientLineConnection.realDifferential (E.coefficient s) x := by
            unfold QuotientLineConnection.realDifferential
            rw [hcoeffeq.eq_of_nhds, hcoeffeq.mfderiv_eq]
            rfl
          unfold QuotientLineConnection.covariantDerivative
          rw [hdc, hcoeffeq.eq_of_nhds, hform]
          rfl
        have hzero (v : TangentSpace (complexModel d) x) (hv : v ∈ P x) : θ x v = 0 := by
          rw [hker x hx] at hv
          exact hv
        have hv : Y x ∈ P x := hYP x ⟨hxV, hx⟩
        have hDI (v : TangentSpace (complexModel d) x) (hv : v ∈ P x) :
            QuotientLineConnection.covariantDerivative D E
              (fun y ↦ QuotientLineConnection.projection P y (Z y)) x hxV
              (complexTangentToReal d x v) =
            QuotientLineConnection.covariantDerivative D₀ E
              (fun y ↦ QuotientLineConnection.projection P y (Z y)) x hxV
              (complexTangentToReal d x v) := by
          unfold QuotientLineConnection.covariantDerivative
          rw [hdiff V E x hxV hx v, hzero v hv, mul_zero, add_zero]
        rw [hDI (Y x) hv, hDI (Complex.I • Y x) ((P x).smul_mem Complex.I hv)]
        have hh := hD₀compatible.2 W EW Y Z hY hZ hYP x hxW
        rw [hR, hR] at hh
        exact hh
  · intro f hf
    exact concrete_pullback_connection_exists P hP hline f hf
  · intro D hD
    obtain ⟨R, hR⟩ : ∃ R, curvatureRepresents D R := by
      obtain ⟨R, hR⟩ := exists_curvature_representative_gap P hP hline D (hD := hD)
      exact ⟨R, hR⟩
    have hparam (x : X) : Function.Surjective
        (fun v : ComplexModel d ↦
          mfderiv (realModel d) (realModel d) (chartAt (ComplexModel d) x).symm
            (chartAt (ComplexModel d) x x)
            ((NormedSpace.fromTangentSpace (chartAt (ComplexModel d) x x)).symm v)) := by
      exact ((mdifferentiable_chart (I := realModel d) x).symm.mfderiv_surjective
        (mem_chart_target (ComplexModel d) x)).comp
        (NormedSpace.fromTangentSpace (chartAt (ComplexModel d) x x)).symm.surjective
    have hdiag : ∀ x (v : TangentSpace (realModel d) x), R x v v = 0 := by
      intro x v
      obtain ⟨V, hxV, ⟨e⟩⟩ := hcover x
      obtain ⟨w, hw⟩ := hparam x v
      have hz : chartAt (ComplexModel d) x x ∈
          (chartAt (ComplexModel d) x).target ∩
            (chartAt (ComplexModel d) x).symm ⁻¹' (V : Set X) := by
        exact ⟨mem_chart_target _ x, by simpa using hxV⟩
      have hh := hR V e (chartAt (ComplexModel d) x)
        (IsManifold.chart_mem_maximalAtlas x) _ hz w w
      have hh' : R ((chartAt (ComplexModel d) x).symm (chartAt (ComplexModel d) x x))
          v v = 0 := by simpa only [hw, sub_self] using hh
      rw [(chartAt (ComplexModel d) x).left_inv (mem_chart_source _ x)] at hh'
      exact hh'
    refine ⟨R, ⟨hR, hdiag⟩, ?_⟩
    intro R' hR'
    exact curvature_representative_unique P hcover D R R' hR hR'.1
  · intro f hf D Dp hD hDp hpull R Rp hR hRp
    
    
    
    have hcoordinate_curvature
        (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (c : OpenPartialHomeomorph X (ComplexModel d))
        (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
        (F : ComplexModel d → ComplexModel d) (g : ComplexModel d → ℂ)
        (z : ComplexModel d) (hz : F z ∈ c.target ∩ c.symm ⁻¹' (V : Set X))
        (hF : ContDiffAt ℝ 2 F z) (hg : ContDiffAt ℝ 2 g z) (hg0 : g z ≠ 0)
        (v w : ComplexModel d) :
        fderiv ℝ (fun y ↦ (g y)⁻¹ • fderiv ℝ g y +
            (QuotientLineConnection.coordinateForm D e c (F y)).comp (fderiv ℝ F y)) z v w -
          fderiv ℝ (fun y ↦ (g y)⁻¹ • fderiv ℝ g y +
            (QuotientLineConnection.coordinateForm D e c (F y)).comp (fderiv ℝ F y)) z w v =
          fderiv ℝ (QuotientLineConnection.coordinateForm D e c) (F z)
              (fderiv ℝ F z v) (fderiv ℝ F z w) -
            fderiv ℝ (QuotientLineConnection.coordinateForm D e c) (F z)
              (fderiv ℝ F z w) (fderiv ℝ F z v) := by
      exact curvature_local_pullback_formula P D V e c hc hD F g z hz hF hg hg0 v w
    
    have hcoordinate_transport
        (W : Opens X) (e' : QuotientLineConnection.HolomorphicFrame P W)
        (c c' : OpenPartialHomeomorph X (ComplexModel d))
        (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
        (hc' : c' ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
        (z : ComplexModel d) (hz : z ∈ c.target)
        (hfz : f (c.symm z) ∈ c'.source) :
        ((D.form W e' (f (c.symm z))).comp
            (mfderiv (realModel d) (realModel d) f (c.symm z))).comp
          ((mfderiv (realModel d) (realModel d) c.symm z).comp
            (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap) =
        (QuotientLineConnection.coordinateForm D e' c'
            ((c' ∘ f ∘ c.symm) z)).comp (fderiv ℝ (c' ∘ f ∘ c.symm) z) := by
      have hcd : c'.MDifferentiable (realModel d) (realModel d) := by
        constructor
        · intro x hx
          obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp
            (contMDiffAt_of_mem_maximalAtlas hc' hx)
          exact (contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩).mdifferentiableAt
            (by simp) |>.mdifferentiableWithinAt
        · intro y hy
          obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp
            (contMDiffAt_symm_of_mem_maximalAtlas hc' hy)
          exact (contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩).mdifferentiableAt
            (by simp) |>.mdifferentiableWithinAt
      have hfd := local_chart_conjugacy_mfderiv f c c' (c' ∘ f ∘ c.symm) z
        hc hc' hz hfz Filter.EventuallyEq.rfl
      have hfd' : fderiv ℝ (c' ∘ f ∘ c.symm) z =
          (mfderiv (realModel d) (realModel d) c' (f (c.symm z))).comp
            ((mfderiv (realModel d) (realModel d) f (c.symm z)).comp
              (mfderiv (realModel d) (realModel d) c.symm z)) := by
        simpa only [mfderiv_eq_fderiv] using hfd
      have hbase : c'.symm (c' (f (c.symm z))) = f (c.symm z) := c'.left_inv hfz
      ext v
      simp only [ContinuousLinearMap.comp_apply, QuotientLineConnection.coordinateForm,
        Function.comp_apply]
      rw [hbase]
      change D.form W e' (f (c.symm z))
          (mfderiv (realModel d) (realModel d) f (c.symm z)
            (mfderiv (realModel d) (realModel d) c.symm z v)) =
        D.form W e' (f (c.symm z))
          (mfderiv (realModel d) (realModel d) c'.symm (c' (f (c.symm z)))
            (fderiv ℝ (c' ∘ f ∘ c.symm) z v))
      rw [hfd']
      have hinv := congrArg (fun L ↦ L
        (mfderiv (realModel d) (realModel d) f (c.symm z)
          (mfderiv (realModel d) (realModel d) c.symm z v))) (hcd.symm_comp_deriv hfz)
      exact congrArg (D.form W e' (f (c.symm z))) hinv.symm
    
    have hcoordinate_pullback
        (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (e' : QuotientLineConnection.HolomorphicFrame P W)
        (hV : ∀ x, x ∈ V → f x ∈ W)
        (c c' : OpenPartialHomeomorph X (ComplexModel d))
        (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
        (hc' : c' ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
        (z : ComplexModel d)
        (hz : z ∈ c.target ∩ c.symm ⁻¹' (V : Set X))
        (hfz : f (c.symm z) ∈ c'.source) :
        QuotientLineConnection.coordinateForm Dp e c z =
          (QuotientLineConnection.imageFrameCoefficient f hf e e' (c.symm z))⁻¹ •
            fderiv ℝ (fun w ↦ QuotientLineConnection.imageFrameCoefficient f hf e e'
              (c.symm w)) z +
          (QuotientLineConnection.coordinateForm D e' c' ((c' ∘ f ∘ c.symm) z)).comp
            (fderiv ℝ (c' ∘ f ∘ c.symm) z) := by
      have hq := (quotient_frame_multiplier_smooth P hP hline f hf e e' hV).1
      obtain ⟨hcont, hreg⟩ := contMDiffAt_iff.mp
        ((hq _ hz.2).contMDiffAt (V.isOpen.mem_nhds hz.2))
      have hg : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ)
          (QuotientLineConnection.imageFrameCoefficient f hf e e') (c.symm z) :=
        (contMDiffAt_iff.mpr ⟨hcont, hreg.restrict_scalars ℝ⟩).mdifferentiableAt (by simp)
      rw [pullback_coordinate_form_chart_transport P Dp D f hf e e' c c'
        (c' ∘ f ∘ c.symm) z hz (hV _ hz.2)
        (hpull V W e e' (c.symm z) hz.2 (hV _ hz.2))
        (hcoordinate_transport W e' c c' hc hc' z hz.1 hfz)]
      rw [ContinuousLinearMap.smul_comp,
        scalar_differential_chart_transport _ c hc z hz.1 hg]
    have hcurvature_coordinates
        (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
        (e' : QuotientLineConnection.HolomorphicFrame P W)
        (hV : ∀ x, x ∈ V → f x ∈ W)
        (c c' : OpenPartialHomeomorph X (ComplexModel d))
        (hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
        (hc' : c' ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
        (z : ComplexModel d)
        (hz : z ∈ c.target ∩ c.symm ⁻¹' (V : Set X))
        (hfz : f (c.symm z) ∈ c'.source) (v w : ComplexModel d) :
        let F := c' ∘ f ∘ c.symm
        fderiv ℝ (QuotientLineConnection.coordinateForm Dp e c) z v w -
          fderiv ℝ (QuotientLineConnection.coordinateForm Dp e c) z w v =
        fderiv ℝ (QuotientLineConnection.coordinateForm D e' c') (F z)
            (fderiv ℝ F z v) (fderiv ℝ F z w) -
          fderiv ℝ (QuotientLineConnection.coordinateForm D e' c') (F z)
            (fderiv ℝ F z w) (fderiv ℝ F z v) := by
      let F := c' ∘ f ∘ c.symm
      let g := fun y ↦ QuotientLineConnection.imageFrameCoefficient f hf e e' (c.symm y)
      have hcs := contMDiffAt_symm_of_mem_maximalAtlas hc hz.1
      have hfs := f.contMDiff.contMDiffAt.comp z hcs
      have hFs := (contMDiffAt_of_mem_maximalAtlas hc' hfz).comp z hfs
      have hF : ContDiffAt ℝ 2 F z := by
        have hFc : ContDiffAt ℂ ∞ F z := by
          simpa only [contMDiffAt_iff_contDiffAt] using hFs
        exact (hFc.restrict_scalars ℝ).of_le (by simp)
      obtain ⟨hqs, hq0⟩ := quotient_frame_multiplier_smooth P hP hline f hf e e' hV
      have hgs := ((hqs _ hz.2).contMDiffAt (V.isOpen.mem_nhds hz.2)).comp z hcs
      have hg : ContDiffAt ℝ 2 g z := by
        have hgc : ContDiffAt ℂ ∞ g z := by
          simpa only [g, Function.comp_def, contMDiffAt_iff_contDiffAt] using hgs
        exact (hgc.restrict_scalars ℝ).of_le (by simp)
      have hg0 : g z ≠ 0 := hq0 _ hz.2
      have hlocal : QuotientLineConnection.coordinateForm Dp e c =ᶠ[𝓝 z]
          (fun y ↦ (g y)⁻¹ • fderiv ℝ g y +
            (QuotientLineConnection.coordinateForm D e' c' (F y)).comp (fderiv ℝ F y)) := by
        have hVnear := hcs.continuousAt.preimage_mem_nhds (V.isOpen.mem_nhds hz.2)
        have hSnear := hfs.continuousAt.preimage_mem_nhds (c'.open_source.mem_nhds hfz)
        filter_upwards [c.open_target.mem_nhds hz.1, hVnear, hSnear] with y hyT hyV hyS
        exact hcoordinate_pullback V W e e' hV c c' hc hc' y ⟨hyT, hyV⟩ hyS
      change fderiv ℝ (QuotientLineConnection.coordinateForm Dp e c) z v w -
          fderiv ℝ (QuotientLineConnection.coordinateForm Dp e c) z w v = _
      rw [hlocal.fderiv_eq]
      apply hcoordinate_curvature W e' c' hc' F g z _ hF hg hg0 v w
      exact ⟨c'.map_source hfz, by simpa [F, Function.comp_def, c'.left_inv hfz] using hV _ hz.2⟩
    intro x v w
    obtain ⟨V₀, hxV₀, ⟨e₀⟩⟩ := hcover x
    obtain ⟨W, hxW, ⟨e'⟩⟩ := hcover (f x)
    let V : Opens X := ⟨(V₀ : Set X) ∩ f ⁻¹' (W : Set X),
      V₀.isOpen.inter (W.isOpen.preimage f.continuous)⟩
    let e := holomorphicFrameRestrict e₀ (show V ≤ V₀ from fun _ h ↦ h.1)
    have hxV : x ∈ V := ⟨hxV₀, hxW⟩
    have hVW : ∀ y, y ∈ V → f y ∈ W := fun _ h ↦ h.2
    let c := chartAt (ComplexModel d) x
    let c' := chartAt (ComplexModel d) (f x)
    let z := c x
    let F := c' ∘ f ∘ c.symm
    have hc : c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
      IsManifold.chart_mem_maximalAtlas x
    have hc' : c' ∈ IsManifold.maximalAtlas (complexModel d) ∞ X :=
      IsManifold.chart_mem_maximalAtlas (f x)
    have hz : z ∈ c.target := mem_chart_target _ x
    have hzx : c.symm z = x := c.left_inv (mem_chart_source _ x)
    have hfz : f (c.symm z) ∈ c'.source := by
      rw [hzx]; exact mem_chart_source _ (f x)
    have hzV : z ∈ c.target ∩ c.symm ⁻¹' (V : Set X) :=
      ⟨hz, by change c.symm z ∈ V; rw [hzx]; exact hxV⟩
    have hFz : c'.symm (F z) = f x := by
      change c'.symm (c' (f (c.symm z))) = f x
      rw [hzx, c'.left_inv (mem_chart_source _ (f x))]
    have hFzW : F z ∈ c'.target ∩ c'.symm ⁻¹' (W : Set X) :=
      ⟨c'.map_source hfz, by change c'.symm (F z) ∈ W; rw [hFz]; exact hxW⟩
    have hsurj : Function.Surjective
        (mfderiv (realModel d) (realModel d) c.symm z) :=
      (mdifferentiable_chart (I := realModel d) x).symm.mfderiv_surjective hz
    obtain ⟨v₀, hv₀⟩ := hsurj v
    obtain ⟨w₀, hw₀⟩ := hsurj w
    have htransport (a : ComplexModel d) :
        mfderiv (realModel d) (realModel d) c'.symm (F z) (fderiv ℝ F z a) =
          mfderiv (realModel d) (realModel d) f x
            (mfderiv (realModel d) (realModel d) c.symm z a) := by
      have hfd := local_chart_conjugacy_mfderiv f c c' F z hc hc' hz hfz
        Filter.EventuallyEq.rfl
      rw [mfderiv_eq_fderiv] at hfd
      rw [hfd]
      have hi := congrArg (fun L ↦ L
          (mfderiv (realModel d) (realModel d) f (c.symm z)
            (mfderiv (realModel d) (realModel d) c.symm z a)))
        ((mdifferentiable_chart (I := realModel d) (f x)).symm_comp_deriv hfz)
      change mfderiv (realModel d) (realModel d) c'.symm (F z)
          (mfderiv (realModel d) (realModel d) c' (f (c.symm z))
            (mfderiv (realModel d) (realModel d) f (c.symm z)
              (mfderiv (realModel d) (realModel d) c.symm z a))) =
          mfderiv (realModel d) (realModel d) f (c.symm z)
            (mfderiv (realModel d) (realModel d) c.symm z a) at hi
      change _ = _ at hi
      exact hi.trans (by congr 2)
    have hp := hRp V e c hc z hzV v₀ w₀
    have ht := hR W e' c' hc' (F z) hFzW (fderiv ℝ F z v₀) (fderiv ℝ F z w₀)
    have heq := hcurvature_coordinates V W e e' hVW c c' hc hc' z hzV hfz v₀ w₀
    change Rp (c.symm z)
      (mfderiv (realModel d) (realModel d) c.symm z v₀)
      (mfderiv (realModel d) (realModel d) c.symm z w₀) = _ at hp
    change R (c'.symm (F z))
      (mfderiv (realModel d) (realModel d) c'.symm (F z) (fderiv ℝ F z v₀))
      (mfderiv (realModel d) (realModel d) c'.symm (F z) (fderiv ℝ F z w₀)) = _ at ht
    erw [hv₀, hw₀] at hp
    rw [hzx] at hp
    erw [htransport, htransport, hv₀, hw₀] at ht
    rw [hFz] at ht
    exact hp.trans (heq.trans ht.symm)


end ConnectionCalculus
end HolomorphicAnosov

