import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexToRealManifold
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.LinearAlgebra.Quotient.Defs

/-! Connections on the holomorphic tangent quotient line are described by local real one-forms and
their gauge transformations. The file defines covariant derivatives, regularity, flatness, Bott
and Dolbeault compatibility, parallel sections, and invariance (Zhang, Def. 2.1, Eqs. (2)–(5),
pp.4–5, Eqs. (12)–(13), p.7; Demailly, V (11.1)–(11.3), p.267, (14.1), p.273). -/

open Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff Classical

attribute [local instance] HolomorphicAnosov.complex_isManifold_real

noncomputable section
universe u

namespace HolomorphicAnosov.QuotientLineConnection

variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-- The quotient fibre `TangentSpace (complexModel d) x ⧸ U x` (Zhang, p.4). -/
abbrev Fibre (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) (x : X) :=
  HolomorphicQuotientTangentLine U x

/-- The complex-linear projection from the tangent fibre to its quotient by `U x` (Zhang, p.4). -/
abbrev projection (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))
    (x : X) : TangentSpace (complexModel d) x →ₗ[ℂ] Fibre U x := (U x).mkQ

variable (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x))

/-- A quotient section is holomorphic on `V` if it admits local holomorphic tangent lifts near every
point of `V` (Demailly, V (11.1)–(11.3), p.267, (14.1), p.273). -/
def IsHolomorphicSection (V : Set X) (s : (x : X) → Fibre U x) : Prop :=
  ∀ x ∈ V, ∃ (W : Set X) (v : (y : X) → TangentSpace (complexModel d) y),
    IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ContMDiffOn (complexModel d) (complexModel d).tangent ∞
        (fun y ↦ (⟨y, v y⟩ : TangentBundle (complexModel d) X)) W ∧
      ∀ y ∈ W, projection U y (v y) = s y

/-- A holomorphic frame on `V`, consisting of a holomorphic quotient section and fibrewise complex-
linear coordinates sending that section to `1` (Zhang, Eq. (3), p.4). -/
structure HolomorphicFrame (V : Opens X) where
  sectionValue : (x : X) → Fibre U x
  holomorphic : IsHolomorphicSection U V sectionValue
  coordinate : ∀ x : X, x ∈ V → Fibre U x ≃ₗ[ℂ] ℂ
  normalized : ∀ x (hx : x ∈ V), coordinate x hx (sectionValue x) = 1

variable {U}

/-- The scalar coefficient of a quotient section in a local holomorphic frame, extended by zero
outside the frame domain (Zhang, Eq. (3)). -/
def HolomorphicFrame.coefficient {V : Opens X} (e : HolomorphicFrame U V)
    (s : (x : X) → Fibre U x) (x : X) : ℂ :=
  if hx : x ∈ V then e.coordinate x hx (s x) else 0

/-- The real differential of a complex-valued function, with its target tangent space identified
with `ℂ`. -/
def realDifferential (g : X → ℂ) (x : X) : TangentSpace (realModel d) x →L[ℝ] ℂ :=
  (tangentSpaceCastModel 𝓘(ℝ, ℂ) (g x)).toContinuousLinearMap.comp
    (mfderiv (realModel d) 𝓘(ℝ, ℂ) g x)

/-- A connection given by complex-valued real one-forms in every holomorphic quotient frame,
satisfying `A_e′ = A_e + g⁻¹ d_R g` for `e′ = g e` on overlaps (Zhang, Eqs. (3), (5)). -/
structure Connection (U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)) where
  form : ∀ (V : Opens X), HolomorphicFrame U V →
    (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ
  gauge : ∀ (V W : Opens X) (e : HolomorphicFrame U V) (e' : HolomorphicFrame U W)
    (x : X), x ∈ V → x ∈ W →
      form W e' x = form V e x +
        (e.coefficient e'.sectionValue x)⁻¹ • realDifferential (e.coefficient e'.sectionValue) x

variable (nabla : Connection U)

/-- The covariant derivative of a quotient section, whose coefficient in the local frame is `du +
uA` (Zhang, Eq. (3)). -/
def covariantDerivative {V : Opens X} (e : HolomorphicFrame U V)
    (s : (x : X) → Fibre U x) (x : X) (hx : x ∈ V)
    (v : TangentSpace (realModel d) x) : Fibre U x :=
  (e.coordinate x hx).symm
    (realDifferential (e.coefficient s) x v + e.coefficient s x * nabla.form V e x v)

/-- The connection one-form expressed in the tangent coordinates of an inverse chart. -/
def coordinateForm {V : Opens X} (e : HolomorphicFrame U V)
    (c : OpenPartialHomeomorph X (ComplexModel d)) (z : ComplexModel d) :
    ComplexModel d →L[ℝ] ℂ :=
  (nabla.form V e (c.symm z)).comp
    ((mfderiv (realModel d) (realModel d) c.symm z).comp
      (NormedSpace.fromTangentSpace z).symm.toContinuousLinearMap)

/-- Continuity of the connection one-form coefficients on every overlap of a compatible chart and a
local frame domain (Zhang, Lemma 2.2, p.5). -/
def IsContinuous : Prop :=
  ∀ (V : Opens X) (e : HolomorphicFrame U V)
    (c : OpenPartialHomeomorph X (ComplexModel d)),
    c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      ContinuousOn (coordinateForm nabla e c) (c.target ∩ c.symm ⁻¹' (V : Set X))

/-- The connection forms have type (1,0) and holomorphic scalar coefficients in every compatible
chart (Zhang, Eq. (7)). -/
def IsHolomorphic : Prop :=
  (∀ (V : Opens X) (e : HolomorphicFrame U V) (x : X), x ∈ V →
    ∀ v : TangentSpace (complexModel d) x,
      nabla.form V e x (complexTangentToReal d x (Complex.I • v)) =
        Complex.I * nabla.form V e x (complexTangentToReal d x v)) ∧
  ∀ (V : Opens X) (e : HolomorphicFrame U V)
    (c : OpenPartialHomeomorph X (ComplexModel d)),
    c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X → ∀ j : Fin d,
      DifferentiableOn ℂ
        (fun z ↦ coordinateForm nabla e c z (Pi.single j 1))
        (c.target ∩ c.symm ⁻¹' (V : Set X))

/-- The connection forms have real differentiable coordinate coefficients with vanishing exterior
derivative (Zhang, p.6). -/
def IsFlat : Prop :=
  ∀ (V : Opens X) (e : HolomorphicFrame U V)
    (c : OpenPartialHomeomorph X (ComplexModel d)),
    c ∈ IsManifold.maximalAtlas (complexModel d) ∞ X →
      DifferentiableOn ℝ (coordinateForm nabla e c) (c.target ∩ c.symm ⁻¹' (V : Set X)) ∧
      ∀ z ∈ c.target ∩ c.symm ⁻¹' (V : Set X), ∀ v w : ComplexModel d,
        fderiv ℝ (coordinateForm nabla e c) z v w -
          fderiv ℝ (coordinateForm nabla e c) z w v = 0

/-- A complex tangent field is smooth on `V` when its corresponding real tangent section is smooth
there (Zhang, Eq. (2), p.4). -/
def IsSmoothTangentField (V : Set X) (Y : (x : X) → TangentSpace (complexModel d) x) : Prop :=
  ContMDiffOn (realModel d) (realModel d).tangent ∞
    (fun x ↦ (⟨x, complexTangentToReal d x (Y x)⟩ : TangentBundle (realModel d) X)) V

/-- The (1,0) bracket of smooth complex tangent fields, computed as one half of the difference
between the real brackets of their real representatives and of the representatives multiplied by
`Complex.I`. -/
def bottBracket (Y Z : (x : X) → TangentSpace (complexModel d) x) (x : X) :
    TangentSpace (complexModel d) x :=
  (1 / 2 : ℂ) • ((complexTangentToReal d x).symm
    (VectorField.mlieBracket (realModel d)
      (fun y ↦ complexTangentToReal d y (Y y))
      (fun y ↦ complexTangentToReal d y (Z y)) x -
    VectorField.mlieBracket (realModel d)
      (fun y ↦ complexTangentToReal d y (Complex.I • Y y))
      (fun y ↦ complexTangentToReal d y (Complex.I • Z y)) x))

/-- Compatibility with the Dolbeault operator and with the Bott quotient bracket along smooth fields
valued in `U` (Zhang, Def. 2.1, Eqs. (2)–(4)). -/
def IsCompatible : Prop :=
  (∀ (V : Opens X) (e : HolomorphicFrame U V) (x : X), x ∈ V →
    ∀ v : TangentSpace (complexModel d) x,
      nabla.form V e x (complexTangentToReal d x (Complex.I • v)) =
        Complex.I * nabla.form V e x (complexTangentToReal d x v)) ∧
  ∀ (V : Opens X) (e : HolomorphicFrame U V)
    (Y Z : (x : X) → TangentSpace (complexModel d) x),
    IsSmoothTangentField V Y → IsSmoothTangentField V Z →
    (∀ x ∈ V, Y x ∈ U x) → ∀ x (hx : x ∈ V),
      (1 / 2 : ℂ) •
        (covariantDerivative nabla e (fun y ↦ projection U y (Z y)) x hx
          (complexTangentToReal d x (Y x)) -
        Complex.I • covariantDerivative nabla e (fun y ↦ projection U y (Z y)) x hx
          (complexTangentToReal d x (Complex.I • Y x))) =
        projection U x (bottBracket Y Z x)

/-- A quotient section is parallel on `V` if its covariant derivative vanishes in every local frame
on its overlap with `V` (Zhang, Lemma 2.4, p.7). -/
def IsParallelOn (V : Set X) (s : (x : X) → Fibre U x) : Prop :=
  ∀ (W : Opens X) (e : HolomorphicFrame U W) (x : X) (hx : x ∈ W), x ∈ V →
    ∀ v : TangentSpace (realModel d) x, covariantDerivative nabla e s x hx v = 0

/-- Two connections agree when their one-forms coincide on every local frame domain (Zhang, Lemma
2.2). -/
def Agrees (other : Connection U) : Prop :=
  ∀ (V : Opens X) (e : HolomorphicFrame U V) (x : X), x ∈ V →
    nabla.form V e x = other.form V e x

/-- The complex-linear map on quotient fibres induced by the derivative of a biholomorphism
preserving `U` (Zhang, p.4). -/
def quotientDerivative (f : Biholomorph d d X X)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x)) (x : X) :
    Fibre U x →ₗ[ℂ] Fibre U (f x) :=
  (U x).mapQ (U (f x)) (mfderiv (complexModel d) (complexModel d) f x).toLinearMap
    (fun v hv ↦ hU x v hv)

/-- The target-frame coefficient of the image of a source-frame section under the quotient
derivative, extended by zero outside the preimage of the target frame domain. -/
def imageFrameCoefficient (f : Biholomorph d d X X)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x))
    {V W : Opens X} (e : HolomorphicFrame U V) (e' : HolomorphicFrame U W) (x : X) : ℂ :=
  if hx : f x ∈ W then e'.coordinate (f x) hx (quotientDerivative f hU x (e.sectionValue x))
  else 0

/-- Invariance under `f` means that the frame forms satisfy the connection pullback formula `A_e =
g⁻¹ d_R g + A_e′ ∘ D_R f`, where the quotient derivative sends `e` to `g e′` (Zhang, Eq. (5)). -/
def IsInvariant (f : Biholomorph d d X X)
    (hU : ∀ x (v : TangentSpace (complexModel d) x), v ∈ U x →
      mfderiv (complexModel d) (complexModel d) f x v ∈ U (f x)) : Prop :=
  ∀ (V W : Opens X) (e : HolomorphicFrame U V) (e' : HolomorphicFrame U W)
    (x : X), x ∈ V → f x ∈ W →
      nabla.form V e x =
        (imageFrameCoefficient f hU e e' x)⁻¹ •
          realDifferential (imageFrameCoefficient f hU e e') x +
        (nabla.form W e' (f x)).comp (mfderiv (realModel d) (realModel d) f x)

end HolomorphicAnosov.QuotientLineConnection
