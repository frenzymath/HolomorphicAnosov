import HolomorphicAnosov.Topology.Franks.LeafFoliation
import HolomorphicAnosov.Topology.FranksPiecewiseC1PathG8
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Analysis.Real.Sqrt

/-!
# Lengths of finite-piece intrinsic leaf paths in the supplied ambient metric

Source: John Franks, *Anosov Diffeomorphisms*, Global Analysis Part I (1970),
Proposition 1.1 and the intrinsic metric definition, p.65; Lemma 1.2, pp.65–66.
Native intrinsic leaf charts are as in HPS (1977), §7, pp.115–116.
DAG node: `topo.franks_leaf_path_length_g8`.

The actual Mathlib singular-parameter manifold path-length integral is applied to the
inclusion composed with the given intrinsic path. Its tangent ENorm is explicitly the
square root of the given metric tensor, not the native coordinate Euclidean norm.
The real length is its `toReal`. Finiteness for this admissible finite-piece C¹
path class is a separate statement obligation, not proof data in this definition.
Franks writes piecewise smooth paths; no equality of the piecewise smooth and C¹
path-distance infima is asserted by this definition.
-/

noncomputable section

open Set MeasureTheory Bundle
open scoped Manifold ContDiff ENNReal

universe u

namespace HolomorphicAnosov.Franks

variable {n r : ℕ} {P : Type u} [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) P] [IsManifold (𝓡 n) ∞ P]
  {ι : Type u} {L : ι → Type u}
  [∀ i, TopologicalSpace (L i)]
  [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin r)) (L i)]
  [∀ i, IsManifold (𝓡 r) 1 (L i)]
  {D : RealTangentDistribution (𝓡 n) P}

/-- The supplied ambient metric's extended tangent norm, only as a local interface
for native `Manifold.pathELength`. Source: Franks, p.65, pullback of the actual
Riemannian metric. This does not create a global instance or change any fibre topology. -/
abbrev ambientMetricENorm
    (g : ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _)) (p : P) : ENorm (TangentSpace (𝓡 n) p) :=
  ⟨fun v ↦ ENNReal.ofReal (Real.sqrt (g.inner p v v))⟩

/-- The real tangent pairing obtained by pulling back the supplied ambient tensor
along the actual leaf inclusion. Source: Franks, p.65. Both derivative vectors
lie in the SAME receiving tangent fibre at the actual image of the leaf point. -/
def leafPullbackPairing
    (g : ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (F : LeafFoliation (r := r) (L := L) D) (i : ι) (p : L i)
    (v w : TangentSpace (𝓡 r) p) : ℝ :=
  g.inner (F.inclusion i p)
    (mfderiv (𝓡 r) (𝓡 n) (F.inclusion i) p v)
    (mfderiv (𝓡 r) (𝓡 n) (F.inclusion i) p w)

/-- The actual finite-piece interval of an existing intrinsic path.
Source: Franks, pp.65–66, with the stipulated closed-piece C¹ convention.
No path is replaced and no velocity agreement at its division times is required. -/
def PiecewiseC1Path.pieceInterval {i : ι} {x y : L i}
    (γ : PiecewiseC1Path (r := r) x y) (j : Fin γ.pieces) : Set ℝ :=
  Icc (γ.division j.castSucc) (γ.division j.succ)

/-- The within-piece intrinsic velocity in the original leaf tangent fibre.
Source: Franks's path speed integral, p.66, and Mathlib's manifold derivative.
It is used only on the displayed closed piece, never as a globally C¹ certificate. -/
def PiecewiseC1Path.pieceVelocity {i : ι} {x y : L i}
    (γ : PiecewiseC1Path (r := r) x y) (j : Fin γ.pieces) (t : ℝ) :
    TangentSpace (𝓡 r) (γ.toFun t) :=
  mfderivWithin 𝓘(ℝ, ℝ) (𝓡 r) γ.toFun (γ.pieceInterval j) t (1 : ℝ)

/-- The given metric's nonnegative pulled-back speed on one genuine path piece.
Source: Franks, pp.65–66. Endpoints are finite values of the total manifold
within derivative, and have zero real Lebesgue measure. -/
def leafPathPieceSpeed
    (g : ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (F : LeafFoliation (r := r) (L := L) D) {i : ι} {x y : L i}
    (γ : PiecewiseC1Path (r := r) x y) (j : Fin γ.pieces) (t : ℝ) : ℝ :=
  Real.sqrt (leafPullbackPairing g F i (γ.toFun t)
    (γ.pieceVelocity j t) (γ.pieceVelocity j t))

/-- The actual extended length of inclusion composed with the intrinsic path.
Source: Franks, pp.65–66; `Manifold.pathELength_eq_lintegral_mfderiv_Ioo`.
The only tangent norm used is the one explicitly supplied by `g`. Breakpoint
velocities of the total path may be undefined; their finite totalized values
at finitely many times do not affect this real-volume integral on [0,1]. -/
def leafPathELength
    (g : ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (F : LeafFoliation (r := r) (L := L) D) {i : ι} {x y : L i}
    (γ : PiecewiseC1Path (r := r) x y) : ℝ≥0∞ :=
  letI : ∀ p : P, ENorm (TangentSpace (𝓡 n) p) := ambientMetricENorm g
  Manifold.pathELength (𝓡 n) (F.inclusion i ∘ γ.toFun) 0 1

/-- The real value of the same nonnegative extended speed integral.
Source: Franks, p.66, literal path length, with the node's finite-piece C¹ convention.
Finiteness is a separate statement obligation; no default Euclidean distance,
ambient endpoint distance, or global-C¹ path length is substituted. -/
def leafPathLength
    (g : ContMDiffRiemannianMetric (𝓡 n) ∞ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : P → Type _))
    (F : LeafFoliation (r := r) (L := L) D) {i : ι} {x y : L i}
    (γ : PiecewiseC1Path (r := r) x y) : ℝ :=
  (leafPathELength g F γ).toReal

end HolomorphicAnosov.Franks
