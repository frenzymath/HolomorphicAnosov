import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Geometry.HermitianTangentMetric
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! This file defines intrinsic Hermitian lengths and distances on immersed leaves. -/



open Set MeasureTheory
open scoped ContDiff Manifold ENNReal

noncomputable section

namespace HolomorphicAnosov

universe u v

variable {r d : ℕ} {L : Type u} {M : Type v}
  [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
  [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]

/-- The original real tangent pairing pulled back from the given ambient Hermitian metric. (Demailly, VI §4; Ghys, §4; Lee, §11.) -/
def leafPullbackHermitianPairing (inclusion : L → M) (h : HermitianTangentMetricCore d M)
    (z : L) (v w : TangentSpace (modelWithCornersSelf ℝ (Fin r → ℝ)) z) : ℝ :=
  hermitianTangentRealPairing h (inclusion z)
    (mfderiv (modelWithCornersSelf ℝ (Fin r → ℝ)) (realModel d) inclusion z v)
    (mfderiv (modelWithCornersSelf ℝ (Fin r → ℝ)) (realModel d) inclusion z w)

/-- The pullback norm is the square root of the actual real diagonal pairing. (Demailly, VI §4; Ghys, §4; Lee, §11.) -/
def leafPullbackHermitianNorm (inclusion : L → M) (h : HermitianTangentMetricCore d M)
    (z : L) (v : TangentSpace (modelWithCornersSelf ℝ (Fin r → ℝ)) z) : ℝ :=
  Real.sqrt (leafPullbackHermitianPairing inclusion h z v v)

/-- A finite piecewise C¹ path in the same intrinsic leaf, with its literal endpoints. (Demailly, VI §4; Ghys, §4; Lee, §11.) -/
structure IntrinsicPiecewiseC1Path (x y : L) where
  n : ℕ
  time : Fin (n + 2) → ℝ
  time_strictMono : StrictMono time
  time_zero : time 0 = 0
  time_one : time (Fin.last (n + 1)) = 1
  piece : Fin (n + 1) → ℝ → L
  piece_c1 : ∀ i, ContMDiffOn (modelWithCornersSelf ℝ ℝ)
    (modelWithCornersSelf ℝ (Fin r → ℝ)) 1 (piece i)
    (Icc (time i.castSucc) (time i.succ))
  source : piece 0 0 = x
  target : piece (Fin.last n) 1 = y
  junction : ∀ i : Fin n,
    piece i.castSucc (time i.succ.castSucc) = piece i.succ (time i.succ.castSucc)

namespace IntrinsicPiecewiseC1Path

variable {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y)

/-- Actual closed parameter interval of a C¹ piece. (Demailly, VI §4; Ghys, §4; Lee, §11.) -/
def pieceInterval (i : Fin (p.n + 1)) : Set ℝ :=
  Icc (p.time i.castSucc) (p.time i.succ)

/-- The actual derivative within a piece, valued in its receiving ORIGINAL real tangent fibre. (Demailly, VI §4; Ghys, §4; Lee, §11.) -/
def velocity (i : Fin (p.n + 1)) (t : ℝ) :
    TangentSpace (modelWithCornersSelf ℝ (Fin r → ℝ)) (p.piece i t) :=
  mfderivWithin (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ (Fin r → ℝ))
    (p.piece i) (p.pieceInterval i) t (1 : ℝ)

/-- Pullback Hermitian speed on the same leaf, not ambient point distance. (Demailly, VI §4; Ghys, §4; Lee, §11.) -/
def speed (inclusion : L → M) (h : HermitianTangentMetricCore d M)
    (i : Fin (p.n + 1)) (t : ℝ) : ℝ :=
  leafPullbackHermitianNorm inclusion h (p.piece i t) (p.velocity i t)

/-- Sum of the nonnegative speed integrals of the actual finite C¹ pieces. (Demailly, VI §4; Ghys, §4; Lee, §11.) -/
def length (inclusion : L → M) (h : HermitianTangentMetricCore d M) : ℝ≥0∞ :=
  ∑ i : Fin (p.n + 1),
    ∫⁻ t in p.pieceInterval i, ENNReal.ofReal (p.speed inclusion h i t)

end IntrinsicPiecewiseC1Path

/-- The intrinsic distance candidate is exactly the infimum of piecewise C¹ pullback lengths. (Demailly, VI §4; Ghys, §4; Lee, §11.) -/
def intrinsicHermitianLeafEDist (inclusion : L → M) (h : HermitianTangentMetricCore d M)
    (x y : L) : ℝ≥0∞ :=
  ⨅ p : IntrinsicPiecewiseC1Path (r := r) x y, p.length inclusion h

end HolomorphicAnosov
