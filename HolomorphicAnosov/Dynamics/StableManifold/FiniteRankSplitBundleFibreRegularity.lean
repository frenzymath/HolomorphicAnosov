import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Locally finite-rank normed bundle atlases, split bundles, and fibrewise parameter regularity
(Hirsch–Pugh–Shub, pp. 8 and 62). -/

noncomputable section

open Set Topology _root_.Topology

namespace HolomorphicAnosov

/-- The finite-dimensional real Euclidean fibre model of dimension `d`. -/
abbrev FiniteFiberModel (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A bundle trivialization with a finite-dimensional Euclidean fibre model. -/
abbrev FiniteRankBundleChart {A X : Type*} [TopologicalSpace A] [TopologicalSpace X]
    (d : ℕ) (projection : X → A) :=
  Bundle.Trivialization (EuclideanSpace ℝ (Fin d)) projection

/-- The condition that a map induces the topology on its domain. -/
abbrev OriginalTopologyInducing {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop := Topology.IsInducing f

/-- Continuous fibre differentiability of order `r` over the real numbers. -/
abbrev FibreCr {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (r : ℕ) (g : V → W) : Prop :=
  ContDiff ℝ r g

/-- The iterated fibre derivative of order `m` at `x`. -/
def FibreJet {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (m : ℕ) (g : V → W) (x : V) :=
  iteratedFDeriv ℝ m g x

variable {A : Type*} [TopologicalSpace A] {E : A → Type*}
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
  [TopologicalSpace (Sigma E)]

/-- A continuous locally finite-rank real normed bundle atlas, with continuous fibre norm and
operator-norm continuous transitions (Hirsch–Pugh–Shub, p. 8). -/
structure FiniteRankNormedAtlas where
  rank : A → ℕ
  chart : ∀ i, FiniteRankBundleChart (rank i)
    (fun z : Sigma E ↦ z.1)
  mem_baseSet : ∀ i, i ∈ (chart i).baseSet
  rank_eq : ∀ i p, p ∈ (chart i).baseSet → rank p = rank i
  coordinates : ∀ i p, p ∈ (chart i).baseSet → E p ≃L[ℝ] FiniteFiberModel (rank i)
  chart_apply : ∀ i p (hp : p ∈ (chart i).baseSet) (v : E p),
    chart i ⟨p, v⟩ = (p, coordinates i p hp v)
  fibre_inducing : ∀ p, OriginalTopologyInducing (fun v : E p ↦ (⟨p, v⟩ : Sigma E))
  continuous_norm : Continuous (fun z : Sigma E ↦ ‖z.2‖)
  continuous_transition : ∀ i j,
    Continuous (fun p : {p // p ∈ (chart i).baseSet ∩ (chart j).baseSet} ↦
      (coordinates j p.1 p.2.2).toContinuousLinearMap.comp
        (coordinates i p.1 p.2.1).symm.toContinuousLinearMap)

variable {B : Type*} [TopologicalSpace B] {F : B → Type*}
  [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
  [TopologicalSpace (Sigma F)]

/-- The expression of a fibre map in source and target bundle charts on their valid overlap
(Hirsch–Pugh–Shub, pp. 61–62). -/
def fibreChartExpression (e : FiniteRankNormedAtlas (E := E))
    (f : FiniteRankNormedAtlas (E := F)) (b : A → B) (g : ∀ p, E p → F (b p))
    (i : A) (j : B) (p : A) (x : FiniteFiberModel (e.rank i)) :
    FiniteFiberModel (f.rank j) :=
  let z := (e.chart i).toOpenPartialHomeomorph.symm (p, x)
  (f.chart j ⟨b z.1, g z.1 z.2⟩).2

/-- Fibrewise `C^r` regularity with jointly continuous iterated derivatives in local frames over a
topological base (Hirsch–Pugh–Shub, p. 62). -/
def JointFiberContDiff (e : FiniteRankNormedAtlas (E := E))
    (f : FiniteRankNormedAtlas (E := F)) (b : A → B) (r : ℕ)
    (g : ∀ p, E p → F (b p)) : Prop :=
  (∀ p, FibreCr r (g p)) ∧
  ∀ i j m, m ≤ r → ContinuousOn
    (fun z : A × FiniteFiberModel (e.rank i) ↦
      FibreJet m (fibreChartExpression e f b g i j z.1) z.2)
    (((e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet) ×ˢ univ)

/-- Continuity of a fibre-map family in the finite `C^r` supremum topology on each fixed local
closed model disc (Hirsch–Pugh–Shub, pp. 61–62). -/
def FixedDiscCrContinuous (e : FiniteRankNormedAtlas (E := E))
    (f : FiniteRankNormedAtlas (E := F)) (b : A → B) (r : ℕ)
    (g : ∀ p, E p → F (b p)) : Prop :=
  ∀ i j p, p ∈ (e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet →
    ∀ R : ℝ, 0 < R → ∀ m, m ≤ r → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ q in 𝓝 p, q ∈ (e.chart i).baseSet ∩ b ⁻¹' (f.chart j).baseSet ∧
        ∀ x ∈ Metric.closedBall (0 : FiniteFiberModel (e.rank i)) R,
          ‖FibreJet m (fibreChartExpression e f b g i j q) x -
            FibreJet m (fibreChartExpression e f b g i j p) x‖ < ε


variable {E₁ E₂ : A → Type*}
  [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
  [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
  [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
  [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]

/-- A locally finite-rank split normed bundle atlas whose total topology is induced by the fibre
product of its component bundles, with the maximum fibre norm (Hirsch–Pugh–Shub, pp. 8, 53 and
62). -/
structure SplitFiniteRankNormedAtlas where
  first : FiniteRankNormedAtlas (E := E₁)
  second : FiniteRankNormedAtlas (E := E₂)
  total : FiniteRankNormedAtlas (E := fun p ↦ E₁ p × E₂ p)
  split_inducing : OriginalTopologyInducing
    (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      ((⟨z.1, z.2.1⟩ : Sigma E₁), (⟨z.1, z.2.2⟩ : Sigma E₂)))

end HolomorphicAnosov
