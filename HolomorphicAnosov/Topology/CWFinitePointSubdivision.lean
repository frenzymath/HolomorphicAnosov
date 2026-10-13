import HolomorphicAnosov.Topology.CWDiskBoundaryCollapse
import HolomorphicAnosov.Topology.CWFiniteOpenRefinement
import HolomorphicAnosov.Topology.CWPointVertexBoundarySmallerCell
import HolomorphicAnosov.Topology.CWVertexDiskHomeomorph

/-!
# Finite subdivision at a marked interior point

Source: Fritsch–Piccinini, Cellular Structures in Topology (1990), Lemma 2.3.7,
printed p.67. The proof carries out its dimension induction with three explicit
cone cells, a boundary-fixing disk mover, finite carrier maps, and unchanged
characteristic maps away from the finite change support.
-/

open Set _root_.Topology

namespace HolomorphicAnosov
universe u
noncomputable section

/-- The disk peak mover extends to a global homeomorphism, preserving both the
open and closed unit disks and fixing their boundary pointwise. -/
theorem cw_vertex_ambient_homeomorph {n : ℕ} (a : Fin n → ℝ) (ha : ‖a‖ < 1) :
    ∃ M : (Fin n → ℝ) ≃ₜ (Fin n → ℝ),
      M 0 = a ∧ (∀ v ∈ Metric.sphere 0 1, M v = v) ∧
      (∀ v, M v ∈ Metric.closedBall 0 1 ↔ v ∈ Metric.closedBall 0 1) ∧
      (∀ v, M v ∈ Metric.ball 0 1 ↔ v ∈ Metric.ball 0 1) := by
  let move : (Fin n → ℝ) → (Fin n → ℝ) := fun v ↦ v + (1 - ‖v‖) • a
  have happrox : ApproximatesLinearOn move
      (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)).toContinuousLinearMap
      Set.univ ‖a‖₊ := by
    intro v _ w _
    have hdiff : move v - move w - (v - w) = (‖w‖ - ‖v‖) • a := by
      ext k
      simp only [move, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    change ‖move v - move w - (v - w)‖ ≤ ‖a‖ * ‖v - w‖
    rw [hdiff, norm_smul, Real.norm_eq_abs]
    calc
      |‖w‖ - ‖v‖| * ‖a‖ ≤ ‖w - v‖ * ‖a‖ :=
        mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le w v) (norm_nonneg a)
      _ = ‖a‖ * ‖v - w‖ := by rw [norm_sub_rev, mul_comm]
  have hsmall : Subsingleton (Fin n → ℝ) ∨
      ‖a‖₊ < ‖((ContinuousLinearEquiv.refl ℝ (Fin n → ℝ)).symm :
        (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))‖₊⁻¹ := by
    by_cases hs : Subsingleton (Fin n → ℝ)
    · exact Or.inl hs
    · let : Nontrivial (Fin n → ℝ) := not_subsingleton_iff_nontrivial.mp hs
      right
      have haNN : ‖a‖₊ < 1 := by exact_mod_cast ha
      simpa using haNN
  let moveHomeomorph : (Fin n → ℝ) ≃ₜ (Fin n → ℝ) :=
    happrox.toHomeomorph move hsmall

  obtain ⟨H, hH, h0, hb⟩ := cw_vertex_disk_homeomorph a ha
  have hformula (v) : moveHomeomorph v = move v := rfl
  have hfix (v) (hv : v ∈ Metric.sphere 0 1) : moveHomeomorph v = v := by
    have hn : ‖v‖ = 1 := by simpa using hv
    simp [hformula, move, hn]
  have hc (v) : moveHomeomorph v ∈ Metric.closedBall 0 1 ↔ v ∈ Metric.closedBall 0 1 := by
    constructor
    · intro hv
      let z := H.symm ⟨moveHomeomorph v, hv⟩
      have heq : moveHomeomorph z.val = moveHomeomorph v := by
        change z.val + (1 - ‖z.val‖) • a = moveHomeomorph v
        rw [← hH z]
        exact congrArg Subtype.val (H.apply_symm_apply _)
      exact moveHomeomorph.injective heq ▸ z.property
    · intro hv
      simp [hformula, move, ← hH ⟨v,hv⟩]
  refine ⟨moveHomeomorph, by simp [hformula, move], hfix, hc, ?_⟩
  intro v
  have hn (w : Fin n → ℝ) : w ∈ Metric.ball 0 1 ↔
      w ∈ Metric.closedBall 0 1 ∧ w ∉ Metric.sphere 0 1 := by
    simp only [Metric.mem_ball, Metric.mem_closedBall, Metric.mem_sphere, dist_zero_right]
    exact lt_iff_le_and_ne
  rw [hn, hn, hc]
  apply and_congr_right
  intro _
  constructor
  · intro hv hs
    apply hv
    rw [hfix v hs]
    exact hs
  · intro hv hs
    have heq := hfix (moveHomeomorph v) hs
    have heq' : moveHomeomorph v = v := moveHomeomorph.injective heq
    exact hv (heq' ▸ hs)

/-- Composition with an old characteristic map retains the whole new source
when the new chart lands inside the old open disk. -/
theorem characteristic_trans_source {d n : ℕ} {X : Type*}
    (g : PartialEquiv (Fin d → ℝ) (Fin n → ℝ))
    (f : PartialEquiv (Fin n → ℝ) X)
    (hs : g.source = Metric.ball 0 1) (hf : f.source = Metric.ball 0 1)
    (ht : g.target ⊆ Metric.ball 0 1) :
    (g.trans f).source = Metric.ball 0 1 := by
  rw [g.trans_source, ← hs]
  exact inter_eq_left.mpr (fun _ hx ↦ hf.symm ▸ ht (g.map_source hx))

theorem characteristic_trans_target {d n : ℕ} {X : Type*}
    (g : PartialEquiv (Fin d → ℝ) (Fin n → ℝ))
    (f : PartialEquiv (Fin n → ℝ) X)
    (hf : f.source = Metric.ball 0 1) (ht : g.target ⊆ Metric.ball 0 1) :
    (g.trans f).target = f '' g.target := by
  rw [g.trans_target'', hf, inter_eq_right.mpr ht]

theorem characteristic_trans_continuousOn {d n : ℕ} {X : Type*} [TopologicalSpace X]
    (g : PartialEquiv (Fin d → ℝ) (Fin n → ℝ))
    (f : PartialEquiv (Fin n → ℝ) X)
    (hg : ContinuousOn g (Metric.closedBall 0 1))
    (hf : ContinuousOn f (Metric.closedBall 0 1))
    (ht : MapsTo g (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ContinuousOn (g.trans f) (Metric.closedBall 0 1) := hf.comp hg ht

theorem characteristic_trans_continuousOn_symm {d n : ℕ} {X : Type*} [TopologicalSpace X]
    (g : PartialEquiv (Fin d → ℝ) (Fin n → ℝ))
    (f : PartialEquiv (Fin n → ℝ) X)
    (hg : ContinuousOn g.symm g.target) (hf : ContinuousOn f.symm f.target) :
    ContinuousOn (g.trans f).symm (g.trans f).target := by
  exact hg.comp (hf.mono inter_subset_left) (fun _ hx ↦ hx.2)


inductive ConeDiskCell (n : ℕ) : ℕ → Type
  | peak : ConeDiskCell n 0
  | ray : ConeDiskCell n 1
  | body : ConeDiskCell n (n + 1)

def ConeDiskCell.tag {n d : ℕ} : ConeDiskCell n d → Fin 3
  | .peak => 0
  | .ray => 1
  | .body => 2

instance (n : ℕ) : Finite (Σ d, ConeDiskCell n d) := by
  apply Finite.of_injective (fun p : Σ d, ConeDiskCell n d ↦ p.2.tag)
  rintro ⟨d,p⟩ ⟨e,q⟩ h
  cases p <;> cases q <;> simp_all [ConeDiskCell.tag]

def coneDiskVertex (n : ℕ) : Metric.sphere (0 : Fin (n + 1) → ℝ) 1 :=
  onePointSupSphereHomeomorph n OnePoint.infty

def coneDiskChart (n : ℕ) : (d : ℕ) → ConeDiskCell n d →
    PartialEquiv (Fin d → ℝ) (Fin (n + 1) → ℝ)
  | _, .peak => PartialEquiv.single 0 0
  | _, .ray => coneCharacteristicPartialEquiv 0 (n+1) (coneDiskVertex n)
      (sphereVertexCharacteristic (n+1) (coneDiskVertex n))
      (sphereVertexCharacteristic_source _ _)
  | _, .body => coneCharacteristicPartialEquiv n (n+1) (coneDiskVertex n)
      (sphereDiskCharacteristic n) (sphereDiskCharacteristic_source n)

theorem coneDiskChart_source (n d : ℕ) (p : ConeDiskCell n d) :
    (coneDiskChart n d p).source = Metric.ball 0 1 := by
  cases p with
  | peak =>
    ext v
    have hv : v = 0 := Subsingleton.elim _ _
    simp [coneDiskChart, hv]
  | ray => rfl
  | body => rfl

theorem coneDiskChart_continuous (n d : ℕ) (p : ConeDiskCell n d) :
    Continuous (coneDiskChart n d p) := by
  cases p with
  | peak => exact continuous_const
  | ray =>
    exact coneCharacteristicMap_continuous _ _ _
        (sphereVertexCharacteristic_continuous _ _)
  | body =>
    exact coneCharacteristicMap_continuous _ _ _
        (sphereDiskCharacteristic_continuous _)

theorem coneDiskChart_inverse_continuous (n d : ℕ) (p : ConeDiskCell n d) :
    ContinuousOn (coneDiskChart n d p).symm (coneDiskChart n d p).target := by
  cases p with
  | peak => exact continuous_const.continuousOn
  | ray =>
    exact coneCharacteristicInverse_continuousOn _ _ _ _
        (sphereVertexCharacteristic_continuousOn_symm _ _)
  | body =>
    exact coneCharacteristicInverse_continuousOn _ _ _ _
        (sphereDiskCharacteristic_continuousOn_symm _)

theorem coneDiskChart_closed (n d : ℕ) (p : ConeDiskCell n d) :
    MapsTo (coneDiskChart n d p) (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
  cases p with
  | peak => intro v hv; simp [coneDiskChart]
  | ray => exact coneCharacteristicMap_closedBall _ _ _
  | body => exact coneCharacteristicMap_closedBall _ _ _

theorem coneDiskChart_target_peak (n : ℕ) :
    (coneDiskChart n 0 .peak).target = {0} := rfl

theorem coneDiskChart_target_ray (n : ℕ) :
    (coneDiskChart n 1 .ray).target =
      {y | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ sphereDirection (n+1) (coneDiskVertex n) y = coneDiskVertex n} := by
  rfl

theorem coneDiskChart_target_body (n : ℕ) :
    (coneDiskChart n (n+1) .body).target =
      {y | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ sphereDirection (n+1) (coneDiskVertex n) y ≠ coneDiskVertex n} := by
  change {y | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ sphereDirection (n+1) (coneDiskVertex n) y ∈
      (sphereDiskCharacteristic n).target} = _
  rw [sphereDiskCharacteristic_target]
  rfl

theorem coneDiskChart_target_subset (n d : ℕ) (p : ConeDiskCell n d) :
    (coneDiskChart n d p).target ⊆ Metric.ball 0 1 := by
  cases p with
  | peak => simp [coneDiskChart_target_peak]
  | ray => intro y hy; exact mem_ball_zero_iff.mpr hy.2.1
  | body => intro y hy; exact mem_ball_zero_iff.mpr hy.2.1

theorem coneDiskChart_cover (n : ℕ) :
    Metric.ball (0 : Fin (n+1) → ℝ) 1 = ⋃ d, ⋃ p : ConeDiskCell n d,
      (coneDiskChart n d p).target := by
  ext y
  constructor
  · intro hy
    by_cases h0 : y = 0
    · exact mem_iUnion.mpr ⟨0, mem_iUnion.mpr ⟨.peak, h0⟩⟩
    · have hp : 0 < ‖y‖ := norm_pos_iff.mpr h0
      have hlt : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
      by_cases hdir : sphereDirection (n+1) (coneDiskVertex n) y = coneDiskVertex n
      · exact mem_iUnion.mpr ⟨1, mem_iUnion.mpr ⟨.ray, ⟨hp,hlt,hdir⟩⟩⟩
      · refine mem_iUnion.mpr ⟨n+1, mem_iUnion.mpr ⟨.body, ?_⟩⟩
        rw [coneDiskChart_target_body]
        exact ⟨hp,hlt,hdir⟩
  · intro hy
    obtain ⟨d, p, hp⟩ := mem_iUnion₂.mp hy
    exact coneDiskChart_target_subset n d p hp

theorem coneDiskChart_disjoint (n : ℕ) :
    (univ : Set (Σ d, ConeDiskCell n d)).PairwiseDisjoint
      (fun p ↦ (coneDiskChart n p.1 p.2).target) := by
  rintro ⟨d,p⟩ _ ⟨e,q⟩ _ hne
  cases p <;> cases q
  all_goals try exact (hne rfl).elim
  all_goals apply disjoint_left.mpr
  all_goals intro y hy hz
  all_goals try { rcases hy with rfl; simpa using hz.1 }
  all_goals try { rcases hz with rfl; simpa using hy.1 }
  · have hb := hz.2.2
    change sphereDirection (n+1) (coneDiskVertex n) y ∈ (sphereDiskCharacteristic n).target at hb
    rw [sphereDiskCharacteristic_target] at hb
    exact hb hy.2.2
  · have hb := hy.2.2
    change sphereDirection (n+1) (coneDiskVertex n) y ∈ (sphereDiskCharacteristic n).target at hb
    rw [sphereDiskCharacteristic_target] at hb
    exact hb hz.2.2


theorem coneDiskChart_ray_closed (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • (coneDiskVertex n).val ∈ coneDiskChart n 1 .ray '' Metric.closedBall 0 1 := by
  refine ⟨Fin.cons (2*t-1) (0 : Fin 0 → ℝ), ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
    intro j
    refine Fin.cases ?_ (fun k ↦ Fin.elim0 k) j
    change ‖2*t-1‖ ≤ 1
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · change ((2*t-1+1)/2) • (coneDiskVertex n).val = _
    congr 1
    ring

theorem coneDiskChart_boundary (n d : ℕ) (p : ConeDiskCell n d)
    {v : Fin d → ℝ} (hv : v ∈ Metric.sphere 0 1) :
    coneDiskChart n d p v ∈ Metric.sphere 0 1 ∨
      ∃ k, ∃ q : ConeDiskCell n k, k < d ∧
        coneDiskChart n d p v ∈ coneDiskChart n k q '' Metric.closedBall 0 1 := by
  have hpeak : (0 : Fin (n+1) → ℝ) ∈
      coneDiskChart n 0 .peak '' Metric.closedBall 0 1 := ⟨0, by simp, rfl⟩
  cases p with
  | peak =>
    have h0 : v = 0 := Subsingleton.elim _ _
    rw [h0] at hv
    norm_num only [Metric.mem_sphere, dist_zero_right, norm_zero] at hv
  | ray =>
    let w : CubicalCharacteristicParameterG8.ClosedDisk 1 := ⟨v, Metric.sphere_subset_closedBall hv⟩
    rcases (CubicalCharacteristicParameterG8.diskPrismHomeomorph_boundary_iff 0 w).mp hv with h | h | h
    · right
      refine ⟨0, .peak, by omega, ?_⟩
      change (v 0 + 1)/2 = 0 at h
      change ((v 0+1)/2) • (coneDiskVertex n).val ∈ _
      simpa [h] using hpeak
    · left
      change (v 0 + 1)/2 = 1 at h
      change ((v 0+1)/2) • (coneDiskVertex n).val ∈ _
      simp [h]
    · change Fin.tail v ∈ Metric.sphere 0 1 at h
      have heq : Fin.tail v = 0 := Subsingleton.elim _ _
      rw [heq] at h
      norm_num only [Metric.mem_sphere, dist_zero_right, norm_zero] at h
  | body =>
    let w : CubicalCharacteristicParameterG8.ClosedDisk (n+1) := ⟨v, Metric.sphere_subset_closedBall hv⟩
    rcases (CubicalCharacteristicParameterG8.diskPrismHomeomorph_boundary_iff n w).mp hv with h | h | h
    · right
      refine ⟨0, .peak, by omega, ?_⟩
      change (v 0+1)/2 = 0 at h
      change ((v 0+1)/2) • (sphereDiskCharacteristic n (Fin.tail v)).val ∈ _
      simpa [h] using hpeak
    · left
      change (v 0+1)/2 = 1 at h
      change ((v 0+1)/2) • (sphereDiskCharacteristic n (Fin.tail v)).val ∈ _
      simp [h]
    · right
      change Fin.tail v ∈ Metric.sphere 0 1 at h
      have hn : 0 < n := by
        by_contra hz
        have hz' : n = 0 := by omega
        subst n
        have heq : Fin.tail v = 0 := Subsingleton.elim _ _
        rw [heq] at h
        norm_num only [Metric.mem_sphere, dist_zero_right, norm_zero] at h
      refine ⟨1, .ray, by omega, ?_⟩
      change ((v 0+1)/2) • (sphereDiskCharacteristic n (Fin.tail v)).val ∈ _
      rw [sphereDiskCharacteristic_boundary n h]
      exact coneDiskChart_ray_closed n
        (CubicalCharacteristicParameterG8.diskPrismHomeomorph n w).2.property


def reparamCharacteristic {n : ℕ} {X : Type*}
    (f : PartialEquiv (Fin n → ℝ) X) (M : (Fin n → ℝ) ≃ₜ (Fin n → ℝ)) :=
  M.toEquiv.toPartialEquiv.trans f

theorem reparamCharacteristic_source {n : ℕ} {X : Type*}
    (f : PartialEquiv (Fin n → ℝ) X) (M : (Fin n → ℝ) ≃ₜ (Fin n → ℝ))
    (hs : f.source = Metric.ball 0 1)
    (hM : ∀ v, M v ∈ Metric.ball 0 1 ↔ v ∈ Metric.ball 0 1) :
    (reparamCharacteristic f M).source = Metric.ball 0 1 := by
  ext v
  change (v ∈ univ ∧ M v ∈ f.source) ↔ _
  simp only [mem_univ, true_and, hs, hM]

theorem reparamCharacteristic_target {n : ℕ} {X : Type*}
    (f : PartialEquiv (Fin n → ℝ) X) (M : (Fin n → ℝ) ≃ₜ (Fin n → ℝ)) :
    (reparamCharacteristic f M).target = f.target := by
  ext y
  exact and_iff_left (mem_univ _)

theorem reparamCharacteristic_continuousOn {n : ℕ} {X : Type*} [TopologicalSpace X]
    (f : PartialEquiv (Fin n → ℝ) X) (M : (Fin n → ℝ) ≃ₜ (Fin n → ℝ))
    (hf : ContinuousOn f (Metric.closedBall 0 1))
    (hM : MapsTo M (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ContinuousOn (reparamCharacteristic f M) (Metric.closedBall 0 1) :=
  hf.comp M.continuous.continuousOn hM

theorem reparamCharacteristic_continuousOn_symm {n : ℕ} {X : Type*} [TopologicalSpace X]
    (f : PartialEquiv (Fin n → ℝ) X) (M : (Fin n → ℝ) ≃ₜ (Fin n → ℝ))
    (hf : ContinuousOn f.symm f.target) :
    ContinuousOn (reparamCharacteristic f M).symm (reparamCharacteristic f M).target := by
  exact M.symm.continuous.comp_continuousOn (hf.mono inter_subset_left)

/-- A finite collection of lower-dimensional closed characteristic images is
exactly the finite-frontier certificate used by the native CW structure. -/
theorem finite_frontier_of_finite_set {X : Type*} {J : ℕ → Type*}
    (f : (d : ℕ) → J d → (Fin d → ℝ) → X) {d : ℕ}
    (g : (Fin d → ℝ) → X) (S : Set (Σ k, J k)) (hS : S.Finite)
    (hcover : ∀ v ∈ Metric.sphere 0 1, ∃ p ∈ S, p.1 < d ∧
      g v ∈ f p.1 p.2 '' Metric.closedBall 0 1) :
    ∃ I : (k : ℕ) → Finset (J k), MapsTo g (Metric.sphere 0 1)
      (⋃ (k < d) (p ∈ I k), f k p '' Metric.closedBall 0 1) := by
  classical
  have hf (k : ℕ) : (Sigma.mk k ⁻¹' S).Finite :=
    hS.preimage (fun _ _ _ _ h ↦ by simpa using h)
  refine ⟨fun k ↦ (hf k).toFinset, ?_⟩
  intro v hv
  obtain ⟨⟨k,p⟩, hp, hk, hvp⟩ := hcover v hv
  exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, mem_iUnion.mpr
    ⟨p, mem_iUnion.mpr ⟨(hf k).mem_toFinset.mpr hp, hvp⟩⟩⟩⟩


abbrev ConeReplacementCell (n d : ℕ) := ULift.{u} (ConeDiskCell n d)

instance (n : ℕ) : Finite (Σ d, ConeReplacementCell.{u} n d) := by
  apply Finite.of_injective (fun p : Σ d, ConeReplacementCell.{u} n d ↦
    (⟨p.1,p.2.down⟩ : Σ d, ConeDiskCell n d))
  rintro ⟨d,⟨p⟩⟩ ⟨e,⟨q⟩⟩ h
  cases h
  rfl

def transportedConeChart {X : Type u} (n : ℕ)
    (f : PartialEquiv (Fin (n+1) → ℝ) X) (d : ℕ) (p : ConeReplacementCell.{u} n d) :=
  (coneDiskChart n d p.down).trans f

theorem transportedConeChart_source {X : Type u} (n : ℕ)
    (f : PartialEquiv (Fin (n+1) → ℝ) X) (hf : f.source = Metric.ball 0 1)
    (d : ℕ) (p : ConeReplacementCell.{u} n d) :
    (transportedConeChart n f d p).source = Metric.ball 0 1 :=
  characteristic_trans_source _ _ (coneDiskChart_source n d p.down) hf
    (coneDiskChart_target_subset n d p.down)

theorem transportedConeChart_target {X : Type u} (n : ℕ)
    (f : PartialEquiv (Fin (n+1) → ℝ) X) (hf : f.source = Metric.ball 0 1)
    (d : ℕ) (p : ConeReplacementCell.{u} n d) :
    (transportedConeChart n f d p).target = f '' (coneDiskChart n d p.down).target :=
  characteristic_trans_target _ _ hf (coneDiskChart_target_subset n d p.down)

theorem transportedConeChart_cover {X : Type u} (n : ℕ)
    (f : PartialEquiv (Fin (n+1) → ℝ) X) (hf : f.source = Metric.ball 0 1) :
    f.target = ⋃ d, ⋃ p : ConeReplacementCell.{u} n d, (transportedConeChart n f d p).target := by
  rw [← f.image_source_eq_target, hf, coneDiskChart_cover]
  ext y
  simp only [mem_image, mem_iUnion]
  constructor
  · rintro ⟨z, ⟨d,p,hp⟩, rfl⟩
    refine ⟨d, ⟨p⟩, ?_⟩
    rw [transportedConeChart_target n f hf]
    exact ⟨z,hp,rfl⟩
  · rintro ⟨d,p,hp⟩
    rw [transportedConeChart_target n f hf] at hp
    obtain ⟨z,hz,rfl⟩ := hp
    exact ⟨z,⟨d,p.down,hz⟩,rfl⟩

theorem transportedConeChart_disjoint {X : Type u} (n : ℕ)
    (f : PartialEquiv (Fin (n+1) → ℝ) X) (hf : f.source = Metric.ball 0 1) :
    (univ : Set (Σ d, ConeReplacementCell.{u} n d)).PairwiseDisjoint
      (fun p ↦ (transportedConeChart n f p.1 p.2).target) := by
  rintro ⟨d,⟨p⟩⟩ _ ⟨e,⟨q⟩⟩ _ hne
  change Disjoint (transportedConeChart n f d ⟨p⟩).target
    (transportedConeChart n f e ⟨q⟩).target
  rw [transportedConeChart_target n f hf, transportedConeChart_target n f hf]
  apply disjoint_left.mpr
  rintro y ⟨v,hv,rfl⟩ ⟨w,hw,heq⟩
  have heq' : w = v := f.injOn
    (hf.symm ▸ coneDiskChart_target_subset n e q hw)
    (hf.symm ▸ coneDiskChart_target_subset n d p hv) heq
  subst w
  have hne' : (⟨d,p⟩ : Σ k, ConeDiskCell n k) ≠ ⟨e,q⟩ := by
    intro hh
    apply hne
    cases hh
    rfl
  exact disjoint_left.mp (coneDiskChart_disjoint n (mem_univ _) (mem_univ _) hne') hv hw


theorem coneDiskChart_ray_sphere (n : ℕ) {v : Fin 1 → ℝ}
    (hv : v ∈ Metric.closedBall 0 1)
    (hs : coneDiskChart n 1 .ray v ∈ Metric.sphere 0 1) :
    coneDiskChart n 1 .ray v = (coneDiskVertex n).val := by
  have ht : 0 ≤ (v 0+1)/2 := by
    have hcoord := (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mp
      (mem_closedBall_zero_iff.mp hv) 0
    rw [Real.norm_eq_abs, abs_le] at hcoord
    linarith [hcoord.1]
  change ((v 0+1)/2) • (coneDiskVertex n).val = _
  have hn : (v 0+1)/2 = 1 := by
    rw [Metric.mem_sphere, dist_zero_right] at hs
    change ‖((v 0+1)/2) • (coneDiskVertex n).val‖ = 1 at hs
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
      (show ‖(coneDiskVertex n).val‖ = 1 by simp), mul_one] using hs
  simp [hn]

theorem cone_replacement_frontier
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (old : CWComplex (Set.univ : Set X)) (n : ℕ)
    (i : @CWComplex.cell X _ Set.univ old (n+1))
    (f : PartialEquiv (Fin (n+1) → ℝ) X)
    (hf : f.source = Metric.ball 0 1)
    (ht : f.target = (@CWComplex.map X _ Set.univ old (n+1) i).target)
    (hb : EqOn f (@CWComplex.map X _ Set.univ old (n+1) i) (Metric.sphere 0 1))
    (vtx : @CWComplex.cell X _ Set.univ old 0)
    (hvtx : (@CWComplex.map X _ Set.univ old 0 vtx).target = {f (coneDiskVertex n).val})
    (d : ℕ) (p : ConeReplacementCell.{u} n d) :
    ∃ I : (k : ℕ) → Finset (cellReplacementLabels old ⟨n+1,i⟩ (ConeReplacementCell n) k),
      MapsTo (transportedConeChart n f d p) (Metric.sphere 0 1)
        (⋃ (k < d) (q ∈ I k),
          cellReplacementMap old ⟨n+1,i⟩ (ConeReplacementCell n)
            (transportedConeChart n f) k q '' Metric.closedBall 0 1) := by
  classical
  let P := ConeReplacementCell.{u} n
  let J := cellReplacementLabels old ⟨n+1,i⟩ P
  let g := transportedConeChart n f
  let F := cellReplacementMap old ⟨n+1,i⟩ P g
  have hdim : ∀ k, P k → k ≤ n+1 := by
    rintro k ⟨q⟩
    cases q <;> omega
  obtain ⟨I,hI⟩ := cellReplacementOldFrontier old ⟨n+1,i⟩ P g
    (transportedConeChart_source n f hf)
    (ht ▸ transportedConeChart_cover n f hf) hdim (n+1) i
  have hne : (⟨0,vtx⟩ : Σ k, @CWComplex.cell X _ Set.univ old k) ≠ ⟨n+1,i⟩ := by
    intro h
    have hh := congrArg Sigma.fst h
    change 0 = n+1 at hh
    omega
  let qv : J 0 := Sum.inl ⟨vtx,hne⟩
  let S₁ : Set (Σ k, J k) := ⋃ k ∈ (Finset.range (n+1) : Set ℕ),
    Sigma.mk k '' (I k : Set (J k))
  let S₂ : Set (Σ k, J k) := Set.range (fun q : Σ k, P k ↦ ⟨q.1,Sum.inr q.2⟩)
  have hS₁ : S₁.Finite := (Finset.finite_toSet _).biUnion
    (fun k _ ↦ (Finset.finite_toSet (I k)).image (Sigma.mk k))
  have hS₂ : S₂.Finite := Set.finite_range _
  apply finite_frontier_of_finite_set (fun k q ↦ F k q) (g d p)
    (S₁ ∪ S₂ ∪ {⟨0,qv⟩}) ((hS₁.union hS₂).union (finite_singleton _))
  intro z hz
  rcases coneDiskChart_boundary n d p.down hz with hs | ⟨k,q,hk,w,hw,heq⟩
  · have hcases : d = n+1 ∨ coneDiskChart n d p.down z = (coneDiskVertex n).val := by
      obtain ⟨p⟩ := p
      cases p with
      | peak =>
        have hz0 : z = 0 := Subsingleton.elim _ _
        rw [hz0] at hz
        norm_num only [Metric.mem_sphere, dist_zero_right, norm_zero] at hz
      | ray => exact Or.inr (coneDiskChart_ray_sphere n (Metric.sphere_subset_closedBall hz) hs)
      | body => exact Or.inl rfl
    rcases hcases with hd | heq
    · have ho := hI hs
      simp only [mem_iUnion] at ho
      obtain ⟨k,hk,q,hq,hh⟩ := ho
      refine ⟨⟨k,q⟩, Or.inl (Or.inl ?_), hd ▸ hk, ?_⟩
      · exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨by simpa using hk,
          ⟨q,hq,rfl⟩⟩⟩
      · change f (coneDiskChart n d p.down z) ∈ _
        rw [hb hs]
        exact hh
    · have hd : 0 < d := by
        by_contra hh
        have hd0 : d = 0 := by omega
        subst d
        have hz0 : z = 0 := Subsingleton.elim _ _
        rw [hz0] at hz
        norm_num only [Metric.mem_sphere, dist_zero_right, norm_zero] at hz
      refine ⟨⟨0,qv⟩, Or.inr rfl, hd, ?_⟩
      change f (coneDiskChart n d p.down z) ∈
        (@CWComplex.map X _ Set.univ old 0 vtx) '' Metric.closedBall 0 1
      rw [heq]
      have hm : f (coneDiskVertex n).val ∈ (@CWComplex.map X _ Set.univ old 0 vtx).target := by
        rw [hvtx]; exact mem_singleton _
      let φ := @CWComplex.map X _ Set.univ old 0 vtx
      refine ⟨φ.symm (f (coneDiskVertex n).val), ?_, φ.right_inv hm⟩
      have hh := φ.map_target hm
      rw [@CWComplex.source_eq X _ Set.univ old 0 vtx] at hh
      exact Metric.ball_subset_closedBall hh
  · refine ⟨⟨k,Sum.inr ⟨q⟩⟩, Or.inl (Or.inr ⟨⟨k,⟨q⟩⟩,rfl⟩), hk, w, hw, ?_⟩
    change f (coneDiskChart n k q w) = f (coneDiskChart n d p.down z)
    exact congrArg f heq


/-- Cone replacement when the chosen attaching point is already a vertex.
The open disk is partitioned into its origin, the open ray to the sphere vertex,
and the cone on the complementary sphere cell. Boundaries of the ray are
vertices; boundaries of the top cone lie in the old frontier or the new ray.
The finite-open-refinement construction therefore supplies the desired CW
structure, with the old topology and every other characteristic map retained. -/
theorem cw_cone_replacement_at_vertex
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (old : CWComplex (Set.univ : Set X)) (n : ℕ)
    (i : @CWComplex.cell X _ Set.univ old (n+1))
    (f : PartialEquiv (Fin (n+1) → ℝ) X)
    (hf : f.source = Metric.ball 0 1)
    (ht : f.target = (@CWComplex.map X _ Set.univ old (n+1) i).target)
    (hc : ContinuousOn f (Metric.closedBall 0 1))
    (hi : ContinuousOn f.symm f.target)
    (hb : EqOn f (@CWComplex.map X _ Set.univ old (n+1) i) (Metric.sphere 0 1))
    (vtx : @CWComplex.cell X _ Set.univ old 0)
    (hvtx : (@CWComplex.map X _ Set.univ old 0 vtx).target = {f (coneDiskVertex n).val}) :
    ∃ new : CWComplex (Set.univ : Set X), ∃ R : CWFiniteRefinement old new,
      R.changed = {⟨n+1,i⟩} ∧
      ∃ v : @CWComplex.cell X _ Set.univ new 0,
        (@CWComplex.map X _ Set.univ new 0 v).target = {f 0} := by
  have hsub : ∀ d (p : ConeReplacementCell.{u} n d),
      (transportedConeChart n f d p).target ⊆
        (@CWComplex.map X _ Set.univ old (n+1) i).target := by
    intro d p y hy
    rw [← ht]
    exact hy.1
  have hdim : ∀ d, ConeReplacementCell.{u} n d → d ≤ n+1 := by
    rintro d ⟨p⟩
    cases p <;> omega
  obtain ⟨new,R,hR,hmap⟩ := cw_single_cell_replacement old ⟨n+1,i⟩
    (ConeReplacementCell n) (transportedConeChart n f)
    (transportedConeChart_source n f hf)
    (fun d p ↦ characteristic_trans_continuousOn _ _
      (coneDiskChart_continuous n d p.down).continuousOn hc (coneDiskChart_closed n d p.down))
    (fun d p ↦ characteristic_trans_continuousOn_symm _ _
      (coneDiskChart_inverse_continuous n d p.down) hi)
    hsub (transportedConeChart_disjoint n f hf)
    (ht ▸ transportedConeChart_cover n f hf) hdim
    (cone_replacement_frontier old n i f hf ht hb vtx hvtx)
  obtain ⟨v,hv⟩ := hmap 0 ⟨.peak⟩
  refine ⟨new,R,hR,v,?_⟩
  rw [hv, transportedConeChart_target n f hf, coneDiskChart_target_peak]
  exact image_singleton


/-- Insert an interior marked point as a vertex, changing only finitely many
cells of dimension at most its carrier dimension.

Proof: induct on that dimension. Dimension zero needs no change. In positive
dimension choose the distinguished point of the minimal sphere structure.
Its attaching image belongs to a strictly smaller old cell. Apply induction
there; the selected cell's characteristic map is unchanged because its
dimension is larger than every changed cell. Reparameterize its disk by the
boundary-fixing peak mover, then apply the three-cell cone replacement.
Compose the two finite subdivisions. The only additional changed old cell
is the selected carrier, which proves the dimension bound as well. -/
theorem cw_point_vertex_finite_refinement
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (n : ℕ) (old : CWComplex (Set.univ : Set X))
    (i : @CWComplex.cell X _ Set.univ old n) (a : Fin n → ℝ)
    (ha : a ∈ Metric.ball 0 1) :
    ∃ new : CWComplex (Set.univ : Set X), ∃ R : CWFiniteRefinement old new,
      (∃ v : @CWComplex.cell X _ Set.univ new 0,
        (@CWComplex.map X _ Set.univ new 0 v).target =
          {(@CWComplex.map X _ Set.univ old n i) a}) ∧
      ∀ e ∈ R.changed, e.1 ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      refine ⟨old, CWFiniteRefinement.refl old, ⟨i, ?_⟩, ?_⟩
      · rw [← PartialEquiv.image_source_eq_target, @CWComplex.source_eq X _ Set.univ old]
        ext y
        constructor
        · rintro ⟨z,hz,rfl⟩
          exact congrArg _ (Subsingleton.elim z a)
        · intro hy
          exact ⟨a,ha,hy.symm⟩
      · intro e he
        exact False.elim he
    | succ n =>
      obtain ⟨m,hm,j,b,hb,hbj⟩ := cw_point_vertex_refinement_boundary_smaller_cell X old i
        (coneDiskVertex n).val (coneDiskVertex n).property
      obtain ⟨mid,R,⟨vtx,hvtx⟩,hRdim⟩ := ih m hm j b (mem_ball_zero_iff.mpr hb)
      have hkeep : (⟨n+1,i⟩ : Σ k, @CWComplex.cell X _ Set.univ old k) ∉ R.changed := by
        intro h
        have hh := hRdim ⟨n+1,i⟩ h
        change n+1 ≤ m at hh
        omega
      obtain ⟨q,hq,hmap⟩ := R.unchanged (n+1) i hkeep
      obtain ⟨M,hM0,hMbd,hMclosed,hMball⟩ := cw_vertex_ambient_homeomorph a
        (mem_ball_zero_iff.mp ha)
      let φ := @CWComplex.map X _ Set.univ mid (n+1) q
      let f := reparamCharacteristic φ M
      have hf := reparamCharacteristic_source φ M (@CWComplex.source_eq X _ Set.univ mid _ q) hMball
      have hft := reparamCharacteristic_target φ M
      have hfc := reparamCharacteristic_continuousOn φ M (@CWComplex.continuousOn X _ Set.univ mid _ q)
        (fun z hz ↦ (hMclosed z).mpr hz)
      have hfi := reparamCharacteristic_continuousOn_symm φ M
        (@CWComplex.continuousOn_symm X _ Set.univ mid _ q)
      have hfb : EqOn f φ (Metric.sphere 0 1) := by
        intro z hz
        change φ (M z) = φ z
        rw [hMbd z hz]
      have hvtx' : (@CWComplex.map X _ Set.univ mid 0 vtx).target = {f (coneDiskVertex n).val} := by
        rw [hvtx,hbj]
        congr 1
        exact (hmap (Metric.sphere_subset_closedBall (coneDiskVertex n).property)).symm.trans
          (hfb (coneDiskVertex n).property).symm
      obtain ⟨new,S,hS,v,hv⟩ := cw_cone_replacement_at_vertex mid n q f hf hft hfc hfi hfb vtx hvtx'
      refine ⟨new,R.trans S,⟨v,?_⟩,?_⟩
      · rw [hv]
        congr 1
        change φ (M 0) = _
        rw [hM0]
        exact hmap (Metric.ball_subset_closedBall ha)
      · intro e he
        change e ∈ R.changed ∪ R.carrier '' S.changed at he
        rcases he with he | ⟨z,hz,rfl⟩
        · exact (hRdim e he).trans (by omega)
        · rw [hS] at hz
          have hz' : z = ⟨n+1,q⟩ := hz
          rw [hz',hq]


end
end HolomorphicAnosov

