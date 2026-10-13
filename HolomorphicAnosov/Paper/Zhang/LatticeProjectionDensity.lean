import HolomorphicAnosov.Linear.InvariantComplementProjection
import HolomorphicAnosov.Linear.HyperbolicDecayComplement
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The projections of an invariant full lattice onto the forward and backward decay spaces of a
hyperbolic linear automorphism are dense. (Zhang, Lemma 3.1, p.11) -/

open Filter Set
open scoped Topology _root_.Topology TensorProduct

universe u

namespace HolomorphicAnosov

namespace LatticeDensityPreparation

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- An integer submodule spanning a finite-dimensional real normed space has uniformly bounded
representatives for all additive cosets. (Zhang, Lemma 3.1) -/
theorem bounded_representatives (Γ : Submodule ℤ V)
    (hΓ : Submodule.span ℝ (Γ : Set V) = ⊤) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : V, ∃ γ : Γ, ‖x - (γ : V)‖ ≤ R := by
  classical
  obtain ⟨v, hv, hspan, hlin⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Γ : Set V)
  let b := Module.Basis.mk hlin (by rw [hspan, hΓ])
  have hb : ∀ i, b i ∈ Γ := by simpa [b] using hv
  have hsub : Submodule.span ℤ (Set.range b) ≤ Γ :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
  refine ⟨(∑ i, ‖b i‖) + 1, by positivity, ?_⟩
  intro x
  refine ⟨⟨ZSpan.floor b x, hsub (ZSpan.floor b x).property⟩, ?_⟩
  exact (ZSpan.norm_fract_le b x).trans (by linarith)

/-- Pointwise convergence to zero of linear maps on a finite-dimensional normed space implies
convergence of their operator norms to zero. (Zhang, Lemma 3.1) -/
theorem opNorm_tendsto_zero (L : ℕ → V →L[ℝ] V)
    (hL : ∀ v, Tendsto (fun n ↦ L n v) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ‖L n‖) atTop (𝓝 0) := by
  classical
  let b := Module.finBasis ℝ V
  obtain ⟨C, hC, hbound⟩ := b.exists_opNorm_le (F := V)
  apply squeeze_zero (fun _ ↦ norm_nonneg _)
    (fun n ↦ hbound (show 0 ≤ ∑ i, ‖L n (b i)‖ from Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))
      (fun i ↦ Finset.single_le_sum (fun j _ ↦ norm_nonneg (L n (b j))) (Finset.mem_univ i)))
  have ht : Tendsto (fun n ↦ ∑ i, ‖L n (b i)‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ ↦ (hL (b i)).norm)
  simpa using ht.const_mul C

omit [FiniteDimensional ℝ V] in
/-- Every nonnegative iterate of a lattice-preserving linear automorphism preserves lattice
membership. (Zhang, Lemma 3.1) -/
theorem pow_mem_lattice (Γ : Submodule ℤ V) (B : V ≃L[ℝ] V)
    (hB : B '' (Γ : Set V) = (Γ : Set V)) (n : ℕ) {v : V} (hv : v ∈ Γ) :
    (B ^ n) v ∈ Γ := by
  induction n with
  | zero => change v ∈ Γ; exact hv
  | succ n ih =>
    rw [pow_succ']
    change B ((B ^ n) v) ∈ Γ
    change B ((B ^ n) v) ∈ (Γ : Set V)
    rw [← hB]
    exact ⟨_, ih, rfl⟩

/-- The projection of a full invariant lattice onto an invariant summand is dense if every vector in
that summand converges to zero under forward iteration. (Zhang, Lemma 3.1) -/
theorem dense_projection_of_decay (Γ : Submodule ℤ V)
    (hΓ : Submodule.span ℝ (Γ : Set V) = ⊤) (B : V ≃L[ℝ] V)
    (hB : B '' (Γ : Set V) = (Γ : Set V))
    (P Q : Submodule ℝ V) (h : IsCompl P Q)
    (hP : ∀ n v, v ∈ P → (B ^ n) v ∈ P)
    (hQ : ∀ n v, v ∈ Q → (B ^ n) v ∈ Q)
    (hdec : ∀ v ∈ P, Tendsto (fun n : ℕ ↦ (B ^ n) v) atTop (𝓝 0)) :
    DenseRange (fun γ : Γ ↦ P.projectionOnto Q h γ) := by
  classical
  let p : V →L[ℝ] V := (P.projection Q h).toContinuousLinearMap
  let L (n : ℕ) : V →L[ℝ] V := (B ^ n).toContinuousLinearMap.comp p
  have hL : Tendsto (fun n ↦ ‖L n‖) atTop (𝓝 0) :=
    opNorm_tendsto_zero L (fun v ↦ hdec (p v) (Submodule.projection_apply_mem h v))
  obtain ⟨R, hR, hrep⟩ := bounded_representatives Γ hΓ
  rw [Metric.denseRange_iff]
  intro s ε hε
  have ht : Tendsto (fun n ↦ ‖L n‖ * R) atTop (𝓝 0) := by
    simpa using hL.mul_const R
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨γ, hγ⟩ := hrep ((B.symm ^ n) (s : V))
  let δ : Γ := ⟨(B ^ n) (γ : V), pow_mem_lattice Γ B hB n γ.property⟩
  refine ⟨δ, ?_⟩
  have hinv : (B ^ n) ((B.symm ^ n) (s : V)) = s := by
    have he : B.symm ^ n = (B ^ n).symm := by
      change B⁻¹ ^ n = (B ^ n)⁻¹
      exact inv_pow B n
    rw [he]
    exact (B ^ n).apply_symm_apply s
  have heq : (s : V) - P.projection Q h (δ : V) =
      L n ((B.symm ^ n) (s : V) - (γ : V)) := by
    change (s : V) - P.projection Q h ((B ^ n) (γ : V)) =
      (B ^ n) (P.projection Q h ((B.symm ^ n) (s : V) - (γ : V)))
    have hc := projection_commutes P Q h (B ^ n).toLinearMap (hP n) (hQ n)
      ((B.symm ^ n) (s : V) - (γ : V))
    change P.projection Q h ((B ^ n) _) = (B ^ n) (P.projection Q h _) at hc
    rw [← hc, map_sub, map_sub, hinv, Submodule.projection_apply_left]
  change dist (s : V) (P.projection Q h (δ : V)) < ε
  rw [dist_eq_norm, heq]
  exact ((L n).le_opNorm _).trans_lt
    ((mul_le_mul_of_nonneg_left hγ (norm_nonneg _)).trans_lt hn)

omit [FiniteDimensional ℝ V] in
/-- A commuting continuous linear automorphism preserves convergence of forward orbits to zero.
(Zhang, Lemma 3.1) -/
theorem decay_map_of_commute (B T : V ≃L[ℝ] V) (hc : Commute B T) {v : V}
    (hv : Tendsto (fun n : ℕ ↦ (B ^ n) v) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (B ^ n) (T v)) atTop (𝓝 0) := by
  have ht := T.continuous.tendsto 0 |>.comp hv
  simp only [map_zero] at ht
  convert ht using 1
  funext n
  exact congrArg (fun e : V ≃L[ℝ] V ↦ e v) ((hc.pow_left n).eq)

/-- The ambient closure of the image of a dense map into a finite-dimensional subspace is that
subspace. (Zhang, Lemma 3.1) -/
theorem closure_of_dense_subtype {ι : Type*} (P : Submodule ℝ V) (f : ι → P)
    (hf : DenseRange f) : closure (range (fun i ↦ (f i : V))) = (P : Set V) := by
  apply le_antisymm
  · exact closure_minimal (by rintro _ ⟨i, rfl⟩; exact (f i).property)
      P.closed_of_finiteDimensional
  · intro v hv
    rw [Metric.mem_closure_range_iff]
    intro ε hε
    obtain ⟨i, hi⟩ := Metric.denseRange_iff.mp hf ⟨v, hv⟩ ε hε
    exact ⟨i, hi⟩

end LatticeDensityPreparation

/-- The lattice projections onto both the forward and backward decay spaces of a hyperbolic
lattice-preserving automorphism have ambient closures equal to those spaces. (Zhang, Lemma 3.1,
p.11) -/
theorem lattice_projection_density
    {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Γ : Submodule ℤ V) [DiscreteTopology Γ]
    (hΓ : Submodule.span ℝ (Γ : Set V) = ⊤)
    (A : V ≃L[ℝ] V) (hAΓ : A '' (Γ : Set V) = (Γ : Set V))
    (hhyperbolic : ∀ μ : ℂ,
      Module.End.HasEigenvalue (A.toLinearMap.baseChange ℂ) μ → ‖μ‖ ≠ 1) :
    let decay : (V ≃L[ℝ] V) → Submodule ℝ V := fun B ↦ {
      carrier := {v | Tendsto (fun n : ℕ ↦ (B ^ n) v) atTop (𝓝 0)}
      zero_mem' := by simp
      add_mem' := by
        intro v w hv hw
        simpa only [Set.mem_ofPred_eq, map_add, add_zero] using hv.add hw
      smul_mem' := by
        intro c v hv
        simpa only [Set.mem_ofPred_eq, map_smul, smul_zero] using hv.const_smul c }
    ∃ h : IsCompl (decay A) (decay A.symm),
      DenseRange (fun γ : Γ ↦
        (decay A).projectionOnto (decay A.symm) h γ) ∧
      DenseRange (fun γ : Γ ↦
        (decay A.symm).projectionOnto (decay A) h.symm γ) ∧
      closure (Set.range (fun γ : Γ ↦
        (((decay A).projectionOnto
          (decay A.symm) h γ) : V))) =
        (decay A : Set V) ∧
      closure (Set.range (fun γ : Γ ↦
        (((decay A.symm).projectionOnto
          (decay A) h.symm γ) : V))) =
        (decay A.symm : Set V) := by
  classical
  let decay : (V ≃L[ℝ] V) → Submodule ℝ V := fun B ↦ {
      carrier := {v | Tendsto (fun n : ℕ ↦ (B ^ n) v) atTop (𝓝 0)}
      zero_mem' := by simp
      add_mem' := by
        intro v w hv hw
        simpa only [Set.mem_ofPred_eq, map_add, add_zero] using hv.add hw
      smul_mem' := by
        intro c v hv
        simpa only [Set.mem_ofPred_eq, map_smul, smul_zero] using hv.const_smul c }
  change ∃ h : IsCompl (decay A) (decay A.symm),
      DenseRange (fun γ : Γ ↦
        (decay A).projectionOnto (decay A.symm) h γ) ∧
      DenseRange (fun γ : Γ ↦
        (decay A.symm).projectionOnto (decay A) h.symm γ) ∧
      closure (Set.range (fun γ : Γ ↦
        (((decay A).projectionOnto
          (decay A.symm) h γ) : V))) =
        (decay A : Set V) ∧
      closure (Set.range (fun γ : Γ ↦
        (((decay A.symm).projectionOnto
          (decay A) h.symm γ) : V))) =
        (decay A.symm : Set V)
  
  obtain ⟨S, U, hS, hU, hSU, _⟩ := hyperbolic_decay_space_complement A hhyperbolic
  have hS' : S = decay A := by ext v; exact hS v
  have hU' : U = decay A.symm := by ext v; exact hU v
  subst S U
  have hinv (B T : V ≃L[ℝ] V) (hc : Commute B T) (n : ℕ) (v : V)
      (hv : v ∈ decay B) : (T ^ n) v ∈ decay B :=
    LatticeDensityPreparation.decay_map_of_commute B (T ^ n) (hc.pow_right n) hv
  have hAinv : A.symm '' (Γ : Set V) = (Γ : Set V) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨v, hv, rfl⟩
      have h : v ∈ A '' (Γ : Set V) := hAΓ.symm ▸ hv
      obtain ⟨w, hw, rfl⟩ := h
      simpa using hw
    · intro v hv
      refine ⟨A v, ?_, A.symm_apply_apply v⟩
      rw [← hAΓ]
      exact ⟨v, hv, rfl⟩
  
  
  have hs := LatticeDensityPreparation.dense_projection_of_decay Γ hΓ A hAΓ
    (decay A) (decay A.symm) hSU
    (hinv A A (Commute.refl A))
    (hinv A.symm A (by exact Commute.inv_left_self A)) (fun _ hv ↦ hv)
  have hu := LatticeDensityPreparation.dense_projection_of_decay Γ hΓ A.symm hAinv
    (decay A.symm) (decay A) hSU.symm
    (hinv A.symm A.symm (Commute.refl A.symm))
    (hinv A A.symm (by exact Commute.inv_right_self A)) (fun _ hv ↦ hv)
  exact ⟨hSU, hs, hu,
    LatticeDensityPreparation.closure_of_dense_subtype _ _ hs,
    LatticeDensityPreparation.closure_of_dense_subtype _ _ hu⟩


end HolomorphicAnosov
