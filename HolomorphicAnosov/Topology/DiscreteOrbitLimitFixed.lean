import Mathlib.Topology.Constructions
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Discrete orbits converging to fixed points

Source: Jiesong Zhang, *Codimension-one holomorphic Anosov diffeomorphisms*,
arXiv:2609.37695v1, printed p.14, proof of Lemma 4.2. The orbit argument is
stated in its general topological form, together with its real-lattice
consequence. All notions are Mathlib's existing definitions.
-/

open Filter
open scoped Topology _root_.Topology

namespace HolomorphicAnosov

/-- An injective self-map preserving a discrete subset has no nonconstant
orbit converging to a fixed point in that subset. Consequently an
inverse-contracting real subspace meets a preserved full real lattice only
at zero.

Source: Zhang, arXiv:2609.37695v1, printed p.14, Lemma 4.2 proof, paragraph
beginning "For gamma != 0": an element of the unstable space and the lattice
has inverse iterates in the lattice converging to zero. Printed p.11 states
the lattice preservation as `A(Gamma) = Gamma`. The subtype/filter details
and the general injective-map formulation are agent-written expansions of
that argument, as recorded in `topology.discrete_orbit_limit_fixed`.

Natural-language proof: Since x belongs to s and T maps s into itself,
induction shows that every iterate T^n x belongs to s. Regard these iterates
as points u_n of the original subtype s, and regard z as z_s in that subtype.
Their ambient convergence implies u_n converges to z_s by
`tendsto_subtype_rng`. By `IsDiscrete s`, the inherited subtype topology is
discrete, so `nhds_discrete` identifies its neighborhood filter at z_s with
the pure filter at z_s. By `Filter.tendsto_pure`, eventually u_n = z_s.
The natural-number atTop filter therefore supplies an N with T^N x = z.
Induction from T z = z gives T^N z = z. Induction from injectivity of T gives
injectivity of T^N, including N = 0, so x = z.

For the second assertion let gamma belong to both U and Gamma. Set T to the
actual inverse A.symm and z to zero. A.symm is injective and fixes zero by
linearity. The image equality A(Gamma) = Gamma implies inverse preservation:
for delta in Gamma choose eta in Gamma with A eta = delta; applying A.symm
gives A.symm delta = eta in Gamma. Gamma has its inherited discrete topology,
and gamma's inverse iterates converge to zero by the hypothesis on U. The
first assertion gives gamma = 0. Conversely zero belongs to both submodules,
so their set intersection is exactly {0}.

The ambient topology in the first assertion need not be discrete or
Hausdorff, s need not be closed, and T need not be continuous or surjective.
The second assertion permits dimension zero and the zero subspace. It uses
pointwise inverse decay, with no hyperbolicity or rate assumption. The full
lattice hypothesis is Mathlib's `IsZLattice` under `DiscreteTopology Gamma`;
no complex-linearity or extra lattice-invariance hypothesis is introduced.
-/
theorem discrete_orbit_limit_fixed :
    (∀ (X : Type*) [TopologicalSpace X] (T : X → X) (s : Set X),
      Function.Injective T → IsDiscrete s → Set.MapsTo T s s →
      ∀ (x z : X), x ∈ s → z ∈ s → T z = z →
        Tendsto (fun n : ℕ ↦ T^[n] x) atTop (𝓝 z) → x = z) ∧
    (∀ (n : ℕ) (A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
      (Γ : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology Γ] [IsZLattice ℝ Γ],
      A '' (Γ : Set (Fin n → ℝ)) = (Γ : Set (Fin n → ℝ)) →
      ∀ (U : Submodule ℝ (Fin n → ℝ)),
        (∀ γ ∈ U, Tendsto (fun k : ℕ ↦ (A.symm : (Fin n → ℝ) → (Fin n → ℝ))^[k] γ)
          atTop (𝓝 (0 : Fin n → ℝ))) →
        (U : Set (Fin n → ℝ)) ∩ (Γ : Set (Fin n → ℝ)) = {0}) := by
  constructor
  ·
    intro X _ T s hT hs hpres x z hx hz hfixed hlim
    have : DiscreteTopology s := isDiscrete_iff_discreteTopology.mp hs
    have hmem : ∀ n : ℕ, T^[n] x ∈ s := by
      intro n
      induction n with
      | zero => exact hx
      | succ n hn => simpa only [Function.iterate_succ_apply'] using hpres hn
    let u : ℕ → s := fun n ↦ ⟨T^[n] x, hmem n⟩
    have hu : Tendsto u atTop (𝓝 (⟨z, hz⟩ : s)) :=
      tendsto_subtype_rng.mpr hlim
    rw [nhds_discrete s, tendsto_pure] at hu
    obtain ⟨n, hn⟩ := hu.exists
    apply hT.iterate n
    exact (congrArg Subtype.val hn).trans (Function.iterate_fixed hfixed n).symm
  · intro n A Γ _ _ hpres U hcontract
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨U.zero_mem, Γ.zero_mem⟩, ?_⟩
    intro γ hγ
    have hinv : Set.MapsTo A.symm (Γ : Set (Fin n → ℝ)) Γ := by
      intro δ hδ
      obtain ⟨η, hη, heq⟩ := hpres.symm ▸ hδ
      simpa only [← heq, A.symm_apply_apply] using hη
    have hmem : ∀ k : ℕ, (A.symm : (Fin n → ℝ) → (Fin n → ℝ))^[k] γ ∈ Γ := by
      intro k
      induction k with
      | zero => exact hγ.2
      | succ k hk =>
        rw [Function.iterate_succ_apply']
        exact hinv hk
    let u : ℕ → Γ := fun k ↦ ⟨(A.symm : (Fin n → ℝ) → (Fin n → ℝ))^[k] γ, hmem k⟩
    have hu : Tendsto u atTop (𝓝 (0 : Γ)) := tendsto_subtype_rng.mpr (hcontract γ hγ.1)
    rw [nhds_discrete Γ, tendsto_pure] at hu
    obtain ⟨k, hk⟩ := hu.exists
    apply A.symm.injective.iterate k
    exact (congrArg Subtype.val hk).trans (Function.iterate_fixed A.symm.map_zero k).symm


end HolomorphicAnosov
