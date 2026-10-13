import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrier
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Completeness of the normalized parameter graph carrier

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, LNM 583 (1977), Sublemma 5.2,
printed pp.54–55, and parameter insertion on p.62. The dependent normalization
is the one specified in Step 2 of the parameter graph construction.

DAG node: `hps.parameter_graph_carrier_complete_g12`.
-/

namespace HolomorphicAnosov

/-- The unit-Lipschitz subset of the normalized dependent graph carrier is
closed, complete, and nonempty when every receiving fibre is complete.

Source: Hirsch–Pugh–Shub, *Invariant Manifolds*, Sublemma 5.2, pp.54–55:
weighted convergence gives convergence at each fixed input, and the
unit-Lipschitz inequalities pass to the limit. Page 62 inserts the parameter
and takes the supremum over parameters and nonzero fibre inputs. The dependent
`lp∞` implementation below uses exactly those indices and original fibre norms.

Proof: for a fixed parameter p and nonzero x, graph evaluation is coordinate
evaluation in `lp∞` followed by multiplication by the fixed scalar ‖x‖. The
coordinate norm bound makes that map continuous. At x=0 the recovered graph
value is the constant zero, hence is also continuous. Thus for every fixed
same-fibre pair x,y, the map q ↦ ‖s_q(p,x) - s_q(p,y)‖ is continuous. The
constraint ‖s_q(p,x) - s_q(p,y)‖ ≤ ‖x-y‖ is closed by `isClosed_le`.
Intersecting these constraints over p,x,y gives precisely
`parameterGraphUnitSet E F`, since these inequalities are equivalent to
`LipschitzWith 1` in each fibre. Arbitrary intersections of closed sets are
closed. Complete receiving fibres give completeness of the dependent `lp∞`
carrier; `IsClosed.completeSpace_coe` supplies completeness of its closed
unit-slope subtype with the induced metric. Finally the zero lp family recovers
the zero map in every fibre, which is 1-Lipschitz, so the set is nonempty.

The parameter type may be empty, and either input or receiving fibres may have
zero rank. If there are no nonzero inputs, the lp index type is empty and the
carrier is a singleton. No finite-dimensionality, topology on parameters,
parameter continuity, or continuity of normalized coordinates at the zero
input is assumed. The following proof uses the imported closed-set and lp coordinate APIs directly. -/
theorem parameter_graph_carrier_complete
    {A : Type*} (E F : A → Type*)
    [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
    [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
    [∀ p, CompleteSpace (F p)] :
    IsClosed (parameterGraphUnitSet E F) ∧
    CompleteSpace {q : ParameterGraphCarrier E F // q ∈ parameterGraphUnitSet E F} ∧
    (parameterGraphUnitSet E F).Nonempty := by
  classical
  have hclosed : IsClosed (parameterGraphUnitSet E F) := by
    have heq : parameterGraphUnitSet E F =
        ⋂ (p : A) (x : E p) (y : E p), {q : ParameterGraphCarrier E F |
          ‖parameterGraphValue E F q p x - parameterGraphValue E F q p y‖ ≤ ‖x - y‖} := by
      ext q
      simp only [parameterGraphUnitSet, Set.mem_ofPred_eq, Set.mem_iInter,
        lipschitzWith_iff_dist_le_mul, NNReal.coe_one, one_mul, dist_eq_norm]
    rw [heq]
    apply isClosed_iInter
    intro p
    apply isClosed_iInter
    intro x
    apply isClosed_iInter
    intro y
    apply isClosed_le _ continuous_const
    apply Continuous.norm
    apply Continuous.sub
    · by_cases hx : x = 0
      · simp only [parameterGraphValue, hx]
        exact continuous_const
      · simp only [parameterGraphValue, dite_eq_right hx]
        exact continuous_const.smul
          (lp.evalCLM ℝ (fun i : Sigma (fun p ↦ {x : E p // x ≠ 0}) ↦ F i.1)
            ⊤ ⟨p, ⟨x, hx⟩⟩).continuous
    · by_cases hy : y = 0
      · simp only [parameterGraphValue, hy]
        exact continuous_const
      · simp only [parameterGraphValue, dite_eq_right hy]
        exact continuous_const.smul
          (lp.evalCLM ℝ (fun i : Sigma (fun p ↦ {x : E p // x ≠ 0}) ↦ F i.1)
            ⊤ ⟨p, ⟨y, hy⟩⟩).continuous
  refine ⟨hclosed, hclosed.completeSpace_coe, 0, ?_⟩
  intro p
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;>
    simp [parameterGraphValue, hx, hy]

end HolomorphicAnosov

