import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset
import Mathlib.LinearAlgebra.Matrix.Trace

namespace HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting

open Set
open scoped BigOperators Classical
noncomputable section

/-- The zero-one matrix of a finite directed relation. -/
noncomputable def edgeMatrix {A : Type*} (B : A → A → Prop) : Matrix A A ℤ := by
  classical
  exact fun x y ↦ if B x y then 1 else 0


end
end HolomorphicAnosov.Dynamics.ManningOriginalBasicSetSignedTraceG7.MatrixCounting
