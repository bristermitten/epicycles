import Epicycles.Env
import Epicycles.FuseDM.AST

/-!
# Evaluation of let-normal numeric expressions

This code was generated with the assistance of AI

Only `NumExpr` produces a numeric value; `Curve` and `Program` describe
geometric/parameterised structure rather than a single `Rat`.  We expose
just the numeric evaluator here — that is all the backwards semantics
needs (e.g. for the conditional cases of `mul` and `recip` updates).
-/

/-- Evaluate a let-free numeric expression. -/
def evalNumExpr {n : Nat} : Env n → NumExpr n → Rat
  | _,   .lit v   => v
  | env, .var i   => env i
  | env, .add a b => evalNumExpr env a + evalNumExpr env b
  | env, .mul a b => evalNumExpr env a * evalNumExpr env b
  | env, .recip a => (evalNumExpr env a)⁻¹
