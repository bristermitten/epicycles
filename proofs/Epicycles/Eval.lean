import Epicycles.AST
import Epicycles.Env

/-! Lean implementation of the forward evaluation algorithm.
Generated WITHOUT the assistance of AI
-/

def evalExpr {n : Nat} : Env n → Expr n → Rat
  | _, Expr.lit v => v
  | env, Expr.var i => env i
  | env, Expr.add e1 e2 => evalExpr env e1 + evalExpr env e2
  | env, Expr.mul e1 e2 => evalExpr env e1 * evalExpr env e2
  | env, Expr.recip e => (evalExpr env e)⁻¹
  | env, Expr.let_ e1 e2 =>
      let v := evalExpr env e1
      let env' := Env.extend env v
      evalExpr env' e2
