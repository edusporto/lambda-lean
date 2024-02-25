-- Lambda reduction

import Init.Control.State

import «Lambda».Expr
import «Lambda».Subst
import «Lambda».Fresh
open Expr

class Reduction (m) extends Alternative m, Fresh m

def runReduction (r : ∀ {m}, [MonadStateOf ℕ m] → Expr → m Expr) (expr : Expr) : Option Expr :=
  Prod.fst <$> StateT.run (r expr) (freshest expr + 1)

def pass [Reduction m] (r : Expr → m Expr) (expr : Expr) : m Expr :=
  match expr with
  | var _ => failure
  | x :→ e => (x :→ ·) <$> r e
  | e₁ :. e₂ => ((· :. e₂) <$> r e₁) <|> ((e₁ :. ·) <$> r e₂)

def beta [Reduction m] : Expr → m Expr
  | (x :→ e₁) :. e₂ => subst x e₂ e₁
  | _ => failure

partial def norStep [Reduction m] (expr : Expr) : m Expr :=
  beta expr <|> pass norStep expr

partial def normalForm' [Reduction m] (expr : Expr) : m Expr :=
  (norStep expr >>= normalForm') <|> pure expr

-- def normalForm (expr : Expr) : Expr :=
--   let rec go e := (norStep e >>= go) <|> pure e
--   match runReduction go expr with
--   | some e => e
--   | none => ?
