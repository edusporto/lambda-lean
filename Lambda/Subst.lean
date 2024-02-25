-- Lambda substitution

import Mathlib.Data.Finset.Basic

import «Lambda».Expr
import «Lambda».Fresh
open Expr

def renameUnsafe (src : String) (tgt : String) (expr : Expr) : Expr :=
  let rec go : Expr → Expr
    | var x =>
      if x == src
        then var tgt
        else var x
    | x :→ e =>
      if x == src
        then x :→ e
        else x :→ go e
    | e₁ :. e₂ => go e₁ :. go e₂
  go expr

def rename [Fresh m] (src : String) (expr : Expr) : m (String × Expr) := do
  let tgt ← fresh
  pure (tgt, renameUnsafe src tgt expr)

def free : Expr → Finset String
  | var x => {x}
  | x :→ e => free e \ {x}
  | e₁ :. e₂ => free e₁ ∪ free e₂

partial def subst [Fresh m] (x : String) (what : Expr) (expr : Expr) : m Expr :=
  let rec go : Expr → m Expr
    | var y =>
      if x == y
        then pure what
        else pure (var y)
    | y :→ f =>
      if x == y
        then pure (y :→ f)
      else if y ∈ (free what)
        then do
          let (y', f') ← rename y f
          (y' :→ ·) <$> go f' -- how can we prove this terminates?
      else
        (y :→ ·) <$> go f
    | f₁ :. f₂ => (· :. ·) <$> go f₁ <*> go f₂

  go expr
