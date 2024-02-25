-- Lambda expressions

inductive Expr : Type where
  | var : String → Expr
  | abs : String → Expr → Expr
  | app : Expr → Expr → Expr

open Expr

infixr:1 " :→ " => Expr.abs
infixl:9 " :. " => Expr.app

instance : ToString Expr :=
  ⟨λ expr ↦
    let rec aux : Expr → String
      | var v => v
      | v :→ e => s!"(λ{v}. {aux e})"
      | e₁ :. e₂ => s!"({aux e₁} {aux e₂})"
    aux expr⟩

#eval toString (("x" :→ (var "x")) :. ((var "y") :. (var "y")))
