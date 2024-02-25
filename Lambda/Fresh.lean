-- Generate fresh names

import Mathlib.Data.Finset.Basic
-- import Lean.Data.HashSet
import Mathlib.Data.List.MinMax

import «Lambda».Expr
open Expr

class Fresh (m) extends Monad m, MonadStateOf Nat m

partial def toFresh (n : Nat) :=
  let rec go : Nat → List Char
    | 0 => []
    | n =>
      let r := (n - 1) % 26 + 1
      Char.ofNat ('`'.toNat + r) :: go ((n - r) / 26) -- how can we prove this terminates?
  go n |> List.reverse |> List.cons '`' |> String.mk

#eval toFresh 27

def fromFresh : String → Nat
  | String.mk ('`' :: name) =>
    let nums := name.map ((· - '`'.toNat) ∘ Char.toNat)
    nums.foldl (λ acc num ↦ num + 26 * acc) 0
  | _ => 0

#eval fromFresh "`aa"

def fresh [Fresh m] : m String :=
  modifyGet (λ n ↦ ⟨toFresh n, n + 1⟩)

def freshest (expr : Expr) : Nat :=
  let rec go : Expr → List String
    | var v => {v}
    | x :→ e => go e ∪ {x}
    | e₁ :. e₂ => go e₁ ∪ go e₂

  go expr
    |> List.map fromFresh
    |> List.maximum
    |> WithBot.unbot' 0
