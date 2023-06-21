import Lean

namespace Playground

inductive Expr where
  | bvar    : Nat → Expr                              -- bound variables
  | fvar    : FVarId → Expr                           -- free variables
  | mvar    : MVarId → Expr                           -- meta variables
  | sort    : Level → Expr                            -- Sort
  | const   : Name → List Level → Expr                -- constants
  | app     : Expr → Expr → Expr                      -- application
  | lam     : Name → Expr → Expr → BinderInfo → Expr  -- lambda abstraction
  | forallE : Name → Expr → Expr → BinderInfo → Expr  -- (dependent) arrow
  | letE    : Name → Expr → Expr → Expr → Bool → Expr -- let expressions
  -- less essential constructors:
  | lit     : Literal → Expr                          -- literals
  | mdata   : MData → Expr → Expr                     -- metadata
  | proj    : Name → Nat → Expr → Expr                -- projection

end Playground

open Lean

def z' := Expr.const `Nat.zero []
#eval z' -- Lean.Expr.const `Nat.zero []

-- We also show a second form where we write the name with double backticks. This checks that the name in fact refers to a defined constant, which is useful to avoid typos.

def z := Expr.const ``Nat.zero []
#eval z -- Lean.Expr.const `Nat.zero []

open Nat

def z₁ := Expr.const `zero []
#eval z₁ -- Lean.Expr.const `zero []

def z₂ := Expr.const ``zero []
#eval z₂ -- Lean.Expr.const `Nat.zero []

def one := Expr.app (.const ``Nat.succ []) z
#eval one
-- Lean.Expr.app (Lean.Expr.const `Nat.succ []) (Lean.Expr.const `Nat.zero [])

def natExpr : Nat → Expr 
| 0     => z
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

def sumExpr : Nat → Nat → Expr 
| n, m => mkAppN (.const ``Nat.add []) #[natExpr n, natExpr m]

#eval sumExpr 0 1

def constZero : Expr := 
  .lam `x (.const ``Nat []) (.const ``Nat.zero []) BinderInfo.default

#eval constZero
-- Lean.Expr.lam `x (Lean.Expr.const `Nat []) (Lean.Expr.const `Nat.zero [])
--   (Lean.BinderInfo.default)

def nat : Expr := .const ``Nat []

def addOne : Expr :=
  .lam `x nat
    (mkAppN (.const ``Nat.add []) #[.bvar 0, mkNatLit 1])
    BinderInfo.default

def mapAddOneNil : Expr :=
  mkAppN (.const ``List.map [levelOne, levelOne])
    #[nat, nat, addOne, .app (.const ``List.nil [levelOne]) nat]

elab "mapAddOneNil" : term => return mapAddOneNil

#check mapAddOneNil
-- List.map (fun x => Nat.add x 1) [] : List Nat

set_option pp.universes true in
set_option pp.explicit true in
#check mapAddOneNil
-- @List.map.{1, 1} Nat Nat (fun x => Nat.add x 1) (@List.nil.{1} Nat) : List.{1} Nat

#reduce mapAddOneNil
-- []