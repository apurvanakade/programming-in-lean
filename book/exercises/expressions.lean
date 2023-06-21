-- Create expression 1 + 2 with Expr.app.
-- Create expression 1 + 2 with Lean.mkAppN.
-- Create expression fun x => 1 + x.
-- [De Bruijn Indexes] Create expression fun a, fun b, fun c, (b * a) + c.
-- Create expression fun x y => x + y.
-- Create expression fun x, String.append "hello, " x.
-- Create expression ∀ x : Prop, x ∧ x.
-- Create expression Nat → String.
-- Create expression fun (p : Prop) => (λ hP : p => hP).
-- [Universe levels] Create expression Type 6.

import Lean 

open Lean

def nat : Expr := .const ``Nat []

def zero := Expr.const ``Nat.zero []
def one := Expr.app (.const ``Nat.succ []) zero
def two := Expr.app (.const ``Nat.succ []) one

def natExpr : Nat → Expr 
| 0     => zero
| n + 1 => .app (.const ``Nat.succ []) (natExpr n)

def one_plus_two_Expr := Expr.app (Expr.app (.const ``Nat.add []) two) one

elab "one_plus_two" : term => return one_plus_two_Expr

#eval one_plus_two

def one_plus_two_Expr2 := mkAppN (.const ``Nat.add []) #[one, two]

elab "one_plus_two2" : term => return one_plus_two_Expr2

#eval one_plus_two2


def succ : Expr := 
  .lam `n nat (Expr.app (.const ``Nat.succ []) (.bvar 0)) BinderInfo.default

elab "succ" : term => return succ

#eval succ 2

def DeBruijn := 