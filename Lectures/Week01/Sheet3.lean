/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

-- ## how to define new types from old types

-- Terms can be anonnymous functions (also called λ-expressions)
#check ℕ

-- New types can be created by defining a function between types
#check ℕ → ℤ
#check fun (x : ℕ) ↦ x
#check fun (x : ℕ) ↦ (x : ℤ)
#check fun (x : ℕ) ↦ (x^2 + x - 10 : ℤ)

def f₁ (x : ℕ) : ℤ :=
  x ^ 2 + x - 10

def f₂  := fun (x : ℕ) ↦ (x ^ 2 + x - 10 : ℤ)

#check f₁
#check f₂

#check ℕ → ℕ → Prop
#check fun x : ℕ ↦ fun y ↦ x = y

def f₃ := fun x : ℕ ↦ fun y : ℕ  ↦ x = y
def f₄ (x y : ℕ) : Prop := x = y

def f₅ (p : String × ℕ) : Prop := p.1.length = p.2
def f₆ (s : String) (n : ℕ) : Prop := s.length = n

-- function can be partially applied
#check f₃ 0
#check f₃ 0 0

#check f₄ 0
#check f₄ 0 0

#check f₅ ("teste", 2)

#check f₆ "teste"
#check f₆ "teste" 2

example : f₃ 0 0 := by rfl

/-! New tactics
* `rewrite` [h] - replace a term in the goal with an equivalent term [h].
* `assumption` - we are done because ∃`h` s.t. `exact h` can close the goal
* `rw` -- rewrite, followed by trying to close the goal by rfl.
-/

example (x: ℕ): f₃ 0 x → x = 0 := by
  intro h
  rw [f₃] at h
  symm at h ; assumption

-- Give a direct proof
example (x: ℕ): f₃ x 1 → x ≠ 2 := by
  intro h₁
  rw [f₃] at h₁
  rw [h₁]
  trivial
  /-
  intro h₂
  rw [Nat.succ_inj] at h₂
  symm at h₂
  apply Nat.succ_ne_zero at h₂
  assumption -/

example (x y: ℕ): f₃ 0 x ∧ f₃ 0 y → x = y := by
  intro h
  repeat rw [f₃] at h
  rw [← h.1]
  rw [← h.2]


/-! Bonus:

* `by_contra` - assume the negation of the goal and prove False
* `contradiction` - we are done because we have a proof of `h : P` and `h' : ¬
  P`
* `trivial` - apply `rfl` or `assumption` or `contradiction` tactics
-/

-- Prove by contradiction
example {a b : Type} (h1 : a = b) : a = b := by
  by_contra h2
  -- exact h2 h1
  contradiction

example (x: ℕ): f₃ x 1 → x ≠ 2 := by
  intro h1
  rw [f₃] at h1
  by_contra h2
  rw [h2] at h1
  trivial
