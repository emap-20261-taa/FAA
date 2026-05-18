/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
import Lectures.Week08.API

set_option autoImplicit false
set_option tactic.hygienic false

-- # Q: How to analyze time complexity?

-- We will instrument the code to track the time. However, we do not want to
-- interfere the correctness analysis. We learn an elegant way to do this using
-- Monad

-- Separation of concerns: the correctness proof and running time proof should
-- not interfere to each other

def len : List ℕ → ℕ
| [] => 0
| _ :: xs => 1 + len xs

-- lenT with do notations
def lenT : List ℕ → TimeM ℕ
| [] => ✓ 0, 0
| _ :: xs => do
    let len_xs ← lenT xs
    ✓ (1 + len_xs)

-- Example usage
#eval lenT []
#eval lenT [3,2,5]
#eval lenT [1,2,3,4,5]

#eval ((do
 pure 10
 pure 20) : Option Nat)

theorem lenT_correctness (xs : List ℕ): (lenT xs).ret = len xs := by
  induction xs
  · rfl
  · simp only [lenT, bind, TimeM.tick, TimeM.ret_bind]
    rw [tail_ih]
    rfl

theorem lenT_time (xs : List ℕ ): (lenT xs).time = (len xs) := by
  induction xs
  · rfl
  · simp only [lenT, bind, TimeM.tick, TimeM.time_of_bind]
    rw [tail_ih]
    rw [show len (head :: tail) = 1 + len tail from rfl]
    linarith


-- ============================================================================
-- EXERCISE 1: Sum of a list
-- ============================================================================
-- Implement sumT that computes the sum of a list with time tracking
-- Each recursive call should cost 1 time unit
-- Expected time complexity: n where n is the length of the list

def sumT : List ℕ → TimeM ℕ
| [] => ✓ 0, 0
| x :: xs => do
   let s ← sumT xs
   ✓ (x + s)

def sum : List ℕ → ℕ
| [] => 0
| x :: xs => x + sum xs

-- Prove correctness
theorem sumT_correctness (xs : List ℕ): (sumT xs).ret = sum xs := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [sumT, bind, TimeM.tick, TimeM.ret_bind]
    rw [ih, sum]


-- Prove time complexity
theorem sumT_time (xs : List ℕ): (sumT xs).time = xs.length := by
  induction xs
  · rfl
  · simp only [sumT, bind, TimeM.tick, TimeM.time_of_bind]
    rw [tail_ih]
    rw [List.length]


-- ============================================================================
-- EXERCISE 2: Reverse a list
-- ============================================================================
-- Implement reverseT that reverses a list with time tracking
-- Each cons operation should cost 1 time unit
-- Expected time complexity: n² where n is the length of the list

def fib : Nat → Nat
 | 0 => 0
 | 1 => 1
 | n + 2 => fib n + fib (n + 1)

def fib' : Nat → Nat → Nat → Nat
  | 0, a, _b => a
  | 1, a, _b => a
  | n + 2, a, b => fib' (n + 1) (a + b) a


def appendT : List ℕ → List ℕ → TimeM (List ℕ)
| [], ys => ✓ ys, 0
| x :: xs, ys => do
    let r ← appendT xs ys
    ✓ (x :: r)

def reverseT : List ℕ → TimeM (List ℕ)
| [] => ✓ [], 0
| x :: xs => do
    let r ← reverseT xs
    appendT r [x]

def reverse : List ℕ → List ℕ
| [] => []
| x :: xs => reverse xs ++ [x]

example : reverse [1,2,3] = [3,2,1] := by
  rewrite [reverse]
  rewrite [reverse]
  rewrite [reverse]
  rewrite [reverse]
  rw [← List.append_eq]
  rw [← List.append_eq]
  rw [← List.append_eq]
  rewrite [List.append]
  rewrite [List.append]
  rewrite [List.append]
  rewrite [List.append]
  rewrite [List.append]
  rewrite [List.append]
  simp

theorem appendT_correctness (xs ys : List ℕ)
 : (appendT xs ys).ret = List.append xs ys := by
 induction xs
 . simp [appendT]
 . simp [appendT, List.append]
   assumption

-- TODO: Prove correctness
theorem reverseT_correctness (xs : List ℕ)
  : (reverseT xs).ret = reverse xs := by
  induction xs with
  | nil =>
    rw [reverseT, reverse, TimeM.tick]
  | cons a as ih₁ =>
    rw [reverseT, reverse]
    cases as
    . simp [reverseT, appendT, reverse]
    . simp [reverseT, reverse]
      simp [reverseT] at ih₁
      rw [ih₁, reverse]
      rw [appendT_correctness]
      simp only [List.append_eq, List.append_assoc]
      simp only [List.cons_append, List.nil_append]


theorem appendT_time (xs ys : List ℕ) :
  (appendT xs ys).time = xs.length := by
  induction xs with
  | nil => grind [appendT]
  | cons a as ih =>
    simp [appendT, ih]


theorem reverseT_length (xs : List Nat) :
  (reverseT xs).ret.length = xs.length := by
  rw [reverseT_correctness]
  induction' xs with a as ih
  . rfl
  . simp [reverse, ih]

-- Hint: You'll need a helper lemma about the time of append
-- TODO: Prove time complexity is O(n²)
theorem reverseT_time_quadratic (xs : List ℕ):
  ∃ c : Nat, (reverseT xs).time ≤ c * xs.length * xs.length := by
  use 1
  induction xs with
  | nil => grind [reverseT]
  | cons a as ih =>
    simp [reverseT]
    rw [appendT_time, reverseT_length]
    linarith

theorem reverseT_time_quadratic' (xs : List ℕ):
  ∃ c, (reverseT xs).time ≤ c * xs.length * xs.length := by
  induction xs with
  | nil => simp [reverseT]
  | cons a as ih =>
    simp [reverseT]
    rw [appendT_time, reverseT_length]
    obtain ⟨b, bh⟩ := ih
    use (b + 2)
    grw [bh]
    grind only


-- ============================================================================
-- EXERCISE 3: Tail-recursive reverse with accumulator
-- ============================================================================
-- Implement a tail-recursive reverse using an accumulator
-- Each step should cost 1 time unit
-- Expected time complexity: n (linear, much better than reverseT!)


def reverseTailT : List ℕ → List ℕ → TimeM (List ℕ)
| [], acc => ✓ acc, 0
| x :: xs, acc => do
  let s ← ✓ (x :: acc)
  reverseTailT xs s

def reverseTail : List ℕ → List ℕ → List ℕ
| [], acc => acc
| x :: xs, acc => reverseTail xs (x :: acc)

-- TODO: Prove correctness
theorem reverseTailT_correctness (xs acc : List ℕ):
  (reverseTailT xs acc).ret = reverseTail xs acc := by
  induction' xs with a as ih generalizing acc
  . simp [reverseTailT, reverseTail]
  . simp [reverseTailT, reverseTail, ih]

-- TODO: Prove linear time complexity
theorem reverseTailT_time (xs acc : List ℕ):
  (reverseTailT xs acc).time = xs.length := by
  induction xs generalizing acc with
  | nil => simp [reverseTailT]
  | cons a as ih =>
    simp [reverseTailT, ih]
    linarith
