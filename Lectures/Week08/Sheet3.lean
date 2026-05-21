/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Lectures.Week08.Sheet2
import Lectures.Week08.API

-- Running Time Analysis

set_option autoImplicit false
set_option tactic.hygienic false

-- The following helper lemmas are useful

@[simp] theorem merge_time (xs ys : List ℕ) :
  (merge xs ys).time = xs.length + ys.length := by
  induction' xs with a as ih₁ generalizing ys
  . simp [merge,merge.go]
  . simp [merge]
    induction' ys with b bs ih₂
    . simp [merge.go]
    . by_cases h : a ≤ b
      . simp [merge.go, h]
        specialize ih₁ (b :: bs)
        grind [merge]
      . simp [merge.go, h]
        grind

@[simp] theorem merge_ret_length_eq_sum (xs ys : List ℕ) :
  (merge xs ys).ret.length = xs.length + ys.length := by
 match  xs, ys with
 | [], x => simp [merge, merge.go]
 | xs, [] =>
   unfold merge merge.go
   aesop -- why `grind` does not solve it?
 | a :: as, b :: bs =>
   simp +arith +decide only [List.length_cons, merge, merge.go]
   split_ifs
   · simp
     rw [← merge]
     apply merge_ret_length_eq_sum
   · simp
     rw [← merge]
     -- rw [merge_ret_length_eq_sum]
     -- simp ; linarith
     -- it looks like tail recursive of the theorem is relevant here?
     rw [Nat.add_assoc, Nat.add_comm _ 1, ← Nat.add_assoc]
     apply merge_ret_length_eq_sum

@[simp] theorem mergeSort_same_length (xs : List ℕ) :
  (mergeSort xs).ret.length = xs.length:= by
  unfold mergeSort
  split
  next h =>
   simp
  next h =>
   simp
   repeat rw [mergeSort_same_length]
   grind only [= List.length_drop, = List.length_take, = min_def]


-- Next, we pave our way towards proving O(n log n) running time of merge sort.

def MS_REC : ℕ → ℕ
| 0 => 0
| 1 => 0
| n@(_x + 2) =>
  MS_REC (n / 2) + MS_REC ((n - 1)/2 + 1) + n

#eval mergeSort [4,1,3,4,5,6]
#eval MS_REC 10

theorem mergeSort_time_eq_MS_REC (xs : List ℕ) :
  (mergeSort xs).time = MS_REC xs.length := by
  fun_induction mergeSort
  · simp only [TimeM.tick]
    unfold MS_REC
    grind
  · simp only [bind, TimeM.time_of_bind, merge_time, mergeSort_same_length]
    unfold MS_REC
    grind

def MS_REC_SIMP : ℕ → ℕ
| 0 => 0
| 1 => 0
| n@(_x + 1) =>
  2 * MS_REC_SIMP (n / 2) + n


theorem MS_REC_SIMP_EQ (n : ℕ)
  : (MS_REC (2^n)) = (MS_REC_SIMP (2^n))  := by
  induction' n  with n ih
  · unfold MS_REC_SIMP MS_REC
    rfl
  · unfold MS_REC_SIMP MS_REC
    grind

theorem MS_REC_SIMP_EQ_CLOSED (n : ℕ) : MS_REC_SIMP (2^n) = 2^n * n := by
  induction' n with n ih
  all_goals unfold MS_REC_SIMP ; grind


-- The time is written assuming the length of the list is a power of two (for simplicity).
theorem MStimeBound (xs : List ℕ) (h : ∃ k, xs.length = 2 ^ k) :
  (mergeSort xs).time = xs.length * (Nat.log 2 xs.length)  := by
  rw [mergeSort_time_eq_MS_REC]
  obtain ⟨k,hk⟩ := h
  rw [hk,MS_REC_SIMP_EQ,MS_REC_SIMP_EQ_CLOSED]
  simp only [Nat.lt_add_one, Nat.log_pow]
