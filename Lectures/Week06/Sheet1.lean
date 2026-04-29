/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Lectures.Week06.API

set_option autoImplicit false
set_option tactic.hygienic false

-- Divid-and-Conquer + Functional Induction

-- In the recursive algorithms, we always break the problem P(n) into
-- subproblems P(n₁) + P(n₂) of smaller instances The correctness proof is
-- typically based on induction from the smaller instances building up to the
-- larger instance In this lecture, we are going to see how functional induction
-- formalizes this idea

-- Today, we are going to see two examples
-- 1. MergeSort
-- 2. Binary Search

-- The object of this lecture is to formulate the correct intermediate
-- hypothesis so that the functional induction goes through.

-- Merge sort
-- let's use the following version of merge

def Merge: List ℕ → List ℕ → List ℕ
  | xs, [] => xs
  | [], xs => xs
  | x :: xs, y :: ys =>
    if x ≤ y then x :: Merge xs (y :: ys)
    else y :: Merge (x :: xs) ys

#check Merge

def list1 := [1,2,10]
def list2 := [3,5,20]

#eval Merge list1 list2

-- Define split list into two halves List.take -- Extracts the first n elements
-- of xs, or the whole list if n is greater than xs.length. List.drop -- Removes
-- the first n elements of the list xs. Returns the empty list if n is greater
-- than the length of the list.

-- Merge sort
def MergeSort (xs : List ℕ) : List ℕ  :=
 if xs.length < 2 then xs
 else
  let mid := xs.length / 2
  let l1 := xs.take mid
  let l2 := xs.drop mid
  let l1' := MergeSort l1
  let l2' := MergeSort l2
  Merge l1' l2'

-- Let's assume sorted_merge for now; we will prove sorted_merge in the next
-- sheet
theorem sorted_merge (l1 l2 : List ℕ) (hxs: Sorted l1) (hys: Sorted l2)
 : Sorted (Merge l1 l2) := by
 sorry

#check MergeSort.induct

-- Exercise 1.1: use sorted_merge theorem to prove that MergeSort outputs a
-- sorted list
theorem MS_Sorted (xs : List ℕ) : Sorted (MergeSort xs) := by
  induction xs using MergeSort.induct
  . simp [MergeSort, h]
    cases x
    . exact Sorted.nil
    . simp at h
      rw [h]
      exact Sorted.single head
  . rw [MergeSort]; simp [h]
    exact sorted_merge _ _ ih2 ih1
