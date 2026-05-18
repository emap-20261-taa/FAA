/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Lectures.Week08.API

set_option autoImplicit false
set_option tactic.hygienic false

-- Analysis of merge sort
def merge (xs ys : List ℕ) : TimeM (List ℕ) :=
  let rec go : List ℕ → List ℕ → TimeM (List ℕ)
  | [], ys => ✓ ys, ys.length
  | xs, [] => ✓ xs, xs.length
  | x::xs', y::ys' => do
    if x ≤ y then
      let rest ← go xs' (y::ys')
      ✓ (x :: rest)
    else
      let rest ← go (x::xs') ys'
      ✓ (y :: rest)
  go xs ys

def mergeSort (xs : List ℕ) : TimeM (List ℕ) :=  do
  if xs.length < 2 then return xs
  else
    let half  := xs.length / 2
    let left  :=  xs.take half
    let right := xs.drop half
    let sortedLeft  ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight

-- # interpretation in each line

-- If the return type is a monad, say (`List ℕ`), then
-- `let sortedLeft ← mergeSort left`

-- This line means you can treat `sortedLeft` as type List ℕ and let notation
-- tell Lean to put `sortedLeft` into a box If the return type is not a monad,
-- you can use normal `let` with `:=` notation.


#check mergeSort
#eval merge [1,2,3,10] [4,5]
#eval mergeSort [4,2,3,1]

-- Correctness of Merge sort

@[simp,grind] def Nat.MinOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- inductive predicate
inductive Sorted: List ℕ  → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ) (t : List ℕ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a : ℕ) (t : List ℕ) : a.MinOfList t → Sorted t →  Sorted (a :: t)

theorem sorted_min {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs))
  : x.MinOfList xs := by
  cases hxs
  · simp
  · simp only [Nat.MinOfList, List.mem_cons, forall_eq_or_imp]
    constructor
    · exact a_1
    · apply sorted_min at a_2
      grind
  · exact a_1

theorem sorted_is_preserved_by_min_cons {a : ℕ} {t : List ℕ}
  (hmin : a.MinOfList t) (ht : Sorted t) : Sorted (a :: t) := by
  exact Sorted.cons_min a t hmin ht

theorem sorted_suffix {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs))
  : Sorted xs := by
  cases hxs
  . exact Sorted.nil
  . assumption
  . assumption


-- Exercise: Port your the proof of merge sort in the previous lectures into
-- this proof.

theorem mem_either_merge (xs ys : List ℕ) (z : ℕ)
  (hz : z ∈ (merge xs ys).ret) : z ∈ xs ∨ z ∈ ys := by
  induction' xs with a as ih generalizing ys
  . simp [merge, merge.go] at hz
    right
    assumption
  . simp [merge] at hz
    induction' ys with b bs ih₂
    . left
      simp [merge.go] at hz
      grind
    . by_cases h : a ≤ b
      . unfold merge.go at hz
        simp [h] at hz
        cases hz
        . grind
        . grind [merge]
      . unfold merge.go at hz
        simp [h] at hz
        cases hz
        . grind
        . grind


theorem min_all_merge (x : ℕ) (xs ys : List ℕ)
 (hxs : x.MinOfList xs) (hys : x.MinOfList ys)
 : x.MinOfList (merge xs ys).ret := by
 simp
 intro z hz
 have h : z ∈ xs ∨ z ∈ ys := by
   exact mem_either_merge xs ys z hz
 obtain h1 | h2 := h
 . exact hxs z h1
 . exact hys z h2


theorem sorted_merge {l1 l2 : List ℕ} (hxs : Sorted l1)
  (hys : Sorted l2) : Sorted ((merge l1 l2).ret) := by
  match l1,l2 with
  | [], xs =>
    simp [merge, merge.go]; assumption
  | xs, [] =>
    simp [merge]
    cases xs
    all_goals simp [merge.go]; assumption
  | x::xs, y::ys =>
    simp [merge, merge.go]
    split_ifs with h
    · apply Sorted.cons_min
      apply sorted_min at hxs
      apply sorted_min at hys
      · apply min_all_merge
        · grind
        · grind
      · apply sorted_merge
        · exact sorted_suffix hxs
        · exact hys
    · apply Sorted.cons_min
      apply sorted_min at hxs
      apply sorted_min at hys
      · apply min_all_merge
        · grind
        · grind
      · apply sorted_merge
        · exact hxs
        · exact sorted_suffix hys

-- Let's do this one as an example.
theorem MSMCorrect (xs : List ℕ)
  : Sorted (mergeSort xs).ret := by
  induction xs using mergeSort.induct
  . simp [mergeSort, h]
    cases x
    . exact Sorted.nil
    . simp at h
      rw [h]
      exact Sorted.single head
  . rw [mergeSort]; simp [h]
    exact sorted_merge ih2 ih1
