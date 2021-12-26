-- The proof has a bug! I think I have an update coming...

import tactic
import data.int.basic
import data.stream.init

open classical

-- https://github.com/leanprover-community/mathlib/blob/master/test/coinductive.lean
-- https://leanprover-community.github.io/mathlib_docs/data/stream/init.html

constant alphabet : Type
def String := ℕ → alphabet
constant a : String

-- States that substring [i, j) is decent
constant decent : ℕ → ℕ → String → Prop
def indecent (i j : ℕ) (a : String) : Prop := ¬ decent i j a

def prefix_decent (i : ℕ) (a : String) : Prop :=
  ∀ (j : ℕ), i < j → decent i j a

lemma lemma0 {a : Prop} {b : Prop} : ¬ (a → b) → a :=
begin
  intro k,
  by_contradiction,
  exact k (false.elim ∘ h),
end

lemma lemma1 {a : Prop} {b : Prop} : ¬ (a → b) → a ∧ ¬ b :=
begin
  intro k,
  split,
  
  exact lemma0 k,

  intro b,
  apply k,
  intro a,
  exact b,
end

lemma lemma2 {a : Prop} {b : Prop} : ¬ (a → ¬b) → b :=
begin
  intro k,  
  by_contradiction,
  apply k,
  intro a,
  exact h,
end

def breakable (a : String)
              (prop : ℕ → ℕ → String → Prop) : Prop
              := ∃ (P : ℕ → Prop),
                 ∃ (n : ℕ),
                 ∀ (i : ℕ), n < i → P i → ∃ (j : ℕ), i < j ∧ prop i j a ∧ P j

theorem kolmogorov : breakable a decent ∨ breakable a indecent :=
begin
  by_cases h : ∃ (n : ℕ), ∀ (i : ℕ), n < i → ¬ prefix_decent i a,

  cases h with n h1,
  right,
  rw breakable,
  let P : ℕ → Prop := λ i, true,
  existsi [P, n],
  intros i hj,
  simp [P],
  cases not_forall.mp (h1 i hj) with j h6,
  existsi j,
  exact lemma1 h6,

  -- Suppose not...
  left,
  rw breakable,
  let Q : ℕ → Prop := λ i, prefix_decent i a,
  existsi Q,
  cases not_forall.mp (forall_not_of_not_exists h 0) with n h11,
  existsi n,
  intros i hi hp,
  -- pick a j with prefix_decency
  cases not_forall.mp (forall_not_of_not_exists h i) with j h15,
  have h17 := lemma2 h15,
  existsi j,
  split,
  apply lemma0 h15,
  split,
  apply hp j,
  exact lemma0 h15,
  exact h17,
end
