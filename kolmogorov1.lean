-- Note: see tweet https://twitter.com/dwrensha/status/1475207151534710790?s=20
-- This now contains the fix.

import tactic
import data.int.basic
import data.nat.basic
import data.stream.init
import tactic.binder_matching

open classical

-- https://github.com/leanprover-community/mathlib/blob/master/test/coinductive.lean
-- https://leanprover-community.github.io/mathlib_docs/data/stream/init.
-- https://leanprover-community.github.io/mathlib_docs/tactics.html

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
  tautology!,
end

def breakable (a : String)
              (prop : ℕ → ℕ → String → Prop) : Prop
              := ∃ (P : ℕ → Prop),
                 ∃ (n : ℕ),
                 (∃ (i : ℕ), (P i)) ∧
                  ∀ (i : ℕ), (P i) → ∃ (j : ℕ), i < j ∧ prop i j a ∧ P j

theorem kolmogorov : breakable a decent ∨ breakable a indecent :=
begin
  by_cases h : ∃ (n : ℕ), ∀ (i : ℕ), n < i → ¬ prefix_decent i a,
    cases h with n h1,
    -- Suppose we have h
      right,
        unfold breakable,
        let P : ℕ → Prop, intro i, exact n < i,
        existsi [P, n],
          split, 
            apply exists.intro, simp [P],
            apply nat.lt_succ_iff.mpr, trivial,

            simp_intros i hj [P],
              have : n < i, finish,
              have h1 : ∃ (x : ℕ), ¬(i < x → decent i x a),
                apply not_forall.mp, tautology!,
              cases h1 with j h6,
                have : i < j, finish,
                existsi j,
                  split,
                    assumption,
                    split, tautology, linarith,

      -- Suppose not...
      left,
        unfold breakable,
          -- The property Q i says we can start a new decent word at position i
          let Q : ℕ → Prop := λ i, 0 < i ∧ prefix_decent i a,
          existsi [Q, 0],
            -- We can start the ball rolling at i
            have q : ∃ (i : ℕ), ¬(0 < i → ¬prefix_decent i a),
              from not_forall.mp (forall_not_of_not_exists h 0),
            cases q with i m11,
              split, finish,
                -- And now we need to keep the ball rolling
                intros i,
                  intro,
                    have k : ∃ (j : ℕ), ¬(i < j → ¬prefix_decent j a),
                      from not_forall.mp (forall_not_of_not_exists h i),
                    cases k with j h15,
                      existsi j, have : i < j, finish,
                        split,
                          assumption,                          
                          split,
                            tautology,
                            finish
end
