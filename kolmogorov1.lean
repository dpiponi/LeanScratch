-- Note: see tweet https://twitter.com/dwrensha/status/1475207151534710790?s=20
-- This now contains the fix.

import tactic
import data.int.basic
import data.nat.basic
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
  tautology,
end

lemma lemma2 {a : Prop} {b : Prop} : ¬ (a → ¬b) → b :=
begin
  intro k,  
  by_contradiction,
  apply k,
  tautology,
end
#check nat.lt_succ_iff

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
        let P : ℕ → Prop := λ i, n < i,
        existsi [P, n],
        
          split,
            apply exists.intro,
              simp [P],

            apply nat.lt_succ_iff.mpr, trivial,

            simp_intros i hj [P],
              have h2 : n < i → ¬prefix_decent i a, from h1 i,
              have hj' : n < i := hj,
              cases not_forall.mp (h2 hj') with j h6,
                have h7 : ¬decent i j a, from and.right (lemma1 h6),
                have : i < j := lemma0 h6,
                existsi j,
                  split,
                    assumption,
                    split, assumption, linarith,

      -- Suppose not...
      left,
        unfold breakable,
        cases not_forall.mp (forall_not_of_not_exists h 0) with n h11,
          let Q : ℕ → Prop := λ i, n < i ∧ prefix_decent i a,
          existsi [Q, n],
            cases not_forall.mp (forall_not_of_not_exists h n) with i m11,

              split,
                have : prefix_decent i a, from lemma2 m11,
                existsi i, tautology,

                intros i,
                  intro hip,
                    cases not_forall.mp (forall_not_of_not_exists h i) with j h15,
                      existsi j,
                        have : prefix_decent j a := lemma2 h15,
                        have : i < j := lemma0 h15,

                        split,
                          assumption,                          
                          split,
                            tautology,
                            split, linarith, assumption,
end
