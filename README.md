# LeanScratch
Messing with Lean

# Couple of things here. Nothing finished. Just scraps.

# navigate.lean

Implements a simple tactic `zoom`. If you're trying to prove goal `q` and have hypothesis `p`
then `zoom p x` does a simple structural "diff" from `p` to `q` and leaves you with the task
of proving the difference.

For example if your goal is `(¬ (e ∧ (a → f)) ∧ d) ∧ c`,
and you have hypothesis `¬ (e ∧ (b → f)) ∧ d) ∧ c → (¬ (e ∧ (a → f)) ∧ d) ∧ c`
it should be clear that you only need to prove `b → a` and that's what `zoom` leaves you with.
The first argument is the name you want for the new hypthesis that you'll be using.

Above example:

```lean
example (a b c d e f : Prop) (hyp : b → a) :
  (¬ (e ∧ (b → f)) ∧ d) ∧ c → (¬ (e ∧ (a → f)) ∧ d) ∧ c :=
begin
  intro hac,
  zoom z hac,
  apply hyp, assumption,
end
```



Work in progress.
Removed support for `a → b` because of the way `apply` treats `a → b → c`.
