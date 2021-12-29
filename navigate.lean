-- https://avigad.github.io/programming_in_lean/writing_tactics.html

import tactic.find

open tactic
open tactic.interactive («have»)
open interactive (loc.ns)
open interactive.types (texpr location)
open interactive (parse)
open lean.parser (ident)

theorem descend_imp_left {a b c : Prop}
  : (a → b) → (b → c) → (a → c) := assume f, assume g, g ∘ f
theorem descend_imp_right {a b c : Prop}
  : (a → b) → (c → a) → (c → b) := assume f, assume g, f ∘ g

/-
example (a b f g : Prop) (hyp : b → a) :
  (g → (f → b)) → (g → (f → a)) :=
begin
  intro hac,
  refine descend_imp_right _ hac,
  intro hac2,

  refine descend_imp_right _ hac2,
  intro,


  
  --assumption,
  --revert,
  sorry
end
-/

meta mutual def dobinary, dounary, dozoom
with dobinary : expr → expr → expr → name → tactic name
| u l e thm :=
  unify u l >> (do
    trace ("unified", u, l),
    trace ("thm", thm),
    trace "---",
    trace_state,
    trace "---",
    applyc thm,
    trace "===",
    trace_state,
    trace "===",
     swap, exact e,
    trace "ok",
    x <- mk_fresh_name, --get_unused_name "x",
    hx <- intro x,
    clear e,
    dozoom x hx)

with dounary : expr → name → tactic name
| e thm :=
  do
    applyc thm, swap, exact e,
    x <- mk_fresh_name, --get_unused_name "x",
    hx <- intro x,
    clear e,
    dozoom x hx

with dozoom : name → expr → tactic name | q1 e :=
  do
    t <- infer_type e >>= whnf,
    g <- tactic.target >>= whnf,
    trace ("doing a match on", t),
    match t with
    | `(%%u ∧ %%v) := do
        trace "and",
        `(%%l ∧ %%r) ← tactic.target >>= whnf,
        dobinary u l e `and.imp_right
      <|> dobinary v r e `and.imp_left
      <|> return q1
    | `(%%u ∨ %%v) := do
        trace "or",
        `(%%l ∨  %%r) ← tactic.target >>= whnf,
        dobinary u l e `or.imp_right
      <|> dobinary v r e `or.imp_left
      <|> return q1
    | `(%%u → %%v) := do
        trace ("imp", u, v, "=", g),
        `(%%l → %%r) ← tactic.target >>= whnf,
        trace ("got", l, r),
        trace ("gona unify", u, l),
        dobinary u l e `function.comp
      <|> dobinary v r e ``descend_imp_left
      <|> return q1
    | `(¬ %%u) := do
        trace "not",
        `(¬ %%l) ← tactic.target >>= whnf,
        dounary e `mt
      <|> return q1
    | _ := return q1
    end

meta def tactic.interactive.zoom (q1 : parse ident) (q : parse texpr)
  : tactic unit := do
  e ← tactic.i_to_expr q,
  n <- dozoom q1 e,
  when (q1 ≠ n) $ rename n q1

example (a b : Prop) (hyp : a → b) :
  a → b :=
begin
  intro hac,
  zoom z hac,
  apply hyp, assumption,
end

example (a b : Prop) (hyp : a → b) :
  ¬ b → ¬ a :=
begin
  intro hac,
  zoom z hac,
  apply hyp, assumption,
end

example (a b c : Prop) (hyp : a → b) :
  a ∨ c → b ∨ c :=
begin
  intro hac,
  zoom z hac,
  apply hyp, assumption,
end

example (a b c : Prop) (hyp : a → b) :
  a ∧ c → b ∧ c :=
begin
  intro hac,
  zoom z hac,
  apply hyp, assumption,
end

example (a b c : Prop) (hyp : a → b) :
  c ∧ a → c ∧ b :=
begin
  intro hac,
  zoom z hac,
  apply hyp, assumption,
end

example (a b c d e f : Prop) (hyp : b → a) :
  (¬ (e ∧ (b → f)) ∧ d) ∧ c → (¬ (e ∧ (a → f)) ∧ d) ∧ c :=
begin
  intro hac,
  zoom z hac,
  apply hyp, assumption,
end

example (a b : Prop) (hyp : a → b) :
  (∃ (i : ℕ), a) → ∃ (i : ℕ), b :=
begin
  intro hac,
  zoom z hac, -- does nothing
  cases hac with i p, existsi i, apply hyp, assumption
end

example (a b f g : Prop) (hyp : b → a) :
  (g → (b → f)) → (g → (a → f)) :=
begin
  intro hac,
  zoom z hac,
  apply hyp, assumption,
end
