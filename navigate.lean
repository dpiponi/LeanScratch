-- https://avigad.github.io/programming_in_lean/writing_tactics.html

--import tactic.find


open tactic
open tactic.interactive («have»)
open interactive (loc.ns)
open interactive.types (texpr location)
open interactive (parse)
open lean.parser (ident)


--#find (¬ _) → ¬ _

meta def tactic.interactive.mul_left (q : parse texpr)
  : parse location → tactic unit
| (loc.ns [some h]) := do
   e ← tactic.i_to_expr q,
   H ← get_local h,
   `(%%l = %%r) ← infer_type H,
   «have» h ``(%%e * %%l = %%e * %%r) ``(congr_arg (λ x, %%e*x) %%H),
   tactic.clear H
| _ := tactic.fail "mul_left takes exactly one location"

example (a b c : ℤ) (hyp : a = b) : c * a = c * b :=
begin
  mul_left c at hyp,
  exact hyp
end

theorem descend_and_left {a b c : Prop}
  : (a → b) → a ∧ c → b ∧ c :=
begin
  intro h,
  intro ac,
  apply and.intro,
  apply h,
  apply and.left ac,
  apply and.right ac,
end

theorem descend_or_left {a b c : Prop}
  : (a → b) → a ∨ c → b ∨ c :=
assume h,
  assume ac,
    or.elim ac
      (assume ha, or.inl (h ha))
      (assume hc, or.inr hc)

theorem descend_imp_left {a b c : Prop}
  : (a → b) → (b → c) → (a → c) :=
 assume f, assume g, g ∘ f

theorem descend_imp_right {a b c : Prop}
  : (a → b) → (c → a) → (c → b) :=
 assume f, assume g, f ∘ g
 --function.comp

theorem descend_or_right {a b c : Prop}
  : (a → b) → c ∨ a → c ∨ b :=
assume h,
  assume ac,
    or.elim ac
      (assume hc, or.inl hc)
      (assume ha, or.inr (h ha))

theorem descend_and_right {a b c : Prop}
  : (a → b) → c ∧ a → c ∧ b :=
begin
  intro h,
  intro ca,
  apply and.intro,
  apply and.left ca,
  apply h,
  apply and.right ca,
end

theorem descend_not {a b c : Prop}
  : (a → b) → ¬ b → ¬ a :=
begin
  intro h,
  intro nb,
  intro a,
  exact nb (h a)
end

example (a b c d e f : Prop) (hyp : b → a)
  : (a → c) → (b → c) :=
begin
  intro adc,
  apply descend_imp_left,
  swap,
  exact adc,
  apply hyp,  
end

example (a b c d e f : Prop) (hyp : a → b)
  : (c → a) → (c → b) :=
begin
  intro adc,
  apply descend_imp_right,
  swap,
  exact adc,
  apply hyp,  
end

meta mutual def dobinary, dounary, dozoom
with dobinary : expr → expr → expr → (name) → tactic name
| u l e thm :=
  unify u l >> (do
    applyc thm,
    swap,
    exact e,
    x <- mk_fresh_name, --get_unused_name "x",
    hx <- intro x,
    clear e,
    dozoom x hx)

with dounary : expr → (name) → tactic name
| e thm :=
  do
    applyc thm,
    swap,
    exact e,
    x <- mk_fresh_name, --get_unused_name "x",
    hx <- intro x,
    clear e,
    dozoom x hx

with dozoom : name → expr → tactic name | q1 e :=
  do
    t <- infer_type e >>= whnf,
    g <- tactic.target >>= whnf,
    match t with
    | `(%%u ∧ %%v) := do
        `(%%l ∧ %%r) ← tactic.target >>= whnf,
        dobinary u l e ``descend_and_right
      <|> dobinary v r e ``descend_and_left
      <|> return q1
    | `(%%u ∨ %%v) := do
        `(%%l ∨  %%r) ← tactic.target >>= whnf,
        dobinary u l e ``descend_or_right
      <|> dobinary v r e ``descend_or_left
      <|> return q1
    | `(%%u → %%v) := do
        `(%%l → %%r) ← tactic.target >>= whnf,
        dobinary u l e ``descend_imp_right
      <|> dobinary v r e ``descend_imp_left
      <|> return q1
| `(¬ %%u) := do
        `(¬ %%l) ← tactic.target >>= whnf,
        dounary e `descend_not
      <|> return q1
    | _ := return q1
    end

meta def tactic.interactive.zoom (q1 : parse ident) (q : parse texpr) : tactic unit := do
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
