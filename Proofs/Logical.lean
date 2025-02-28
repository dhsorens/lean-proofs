
variable (p q r : Prop)

-- Notes:
-- The order of operations is as follows: unary negation ¬ binds most strongly, then ∧, then ∨, then →, and finally ↔.

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  . intro h_and
    cases h_and with
    | intro left right =>
      trivial
  . intro h_and
    cases h_and with
    | intro left right =>
    trivial

example : p ∨ q ↔ q ∨ p := by
  constructor
  . intro h_or
    cases h_or with
    | inl hp =>
      exact (Or.inr hp)
    | inr hq =>
      exact (Or.inl hq)
  . intro h_or
    cases h_or with
    | inr hq =>
      exact (Or.inl hq)
    | inl hp =>
      exact (Or.inr hp)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  . intro h_andl
    cases h_andl with
    | intro andl andr =>
    cases andl with
    | intro andll andlr =>
    constructor; repeat trivial
  . intro h_and
    cases h_and with
    | intro andl andr =>
    cases andr with
    | intro andrl andrr =>
    constructor; repeat trivial

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  . intro h_or
    cases h_or with
    | inl h =>
      cases h with
      | inl h =>
        apply Or.inl; assumption
      | inr h =>
        apply Or.inr ∘ Or.inl; assumption
    | inr h =>
      repeat apply Or.inr
      assumption
  . intro h_or
    cases h_or with
    | inl h =>
      repeat apply Or.inl
      assumption
    | inr h =>
      cases h with
      | inl h =>
        apply Or.inl ∘ Or.inr; assumption
      | inr h =>
        apply Or.inr; assumption

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro h
    cases h with
    | intro hl hr =>
    cases hr with
    | inl hq =>
      apply Or.inl
      trivial
    | inr hp =>
      apply Or.inr
      trivial
  . intro h
    cases h with
    | inl hq =>
      cases hq with
      | intro hp hq =>
      constructor; trivial
      apply Or.inl; trivial
    | inr hr =>
      cases hr with
      | intro hp hr =>
      constructor; trivial
      apply Or.inr; trivial

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  . intro h
    cases h with
    | inl hp =>
      constructor <;> apply Or.inl <;> trivial
    | inr h =>
      cases h with
      | intro hq hr =>
      constructor <;> apply Or.inr <;> trivial
  . intro h
    cases h with
    | intro hq hr =>
    cases hq with
    | inl hp =>
      apply Or.inl; trivial
    | inr hq =>
      cases hr with
      | inl h =>
        apply Or.inl; trivial
      | inr h =>
        apply Or.inr
        constructor <;> trivial

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  . intro h_imp h
    cases h with
    | intro hp hq =>
    -- have h_imp' := h_imp hp
    apply (h_imp hp); trivial
  . intro h_imp hp hq
    apply h_imp
    constructor <;> trivial

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  . intro h_or
    constructor <;> intro h <;> apply h_or
    . apply Or.inl; trivial
    . apply Or.inr; trivial
  . intro h_and
    cases h_and with
    | intro hl hr =>
    intro h_or
    cases h_or with
    | inl hp => apply hl; trivial
    | inr hq => apply hr; trivial


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intro h_not
    constructor
    . intro hp
      apply h_not
      apply Or.inl
      exact hp
    . intro hq
      apply h_not
      apply Or.inr
      exact hq
  . intro h_and
    intro h_or
    cases h_and with
    | intro hnp hnq =>
    cases h_or with
    | inl hp => contradiction
    | inr hq => contradiction

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intro h_not
    constructor
    <;> intro h
    <;> apply h_not
    . apply Or.inl; exact h
    . apply Or.inr; exact h
  . intro h_and
    cases h_and with
    | intro hp hq =>
    intro h_or
    cases h_or with
    | inl h => apply hp; exact h
    | inr h => apply hq; exact h


example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h_or
  cases h_or with
  | inl h =>
    intro h_and
    cases h_and with
    | intro hp hq => apply h; exact hp
  | inr h =>
    intro h_and
    cases h_and with
    | intro hp hq => apply h; exact hq

example : ¬(p ∧ ¬p) := by
  intro h_and
  cases h_and with
  | intro hp h_pf => apply h_pf; exact hp

example : p ∧ ¬q → ¬(p → q) := by
  intro h_and h_imp
  cases h_and with
  | intro hp hqf =>
  apply hqf; clear hqf
  apply h_imp; clear h_imp
  exact hp

example : ¬p → (p → q) := by
  intro hpf hp
  have _ := (hpf hp) -- not strictly necessary
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro h_or hp
  cases h_or with
  | inl h => have _ := h hp; contradiction
  | inr h => exact h

example : p ∨ False ↔ p := by
  constructor
  . intro h
    cases h with
    | inl hp => exact hp
    | inr _ => contradiction
  . intro hp
    apply Or.inl; exact hp


example : p ∧ False ↔ False := by
  constructor
  . intro h
    cases h with | intro _ _ => contradiction
  . intro _ ; contradiction

example : (p → q) → (¬q → ¬p) := by
  intro h_imp hqf hp
  apply hqf ∘ h_imp; exact hp
