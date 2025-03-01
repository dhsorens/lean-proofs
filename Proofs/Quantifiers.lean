-- Prove these equivalences:

section equiv

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro h
    constructor <;> intro x
    . exact (h x).left
    . exact (h x).right
  . intro h
    cases h with | intro hp hq =>
    intro x
    constructor
    . exact hp x
    . exact hq x

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h hp x; exact (h x) (hp x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  cases h with
  | inl h =>
    apply Or.inl; exact (h x)
  | inr h =>
    apply Or.inr; exact (h x)

end equiv

-- [x] You should also try to understand why the reverse implication is not derivable in the last example.

/-
It is often possible to bring a component of a formula outside a universal quantifier, when it does not depend on the quantified variable. Try proving these (one direction of the second of these requires classical logic):
-/

section universals

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro a
  constructor
  . intro h_imp; exact (h_imp a)
  . intro h_r _; exact h_r

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  . intro h
    by_cases hr : r
    . apply Or.inr; exact hr
    . apply Or.inl
      intro x
      have h := h x
      cases h with
      | inl h => exact h
      | inr h => contradiction
  . intro h
    cases h with
    | inl h =>
      intro x ; apply Or.inl; exact h x
    | inr h =>
      intro x ; apply Or.inr ; exact h

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  . intro h hr x; exact h x hr
  . intro h x hr; exact h hr x

end universals

section existentials

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := by
  intro h; cases h with | intro x h => exact h

example (a : α) : r → (∃ x : α, r) := by
  intro h ; exists a

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  . intro h
    cases h with | intro x h =>
    constructor
    . exists x
      cases h with | intro hp hr =>
      exact hp
    . cases h with | intro hp hr => exact hr
  . intro h ; cases h with | intro hp hr =>
    cases hp with | intro x hp =>
    exists x

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  . intro h
    cases h with | intro x h_or =>
    cases h_or with
    | inl h =>
      apply Or.inl ; exists x
    | inr h =>
      apply Or.inr ; exists x
  . intro h
    cases h with
    | inl h =>
      cases h with | intro x h =>
      exists x ; apply Or.inl ; exact h
    | inr h =>
      cases h with | intro x h =>
      exists x ; apply Or.inr ; exact h

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  . intro h
    intro ⟨x, hx⟩
    exact hx (h x)
  . intro h x
    -- classical logic time
    by_cases h_c : (p x) ; exact h_c
    have h_x : ∃ x, ¬ p x := by exists x
    contradiction

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor
  . intro ⟨x, hx⟩
    intro h_all
    exact h_all x hx
  . intro h
    -- todo
    sorry

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry


end existentials

/-
Consider the "barber paradox," that is, the claim that in a certain town there is a (male) barber that shaves all and only the men who do not shave themselves. Prove that this is a contradiction:
-/

section barber

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have hb := h barber; clear h
  cases hb with | intro hl hr =>
  by_cases h_shaves : (shaves barber barber)
  . have _ := hl h_shaves
    contradiction
  . have _ := hr h_shaves
    contradiction

end barber

/-
Remember that, without any parameters, an expression of type Prop is just an assertion. Fill in the definitions of prime and Fermat_prime below, and construct each of the given assertions. For example, you can say that there are infinitely many primes by asserting that for every natural number n, there is a prime number greater than n. Goldbach's weak conjecture states that every odd number greater than 5 is the sum of three primes. Look up the definition of a Fermat prime or any of the other statements, if necessary.
-/

section parity

def even (n : Nat) : Prop := n % 2 = 0
def odd (n : Nat) : Prop := n % 2 = 1

def even2 (n : Nat) : Prop := ¬ odd n
def odd2 (n : Nat) : Prop := ¬ (even n)

example : ∀ n, odd n ↔ odd2 n := sorry
example : ∀ n, even n ↔ even2 n := sorry

-- definitions


-- even
example : even 2 := by
  unfold even ; simp
  -- apply Nat.mod_eq_zero_of_dvd
  -- exact (Nat.dvd_refl 2)

example : ∀ n m, even n → even m → even (n + m) := by
  intro n m hn hm
  unfold even at *
  rw [Nat.add_mod, hn, hm]

example : ∀ n m, even n → even m → even (n * m) := by
  intro n m hn hm
  unfold even at *
  rw [Nat.mul_mod, hm, hn]


end parity



def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := sorry
