variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := 
  Iff.intro
    (fun h: p ∧ q =>
      show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h: q ∧ p =>
      show p ∧ q from And.intro (And.right h) (And.left h))


example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h : p ∨ q =>
      Or.elim h
      (fun hp : p =>
        show q ∨ p from Or.intro_right q hp)
      (fun hq : q =>
        show q ∨ p from Or.intro_left p hq))
    (fun h : q ∨ p =>
      Or.elim h
      (fun hq : q =>
        show p ∨ q from Or.intro_right p hq)
      (fun hp : p =>
        show p ∨ q from Or.intro_left q hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h : (p ∧ q) ∧ r =>
      have hpq : p ∧ q := And.left h
      show p ∧ (q ∧ r) from And.intro (And.left hpq) (And.intro (And.right hpq) (And.right h)))
    (fun h : p ∧ (q ∧ r) =>
      have hqr : q ∧ r := And.right h
      show (p ∧ q) ∧ r from And.intro (And.intro (And.left h) (And.left hqr)) (And.right hqr))
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry
