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
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
    (fun h : (p ∨ q) ∨ r =>
      Or.elim h
      (fun hpq : p ∨ q =>
        (Or.elim hpq
          (fun hp : p =>
            show p ∨ (q ∨ r) from Or.intro_left (q ∨ r) hp)
          (fun hq : q =>
            have hqr : q ∨ r := Or.intro_left r hq
            show p ∨ (q ∨ r) from Or.intro_right p hqr)))
      (fun hr : r =>
        have hqr : q ∨ r := Or.intro_right q hr
        show p ∨ (q ∨ r) from Or.intro_right p hqr))
    (fun h : p ∨ (q ∨ r) =>
      Or.elim h
      (fun hp : p =>
        have hpq : p ∨ q := Or.intro_left q hp
        show (p ∨ q) ∨ r from Or.intro_left r hpq)
      (fun hqr : q ∨ r =>
        Or.elim hqr
          (fun hq : q =>
            have hpq : p ∨ q := Or.intro_right p hq
            show (p ∨ q) ∨ r from Or.intro_left r hpq)
          (fun hr : r =>
            show (p ∨ q) ∨ r from Or.intro_right (p ∨ q) hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
  Iff.intro
    (fun hpqr : p ∧ (q ∨ r) =>
      have hp := hpqr.left
      have hqr := hpqr.right
      Or.elim hqr
        (fun hq : q =>
          Or.intro_left (p ∧ r) (And.intro hp hq))
        (fun hr : r =>
          Or.intro_right (p ∧ q) (And.intro hp hr)))
    (fun hpqpr : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim hpqpr
        (fun hpq : p ∧ q =>
          have hp := hpq.left
          have hq := hpq.right
          have hqr : q ∨ r := Or.inl hq
          And.intro hp hqr)
        (fun hpr : p ∧ r =>
          have hp := hpr.left
          have hqr := Or.inr hpr.right
          And.intro hp hqr))
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
  Iff.intro
   (fun hpqr : p ∨ (q ∧ r) =>
     Or.elim hpqr
      (fun hp : p =>
        have hpq : p ∨ q := Or.inl hp
        have hpr : p ∨ r := Or.inl hp
        ⟨hpq, hpr⟩)
      (fun hqr : q ∧ r =>
        have hq : q := hqr.left
        have hr : r := hqr.right
        have hpq : p ∨ q := Or.inr hq
        have hpr : p ∨ r := Or.inr hr
        ⟨hpq, hpr⟩))
    (fun hpqpr : (p ∨ q) ∧ (p ∨ r) =>
      have hpq : p ∨ q := hpqpr.left
      have hpr : p ∨ r := hpqpr.right
      Or.elim hpq
       (fun hp : p =>
        Or.inl hp)
       (fun hq : q =>
        Or.elim hpr
          (fun hp : p =>
            Or.inl hp)
          (fun hr : r =>
            have hqr : q ∧ r := ⟨hq, hr⟩
            Or.inr hqr)))

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := 
  Iff.intro
   (fun hpqr : p → (q → r) =>
     fun hpq : p ∧ q =>
       have hqr : q → r := hpqr hpq.left
       hqr hpq.right)
    (fun hpqr : p ∧ q → r =>
      fun hp : p =>
        fun hq : q =>
          hpqr ⟨hp,hq⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun hpqr : (p ∨ q) → r =>
      And.intro
       (fun hp : p =>
        hpqr (Or.inl hp))
       (fun hq : q =>
        hpqr (Or.inr hq)))
    (fun hprqr : (p → r) ∧ (q → r) =>
      fun hpq : p ∨ q =>
        Or.elim hpq
          (fun hp : p =>
            hprqr.left hp)
          (fun hq : q =>
            hprqr.right hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
  Iff.intro
    (fun hnpq : ¬(p ∨ q) =>
      And.intro
        (fun hp : p =>
          absurd (Or.inl hp) hnpq)
        (fun hq : q =>
          absurd (Or.inr hq) hnpq))
    (fun hnpnq : ¬p ∧ ¬q =>
      fun hpq : p ∨ q =>
        Or.elim hpq
        (fun hp : p =>
          absurd hp hnpnq.left)
        (fun hq : q =>
          absurd hq hnpnq.right))

example : ¬p ∨ ¬q → ¬(p ∧ q) := 
  fun hnpnq : ¬p ∨ ¬q =>
    Or.elim hnpnq
    (fun hnp : ¬p =>
      fun hpq : p ∧ q =>
        absurd hpq.left hnp)
    (fun hnq : ¬q =>
      fun hpq : p ∧ q =>
        absurd hpq.right hnq)

example : ¬(p ∧ ¬p) := 
  fun hpnp : p ∧ ¬p =>
    absurd hpnp.left hpnp.right

example : p ∧ ¬q → ¬(p → q) := 
  fun hpnq : p ∧ ¬q =>
    have hp : p := hpnq.left
    have hnq : ¬q := hpnq.right
    fun hpq : p → q =>
      absurd (hpq hp) hnq

example : ¬p → (p → q) :=
  fun hnp : ¬p =>
    fun hp : p =>
      absurd hp hnp

example : (¬p ∨ q) → (p → q) :=
  fun hnpq : ¬p ∨ q =>
    Or.elim hnpq
    (fun hnp : ¬p =>
      fun hp : p =>
        absurd hp hnp)
    (fun hq : q =>
      fun _ =>
        hq)

example : p ∨ False ↔ p :=
  Iff.intro
    (fun hpf : p ∨ False =>
      Or.elim hpf
      (fun hp : p =>
        hp)
      (fun h: False =>
          h.elim))
    (fun hp : p =>
      Or.inl hp)

example : p ∧ False ↔ False :=
  Iff.intro
    (fun hpf : p ∧ False =>
      hpf.right.elim)
    (fun hf : False =>
      hf.elim)

example : (p → q) → (¬q → ¬p) :=
  fun hpq : p → q =>
    fun hnq : ¬q =>
      fun hp : p =>
        absurd (hpq hp) hnq

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := 
  fun hpqor : p → q ∨ r =>
    byCases
      (fun hp : p =>
        have hqr : q ∨ r := hpqor hp
        Or.elim hqr
          (fun hq : q => Or.inl (fun _ => hq))
          (fun hr : r => Or.inr (fun _ => hr)))
      (fun hnp : ¬p => Or.inl (fun hp : p => absurd hp hnp))
    
example : ¬(p ∧ q) → ¬p ∨ ¬q := 
  fun hnpq : ¬(p ∧ q) =>
    Or.elim (em p)
      (fun hp : p =>
        Or.elim (em q)
          (fun hq : q => absurd ⟨hp, hq⟩ hnpq)
          (fun hnq : ¬q => Or.inr hnq))
      (fun hnp : ¬p => Or.inl hnp)
        
example : ¬(p → q) → p ∧ ¬q := 
  fun hnpq : ¬(p → q) =>
    Or.elim (em p)
      (fun hp : p =>
        Or.elim (em q)
          (fun hq : q => absurd (fun _ => hq) hnpq)
          (fun hnq : ¬q => ⟨hp, hnq⟩))
      (fun hnp : ¬p =>
        have hpq : p → q := fun hp : p => absurd hp hnp
        absurd hpq hnpq)

example : (p → q) → (¬p ∨ q) := 
  fun hpq : p → q =>
    Or.elim (em p)
      (fun hp : p =>
        have hq : q := hpq hp
        Or.inr hq)
      (fun hnp : ¬p => Or.inl hnp)

example : (¬q → ¬p) → (p → q) := 
  fun hnqnp : ¬q → ¬p =>
    Or.elim (em q)
      (fun hq : q =>
        fun _ => hq)
      (fun hnq : ¬q =>
        have hnp : ¬p := hnqnp hnq
        fun hp : p => absurd hp hnp)

example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
