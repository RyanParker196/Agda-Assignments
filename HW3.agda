{-
Name: Ryan Parker
Date: 9/12/19

Collaboration & Resources Statement:
did not collaborate
-}

---------------
-- LOGISTICS --
---------------

-- To submit the assignment, upload your solution to Gradescope as a
-- single .agda file.
--
-- Make sure you write your name, the date, and your collaboration
-- & Resources statement above, as indicated by the course 
-- collaboration and resources policy:
--
--     Collaboration on the high-level ideas and approach on assignments
--     is encouraged. Copying someone else's work is not allowed. Copying
--     solutions from an online source is not allowed. Any collaboration
--     or online resources, even if used only at a high level, must be
--     declared when you submit your assignment. Every assignment must
--     include a collaboration and resources statement. E.g., “I discussed
--     high-level strategies for solving problem 2 and 5 with Alex; I
--     found this stackoverflow post helpful while working on problem 3 ”
--     Students caught copying work are eligible for immediate failure of
--     the course and disciplinary action by the University. All academic
--     integrity misconduct will be treated according to UVM's Code of
--     Academic Integrity.
--
-- This assignment consists of a LIB section which contains relevant
-- definitions and lemmas which you should refer to throughout the
-- assignment, and an ASSIGNMENT section which contains definitions
-- and lemmas with “holes” in them. *If you only change the code
-- within the holes and your entire assignment compiles without
-- errors, you are guaranteed 100% on the assignment.*

module HW3 where

---------
-- LIB --
---------

module Lib where
  infix 4 _≡_

  data _≡_ {A : Set} (x : A) : A → Set where
    ↯ : x ≡ x

  {-# BUILTIN EQUALITY _≡_ #-}

  data 𝔹 : Set where
    True : 𝔹
    False : 𝔹

  data ℕ : Set where
    Z : ℕ
    S : ℕ → ℕ
  
  {-# BUILTIN NATURAL ℕ #-}
  
  infixl 5 _+_
  _+_ : ℕ → ℕ → ℕ
  Z    + n  =  n
  (S m) + n  =  S (m + n)

  infixl 6 _×_
  _×_ : ℕ → ℕ → ℕ
  Z × _ = Z
  S m × n = n + m × n

  infix 4 _≤_
  data _≤_ : ℕ → ℕ → Set where
    Z : ∀ {n} → Z ≤ n
    S : ∀ {m n} → m ≤ n → S m ≤ S n

  infix 4 _<_
  data _<_ : ℕ → ℕ → Set where
    Z : ∀ {n} → Z < S n
    S : ∀ {m n} → m < n → S m < S n

  -- USEFUL LEMMAS --
  infixl 6 _⊚[≤]_
  postulate
    _⊚[≤]_     : ∀ {m n p : ℕ} → n ≤ p → m ≤ n → m ≤ p
    lmono[+/≤] : ∀ (m n p : ℕ) → m ≤ n → m + p ≤ n + p
    rmono[+/≤] : ∀ (m n p : ℕ) → n ≤ p → m + n ≤ m + p
open Lib public

----------------
-- ASSIGNMENT --
----------------

-- E1: [★★☆]
-- Prove that × is monotonic on the right
-- Hint: do induction on m
-- Hint: use _⊚[≤]_, lmono[+/≤] and rmono[+/≤]
rmono[×/≤] : ∀ (m n p : ℕ) → n ≤ p → m × n ≤ m × p
rmono[×/≤] Z n p n≤p = Z
rmono[×/≤] (S m) n p n≤p with rmono[×/≤] m n p n≤p | lmono[+/≤] n p (m × n) n≤p | rmono[+/≤] p (m × n) (m × p)
… | IH | H1 | H2 = H2 IH ⊚[≤] H1

-- E2: [★☆☆]
-- Prove that < is transitive
-- Hint: do induction on m<n and case analysis on n<p
_⊚[<]_ : ∀ {m n p : ℕ} → n < p → m < n → m < p
S n<p ⊚[<] Z = Z
S n<p ⊚[<] S m<n = S (_⊚[<]_ n<p m<n)

-- E3: [★★★]
-- Prove that either m < n, m ≡ n, or m > n for all m and n

data trichotomy (m n : ℕ) : Set where
  [<] : m < n → trichotomy m n
  [≡] : m ≡ n → trichotomy m n
  [>] : n < m → trichotomy m n

-- Hint: do induction on both m and n
-- Hint: use a `with` pattern for the inductive hypothesis
total[<] : ∀ (m n : ℕ) → trichotomy m n
total[<] Z Z = [≡] ↯
total[<] Z (S n) = [<] Z
total[<] (S m) Z = [>] Z
total[<] (S m) (S n) with total[<] m n
… | [<] x = [<] (S x)
… | [>] x = [>] (S x)
… | [≡] ↯ = [≡] ↯


-- E4: [★★☆]
-- Prove that:
-- 1. `m ≤ n` and `m < S n` are isomorphic propositions
-- 2. `S m ≤ n` and `m < n` are isomorphic propositions

-- Hint: do induction on m≤n
isoto[≤/S<] : ∀ {m n : ℕ} → m ≤ n → m < S n 
isoto[≤/S<] Z = Z
isoto[≤/S<] (S m≤n) = S (isoto[≤/S<] m≤n)
--… | IH = S IH

-- Hint: use isoto[≤/S<]
isoto[S≤/<] : ∀ {m n : ℕ} → S m ≤ n → m < n
isoto[S≤/<] (S sm≤n) = isoto[≤/S<] sm≤n

-- Hint: do induction on m<n
isofr[S≤/<] : ∀ {m n : ℕ} → m < n → S m ≤ n 
isofr[S≤/<] Z = S Z
isofr[S≤/<] (S m<n) = S (isofr[S≤/<] m<n)

-- Hint: use isofr[S≤/<]
isofr[≤/S<] : ∀ {m n : ℕ} → m < S n → m ≤ n
isofr[≤/S<] Z = Z
isofr[≤/S<] (S m≤sn) = isofr[S≤/<] m≤sn

-- #E5: [★★☆]
-- Prove that odd plus odd is even

mutual 
  data even : ℕ → Set where
    Z : even Z
    S : ∀ {n}
      → odd n
      → even (S n)
  data odd : ℕ → Set where
    S : ∀ {n}
      → even n
      → odd (S n)
mutual
  -- Hint: do induction on om
  -- Hint: use e+o≡o
  o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
  o+o≡e (S x) on = S (e+o≡o x on)

  -- Hint: do induction on em
  -- Hint: use o+o≡e
  e+o≡o : ∀ {m n : ℕ} → even m → odd n → odd (m + n)
  e+o≡o Z on = on
  e+o≡o (S x) on = S (o+o≡e x on)

-- E6: [★★★]
-- Define an algorithm for less-than-or-equal and prove it correct
_≤?_ : ℕ → ℕ → 𝔹
Z ≤? Z = True
Z ≤? S n = True
S m ≤? Z = False
S m ≤? S n = m ≤? n

-- Tests --

_ : 0 ≤? 0 ≡ True
_ = ↯

_ : 1 ≤? 1 ≡ True
_ = ↯

_ : 0 ≤? 1 ≡ True
_ = ↯

_ : 2 ≤? 2 ≡ True
_ = ↯

_ : 1 ≤? 2 ≡ True
_ = ↯

_ : 0 ≤? 2 ≡ True
_ = ↯

_ : 4 ≤? 0 ≡ False
_ = ↯


-- HINT: do induction on m and n and case analysis on m≤?n
sound[≤?] : ∀ (m n : ℕ) → m ≤? n ≡ True → m ≤ n
sound[≤?] Z Z m≤?n = Z
sound[≤?] Z (S n) m≤?n = Z
sound[≤?] (S m) Z ()
sound[≤?] (S m) (S n) = λ x → S (sound[≤?] m n x)
-- HINT: do induction on m≤n
complete[≤?] : ∀ {m n : ℕ} → m ≤ n → m ≤? n ≡ True
complete[≤?] {n = Z} Z = ↯
complete[≤?] {n = S n} Z = ↯
complete[≤?] (S m≤n) = complete[≤?] m≤n

-- EXTRA PROBLEMS (not graded)
--
-- 1. define an algorithm for strict less-than (`_<?_ : ℕ → ℕ → 𝔹`) and prove it
--    correct (sound and complete)
-- 2. define an enumeration data type called `ord` with three
--     elements `LT`, `EQ` and `GT`. Define an algorithm which determines
--     the ordering between two numbers (`_⋚?_` : ℕ → ℕ → ord`) and prove
--     it correct (sound and complete)
-- 3. prove that `_<_` is irreflexive, transitive and asymmetric
-- 4. prove that `_≤?_ : ℕ → ℕ → 𝔹` is transitive without using any
--    other lemmas (so, directly by induction). transitive means that
--    if `x ≤? y ≡ True` and `y ≤? z ≡ True` then `x ≤? z ≡ True`
-- 5. prove that inequality composed with strict inequality gives a
--    strict inequality, so `x ≤ y` and `y < z` implies `x < z`, and
--    `x < y` and `y ≤ z` implies `x < z`
-- 6. prove that any two proofs of inequality are canonical, that is
--    if `ε₁ : x ≤ y` and `ε₂ : x ≤ y` then `ε₁ ≡ ε₂`

--E4
--_⊚[≤]_ : ∀ {m n p : ℕ}     → n ≤ p → m ≤ n → m ≤ p
e4 : ∀ (m n p : ℕ) → m ≤? n ≡ True → n ≤? p ≡ True → m ≤? p ≡ True
e4 Z Z Z m≤n n≤p = ↯
e4 Z Z (S p) m≤n n≤p = ↯
e4 Z (S n) Z m≤n n≤p = ↯
e4 Z (S n) (S p) m≤n n≤p = ↯
e4 (S m) Z Z m≤n n≤p = m≤n
e4 (S m) Z (S p) () ↯
e4 (S m) (S n) Z m≤n n≤p = n≤p
e4 (S m) (S n) (S p) m≤n n≤p = e4 m n p m≤n n≤p

e6 : ∀ {x y : ℕ} → (ε1 : x ≤ y) → (ε2 : x ≤ y) → ε1 ≡ ε2
e6 Z Z = ↯
e6 (S e1) e2 = {!!}
-- 6. prove that any two proofs of inequality are canonical, that is
--    if `ε₁ : x ≤ y` and `ε₂ : x ≤ y` then `ε₁ ≡ ε₂`
