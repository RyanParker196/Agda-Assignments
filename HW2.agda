{-
Name: Ryan Parker
Date: 9/8/19

Collaboration & Resources Statement:
I discussed high level ideas about exercise 5 and 9 with Tyler Erlich
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

module HW2 where

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

  infixl 5 _∸_
  _∸_ : ℕ → ℕ → ℕ
  Z ∸ _ = Z
  m ∸ Z = m
  S m ∸ S n = m ∸ n

  -- FEEL FREE TO USE THESE IN THE ASSIGNMENT
  postulate
    assoc[+] : ∀ (m n p : ℕ) → m + (n + p) ≡ (m + n) + p
    runit[+] : ∀ (m : ℕ) → m + 0 ≡ m
    reduc[+] : ∀ (m n : ℕ) → m + S n ≡ S (m + n)
    commu[+] : ∀ (m n : ℕ) → m + n ≡ n + m
open Lib public

----------------
-- ASSIGNMENT --
----------------

-- E1: [★☆☆]
-- Define logical conjunction.
infixl 6 _⩓_
_⩓_ : 𝔹 → 𝔹 → 𝔹
True ⩓ True = True
False ⩓ True = False
True ⩓ False = False
False ⩓ False = False

-- test cases: these will check your work for you!
_ : True ⩓ True ≡ True
_ = ↯

_ : True ⩓ False ≡ False
_ = ↯

_ : False ⩓ True ≡ False
_ = ↯

_ : False ⩓ False ≡ False
_ = ↯

_ : False ⩓ False ≡ False
_ = ↯

-- E2: [★☆☆]
-- Define logical disjunction.
infixl 5 _⩔_
_⩔_ : 𝔹 → 𝔹 → 𝔹
True ⩔ True = True
True ⩔ False = True
False ⩔ True = True
False ⩔ False = False

-- test cases: these will check your work for you!
_ : True ⩔ True ≡ True
_ = ↯

_ : True ⩔ False ≡ True
_ = ↯

_ : False ⩔ True ≡ True
_ = ↯

_ : False ⩔ False ≡ False
_ = ↯


-- E3: [★☆☆]
-- Define exponentiation.
infixr 7 _^_
_^_ : ℕ → ℕ → ℕ
m ^ Z = 1
m ^ S n = (_^_ m n) × m

-- test cases: these will check your work for you!
_ : 2 ^ 4 ≡ 16
_ = ↯

_ : 2 ^ 5 ≡ 32
_ = ↯

_ : 2 ^ 6 ≡ 64
_ = ↯

-- E4: [★☆☆]
-- Prove a property involving both commutative and associativity facts
-- about addition.
-- HINT: use equational reasoning (not induction)
-- HINT: use lemmas `commu[+]` and `assoc[+]`
--assoc-swap[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ n + (m + p)
--assoc-swap[+] m n p rewrite commu[+] m n with assoc[+] n m p
--assoc-swap[+] m n p | IH rewrite IH = ↯


assoc-swap[+] : ∀ (m n p : ℕ) → (m + n) + p ≡ n + (m + p)
assoc-swap[+] m n p rewrite commu[+] m n | assoc[+] n m p = ↯
-- E5: [★★☆]
-- Prove that addition distributes through multiplication from the
-- right.
-- HINT: do induction on `m`
-- HINT: use `assoc[+]`
rdist[×] : ∀ (m n p : ℕ) → (m + n) × p ≡ m × p + n × p
rdist[×] Z n p = ↯
rdist[×] (S m) n p with rdist[×] m n p
… | IH rewrite IH | assoc[+] p (m × p) (n × p) = ↯
--rdist[×] (S m) n p | IH = {!rdist[×] m n p!}
--… | IH with rdist[×] m n p
--… | IH2 rewrite IH2 = {!!}

-- E6: [★★☆]
-- Prove that multiplication is associative.
-- HINT: do induction on `m`
-- HINT: use `rdist[×]`
assoc[×] : ∀ (m n p : ℕ) → (m × n) × p ≡ m × (n × p) 
assoc[×] Z n p = ↯
assoc[×] (S m) n p rewrite assoc[×] m n p | rdist[×] n (m × n) p | assoc[×] m n p = ↯
--assoc[×] (S m) n p with assoc[×] m n p
--… | IH rewrite IH with rdist[×] n (m × n) p
--… | IH2 rewrite IH2 | IH = ↯

-- E7: [★☆☆]
-- Prove that 0 is a right zero for multiplication.
-- HINT: do induction on `m`
rzero[×] : ∀ (m : ℕ) → m × 0 ≡ 0
rzero[×] Z = ↯
rzero[×] (S m) = rzero[×] m

-- E8: [★☆☆]
-- Prove that 1 is a right unit for multiplication.
-- HINT: do induction on `m`
runit[×] : ∀ (m : ℕ) → m × 1 ≡ m
runit[×] Z = ↯
runit[×] (S m) rewrite runit[×] m = ↯

--reduc[+] : ∀ (m n : ℕ) → m + S n ≡ S (m + n)
--(runit[×] m) × (runit[×] m)
-- (m * 1) == m
-- E9: [★★★]
-- Prove a fact about multiplication.
-- HINT: do induction on `m`
-- HINT: use `assoc[+]` and `commu[+]`
reduc[×] : ∀ (m n : ℕ) → m × S n ≡ m + m × n
reduc[×] Z n = ↯
reduc[×] (S m) n rewrite reduc[×] m n | assoc[+] n m (m × n) | assoc[+] m n (m × n) | commu[+] n m = ↯




-- E10: [★★☆]
-- Prove that multiplication is commutative
-- HINT: do induction on `m`
-- HINT: use `rzero[×]` and `reduc[×]`
commu[×] : ∀ (m n : ℕ) → m × n ≡ n × m
commu[×] m Z = rzero[×] m
commu[×] m (S n) rewrite reduc[×] m n | commu[×] m n = ↯

-- E11: [★★☆]
-- Prove a funny associativity property for “monus”
-- HINT: do induction on *both* `m` and `n`
assoc[∸] : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
assoc[∸] Z Z p = ↯
assoc[∸] Z (S n) p = ↯
assoc[∸] (S m) Z p = ↯
assoc[∸] (S m) (S n) p = assoc[∸] m n p
