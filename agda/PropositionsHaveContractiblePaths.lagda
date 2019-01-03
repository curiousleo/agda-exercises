We show that a given type A is a proposition iff for any two elements of A, the
type of paths between those elements is contractible.

That is, we show that the following are equivalent (expanded for concreteness).

isProp(A)                   ≡  Π (a b : A) (a = b)
Π (a b : A) isContr(a = b)  ≡  Π (a b : A) Σ (p : a = b) Π (q : a = b) (p = q)

We do this in a univalent setting, hence "without K".

\begin{code}

{-# OPTIONS --without-K #-}

module PropositionsHaveContractiblePaths where

\end{code}

Auxiliary definitions and lemmas
================================

Dependent pair
--------------

\begin{code}

record Σ {A : Set} (P : A → Set) : Set where
  constructor _,_
  field
    pr₁ : A
    pr₂ : P pr₁

\end{code}

Identity
--------

\begin{code}

data Id {A : Set} : A → A → Set where
  refl : (a : A) → Id a a

sym : {A : Set} {a b : A} → Id a b → Id b a
sym (refl a) = refl a

trans : {A : Set} {a b : A} → Id a b → {c : A} → Id b c → Id a c
trans (refl a) id-b-c = id-b-c

\end{code}

Paths
-----

\begin{code}

infixl 20 _∙_
_∙_ : {A : Set} {a b c : A} → Id b c → Id a b → Id a c
refl a ∙ refl .a = refl a

infix 30 _⁻¹
_⁻¹ : {A : Set} {a b : A} → Id a b → Id b a
refl a ⁻¹ = refl a

id-left-inv : {A : Set} {a b : A} (p : Id a b)
            → Id (p ∙ p ⁻¹) (refl b)
id-left-inv (refl a) = refl (refl a)

transport : {A : Set} {a b : A} → Id a b → {B : A → Set} → B a → B b
transport (refl a) ba = ba

\end{code}

Propositions, contractible types and sets
-----------------------------------------

\begin{code}

is-prop : Set → Set
is-prop A = (a b : A) → Id a b

is-contr : Set → Set
is-contr A = Σ {A} (λ a → (b : A) → Id a b)

is-set : Set → Set
is-set A = {a b : A} (p q : Id a b) → Id p q

\end{code}

Proof
=====

Part 1
------

If for any two elements of A, the type of paths between those elements is
contractible, then A is a proposition.

\begin{code}

proof₁ : {A : Set}
       → ((a b : A) → is-contr (Id a b))
       → ((a b : A) → Id a b)
proof₁ A-paths-are-contr a b = Σ.pr₁ (A-paths-are-contr a b)

\end{code}

Part 2
------

If A is a proposition, then for any two elements of A, the type of paths between
them is contractible.

To prove this, we first show that every mere proposition is a set.

\begin{code}

prop-is-set : {A : Set} → is-prop A → is-set A
prop-is-set {A} A-is-prop {a} = A-is-set
  where
    g : (b : A) → Id a b
    g = A-is-prop a

    h : {b c : A} (p : Id b c) → Id (g c ∙ (g b) ⁻¹) p
    h (refl b) = id-left-inv (g b)

    A-is-set : is-set A
    A-is-set p q = trans (sym (h p)) (h q)

proof₂ : {A : Set}
       → ((a b : A) → Id a b)
       → ((a b : A) → is-contr (Id a b))
proof₂ {A} A-is-prop a b = p , A-is-set p
  where
    p : Id a b
    p = A-is-prop a b

    A-is-set : is-set A
    A-is-set = prop-is-set A-is-prop

\end{code}
