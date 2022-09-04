```agda
open import 1Lab.Prelude
open import Data.Nat

module Foundations.Base where
```

# Foundations

As outlined in the [**introduction to type theory**](1Lab.intro.html),
the 1Lab is based on cubical type theory, and not the classical
set-theoretic foundation called [ZFC]. This decision means that more
logical principles are available to us, such as [Univalence]. It also
means that some traditional logical principles, such as the Axiom of
Choice, need to be asserted before they can be used.

[ZFC]: https://en.wikipedia.org/wiki/Zermelo%E2%80%93Fraenkel_set_theory
[Univalence]: 1Lab.Univalence.html

This has a couple of major benefits. Unless we explicitly block it, all
terms that we can write in Agda should evaluate completely to produce an
output, which make it easier to write proofs. Additionally, it enables
the possibility of _synthetic mathematics_, where additional rules or
axioms are used to ensure our basic objects are the objects of study.
For example, cubical type theory is already a form of synthetic homotopy
theory, as its basic objects (types) behave in the same way as the basic
objects of homotopy theory.

# Classical axioms

TODO

```agda
is-choice : ∀ {ℓ'} → Type ℓ' → (ℓ : Level) → Type _ 
is-choice A ℓ = (F : A → Type ℓ) → ∥( (a : A) → F a )∥ → (a : A) → ∥ F a ∥

Countable-choice : (ℓ : Level) → Type _
Countable-choice = is-choice Nat

Excluded-middle : (ℓ : Level) → Type _
Excluded-middle ℓ = (A : Type ℓ) → is-prop A → Dec A

Dependent-choice : (ℓ : Level) → Type _
Dependent-choice ℓ = (P : Nat → Type ℓ)
                   → ∥ P 0 ∥
                   → ({n : Nat} → P n → ∥ P (suc n) ∥ )
                   → ∥( (n : Nat) → P n )∥
```

# Synthetic axioms

Synthetic axioms tend to be more complicated than classical axioms.
