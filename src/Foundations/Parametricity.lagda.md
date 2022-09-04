```agda
open import 1Lab.Prelude

module Foundations.Parametricity (ℓ) where
```

# Parametricity

its simple

```agda
constant : ∀{m n} → (A : Type m) → (B : Type n) → B → A → B
constant A B b _ = b

all-functions-constant : ∀{m n} → Type m → Type n → Type _
all-functions-constant A B = is-equiv (constant A B)

Parametric : Type (lsuc ℓ)
Parametric = (T : Type ℓ) → all-functions-constant (Type ℓ) T
```
