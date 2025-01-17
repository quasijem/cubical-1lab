```
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Type.Pi where
```

<!--
```
private variable
  ℓ ℓ₁ : Level
  A B C D : Type ℓ
  P Q : A → Type ℓ
```
-->

# Properties of Π types

This module contains properties of dependent function types, not necessarily
organised in any way.

## Closure under equivalences

Univalence automatically implies that every type former respects
equivalences. However, this theorem is limited to equivalences between
types _in the same universe_. Thus, there are functions to perturb the
codomain of a dependent function by an equivalence across universe levels:

```agda
Π-cod≃ : ((x : A) → P x ≃ Q x) → ((x : A) → P x) ≃ ((x : A) → Q x)
Π-cod≃ k .fst f x = k x .fst (f x)
Π-cod≃ k .snd .is-eqv f .centre .fst x   = equiv-centre (k x) (f x) .fst
Π-cod≃ k .snd .is-eqv f .centre .snd i x = equiv-centre (k x) (f x) .snd i
Π-cod≃ k .snd .is-eqv f .paths (g , p) i .fst x =
  equiv-path (k x) (f x) (g x , λ j → p j x) i .fst
Π-cod≃ k .snd .is-eqv f .paths (g , p) i .snd j x =
  equiv-path (k x) (f x) (g x , λ k → p k x) i .snd j

Π-dom≃ : (e : B ≃ A) → ((x : A) → P x) ≃ ((x : B) → P (e .fst x))
Π-dom≃ {P = P} e =
  Iso→Equiv λ where
    .fst k x → k (e .fst x)
    .snd .is-iso.inv k x → subst P (e.ε x) (k (e.from x))
    .snd .is-iso.rinv k → funext λ x →
        ap₂ (subst P) (sym (e.zig x))
          (sym (from-pathp (symP (ap k (e.η x)))))
      ∙ transport⁻transport (ap P (ap (e .fst) (sym (e.η x)))) (k x)
    .snd .is-iso.linv k → funext λ x →
      ap (subst P _) (sym (from-pathp (symP (ap k (e.ε x)))))
      ∙ transport⁻transport (sym (ap P (e.ε x))) _
  where module e = Equiv e

Π-impl-cod≃ : ((x : A) → P x ≃ Q x) → ({x : A} → P x) ≃ ({x : A} → Q x)
Π-impl-cod≃ k .fst f {x} = k x .fst (f {x})
Π-impl-cod≃ k .snd .is-eqv f .centre .fst {x}   = equiv-centre (k x) (f {x}) .fst
Π-impl-cod≃ k .snd .is-eqv f .centre .snd i {x} = equiv-centre (k x) (f {x}) .snd i
Π-impl-cod≃ k .snd .is-eqv f .paths (g , p) i .fst {x} =
  equiv-path (k x) (f {x}) (g {x} , λ j → p j {x}) i .fst
Π-impl-cod≃ k .snd .is-eqv f .paths (g , p) i .snd j {x} =
  equiv-path (k x) (f {x}) (g {x} , λ k → p k {x}) i .snd j
```

For non-dependent functions, we can easily perturb both domain and
codomain:

```agda
function≃ : (A ≃ B) → (C ≃ D) → (A → C) ≃ (B → D)
function≃ dom rng = Iso→Equiv the-iso where
  rng-iso = is-equiv→is-iso (rng .snd)
  dom-iso = is-equiv→is-iso (dom .snd)

  the-iso : Iso _ _
  the-iso .fst f x = rng .fst (f (dom-iso .is-iso.inv x))
  the-iso .snd .is-iso.inv f x = rng-iso .is-iso.inv (f (dom .fst x))
  the-iso .snd .is-iso.rinv f =
    funext λ x → rng-iso .is-iso.rinv _
               ∙ ap f (dom-iso .is-iso.rinv _)
  the-iso .snd .is-iso.linv f =
    funext λ x → rng-iso .is-iso.linv _
               ∙ ap f (dom-iso .is-iso.linv _)
```


## Dependent Funext

When the domain and codomain are simple types (rather than a higher
shape), paths in function spaces are characterised by `funext`{.Agda}.
We can generalise this to `funext-dep`, in which the domain and codomain
are allowed to be lines of types:

```agda
funextP
  : ∀ {A : Type ℓ} {B : A → I → Type ℓ₁}
  → {f : ∀ a → B a i0} {g : ∀ a → B a i1}
  → (∀ a → PathP (B a) (f a) (g a))
  → PathP (λ i → ∀ a → B a i) f g
funextP p i x = p x i

funext-dep
  : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
    {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}
  → ( {x₀ : A i0} {x₁ : A i1}
    → (p : PathP A x₀ x₁)
    → PathP (λ i → B i (p i)) (f x₀) (g x₁) )
  → PathP (λ i → (x : A i) → B i x) f g

funext-dep {A = A} {B} {f} {g} h i x =
  comp (λ k → B i (coei→i A i x k)) (∂ i) λ where
    k (i = i0) → f (coei→i A i0 x k)
    k (i = i1) → g (coei→i A i1 x k)
    k (k = i0) → h (λ j → coe A i j x) i
```

A very ugly cubical argument shows that this function is an equivalence:

```agda
funext-dep≃
  : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ₁}
    {f : (x : A i0) → B i0 x} {g : (x : A i1) → B i1 x}

  → ( {x₀ : A i0} {x₁ : A i1} (p : PathP A x₀ x₁)
    → PathP (λ i → B i (p i)) (f x₀) (g x₁)
    )
  ≃ PathP (λ i → (x : A i) → B i x) f g

funext-dep≃ {A = A} {B} {f} {g} = Iso→Equiv isom where
  open is-iso
  isom : Iso _ _
  isom .fst = funext-dep
  isom .snd .is-iso.inv q p i = q i (p i)

  isom .snd .rinv q m i x =
    comp (λ k → B i (coei→i A i x (k ∨ m))) (∂ i ∨ m) λ where
      k (k = i0) → q i (coei→i A i x m)
      k (i = i0) → f (coei→i A i0 x (k ∨ m))
      k (i = i1) → g (coei→i A i1 x (k ∨ m))
      k (m = i1) → q i x

  isom .snd .linv h m p i =
    comp (λ k → B i (lemi→i m k)) (∂ i ∨ m) λ where
      k (k = i0) → h (λ j → lemi→j j m) i
      k (i = i0) → f (lemi→i m k)
      k (i = i1) → g (lemi→i m k)
      k (m = i1) → h p i

    where
    lemi→j : ∀ j → coe A i j (p i) ≡ p j
    lemi→j j =
      coe (λ k → coe A i k (p i) ≡ p k) i j (coei→i A i (p i))

    lemi→i : Square (lemi→j i) (coei→i A i (p i)) refl refl
    lemi→i =
      sym (coei→i (λ k → coe A i k (p i) ≡ p k) i (coei→i A i (p i)))
      ◁ λ m k → lemi→j i (m ∨ k)

hetero-homotopy≃homotopy
  : {A : I → Type ℓ} {B : (i : I) → Type ℓ₁}
    {f : A i0 → B i0} {g : A i1 → B i1}

  → ({x₀ : A i0} {x₁ : A i1} → PathP A x₀ x₁ → PathP B (f x₀) (g x₁))
  ≃ ((x₀ : A i0) → PathP B (f x₀) (g (coe0→1 A x₀)))

hetero-homotopy≃homotopy {A = A} {B} {f} {g} = Iso→Equiv isom where
  open is-iso
  isom : Iso _ _
  isom .fst h x₀ = h (SinglP-is-contr A x₀ .centre .snd)
  isom .snd .inv k {x₀} {x₁} p =
    subst (λ fib → PathP B (f x₀) (g (fib .fst))) (SinglP-is-contr A x₀ .paths (x₁ , p)) (k x₀)

  isom .snd .rinv k = funext λ x₀ →
    ap (λ α → subst (λ fib → PathP B (f x₀) (g (fib .fst))) α (k x₀))
      (is-prop→is-set SinglP-is-prop (SinglP-is-contr A x₀ .centre) _
        (SinglP-is-contr A x₀ .paths (SinglP-is-contr A x₀ .centre))
        refl)
    ∙ transport-refl (k x₀)

  isom .snd .linv h j {x₀} {x₁} p =
    transp
      (λ i → PathP B (f x₀) (g (SinglP-is-contr A x₀ .paths (x₁ , p) (i ∨ j) .fst)))
      j
      (h (SinglP-is-contr A x₀ .paths (x₁ , p) j .snd))
```
