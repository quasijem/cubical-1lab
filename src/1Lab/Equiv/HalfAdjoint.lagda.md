```agda
open import 1Lab.HLevel.Retracts
open import 1Lab.Path.Groupoid
open import 1Lab.Equiv.Biinv
open import 1Lab.Univalence
open import 1Lab.HLevel
open import 1Lab.Equiv
open import 1Lab.Path
open import 1Lab.Type

module 1Lab.Equiv.HalfAdjoint where
```

# Adjoint Equivalences

An **adjoint equivalence** is an [isomorphism] $(f, g, \eta, \epsilon)$
where the [homotopies] ($\eta$, $\epsilon$) satisfy the [triangle
identities], thus witnessing $f$ and $g$ as [adjoint functors]. In
Homotopy Type Theory, we can use a _half_ adjoint equivalence -
satisfying only _one_ of the triangle identities - as a [good notion of
equivalence].

[isomorphism]: agda://1Lab.Equiv#isIso
[homotopies]: 1Lab.Path.html#dependent-functions
[triangle identities]: https://ncatlab.org/nlab/show/triangle+identities
[adjoint functors]: https://ncatlab.org/nlab/show/adjoint+functor
[good notion of equivalence]: 1Lab.Equiv.html#equivalences

```
isHAE : {ℓ₁ ℓ₂ : _} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) → Type _
isHAE {A = A} {B = B} f =
  Σ[ g ∈ (B → A) ]
  Σ[ η ∈ ((x : A) → g (f x) ≡ x) ]
  Σ[ ε ∈ ((y : B) → f (g y) ≡ y) ]
  ((x : A) → ap f (η x) ≡ ε (f x))
```

The argument is an adaptation of a standard result of both category
theory and homotopy theory - where we can "improve" an equivalence of
categories into an adjoint equivalence, or a homotopy equivalence into a
strong homotopy equivalence (Vogt's lemma). In HoTT, we show this
synthetically for equivalences between $\infty$-groupoids.

```
isIso→isHAE : {ℓ₁ ℓ₂ : _} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
            → isIso f → isHAE f
isIso→isHAE {A = A} {B} {f} iiso = g , η , ε' , λ x → sym (zig x) where
  open isIso iiso renaming (left-inverse to η ; right-inverse to ε)
```

For $g$ and $\eta$, we can just take the values provided by
`isIso`{.Agda}. However, if we want $(\eta, \epsilon)$ to satisfy the
triangle identities, we can not in general take $\epsilon' = \epsilon$.
We must perturb it slightly:

```
  ε' : (y : B) → f (g y) ≡ y
  ε' y = sym (ε (f (g y))) ∙ ap f (η (g y)) ∙ ε y
```

Now we can calculate that it satisfies the required triangle identity:

```
  zig : (x : A) → ε' (f x) ≡ ap f (η x)
  zig x =
    ε' (f x)                                      ≡⟨⟩
    sym (ε _) ∙ ap f (η (g (f x))) ∙ ε (f x)      ≡⟨ ap₂ _∙_ refl (ap₂ _∙_ (ap (ap f) (homotopy-invert η)) refl) ⟩
    sym (ε _) ∙ ap (f ∘ g ∘ f) (η x) ∙ ε (f x)    ≡⟨ ap₂ _∙_ refl (sym (homotopy-natural ε _)) ⟩
    sym (ε _) ∙ ε _ ∙ ap f (η x)                  ≡⟨ ∙-assoc _ _ _ ⟩
    (sym (ε _) ∙ ε _) ∙ ap f (η x)                ≡⟨ ap₂ _∙_ (∙-inv-l _) refl ⟩
    refl ∙ ap f (η x)                             ≡⟨ ∙-id-left _ ⟩
    ap f (η x)                                    ∎
```

The notion of `half-adjoint equivalence`{.Agda ident=isHAE} is a useful
stepping stone in writing a more comprehensible proof that `isomorphisms
are equivalences`{.Agda ident=Iso→Equiv}. Since this result is
fundamental, the proof we actually use is written with efficiency of
computation in mind - hence, cubically. The proof here is intended to be
more educational.

First, we give an equivalent characterisation of equality in
`fibre`{.Agda}s, which will be used in proving that `half adjoint
equivalences are equivalences`{.Agda ident=isHAE→isEquiv}.

```
fibre-paths : {ℓ₁ ℓ₂ : _} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B} {y : B}
            → {f1 f2 : fibre f y}
            → Path (fibre f y) f1 f2
            ≃ (Σ[ γ ∈ f1 .fst ≡ f2 .fst ] (ap f γ ∙ f2 .snd ≡ f1 .snd))
```

<details>
<summary>The proof of this is not very enlightening, but it's included
here (rather than being completely invisible) for
completeness:</summary>
```
fibre-paths {f = f} {y} {f1} {f2} =
  Path (fibre f y) f1 f2                                                       ≃⟨ Iso→Equiv Σ-Path-iso e¯¹ ⟩
  (Σ[ γ ∈ f1 .fst ≡ f2 .fst ] (subst (λ x₁ → f x₁ ≡ _) γ (f1 .snd) ≡ f2 .snd)) ≃⟨ Σ-ap (λ x → pathToEquiv (lemma x)) ⟩
  (Σ[ γ ∈ f1 .fst ≡ f2 .fst ] (ap f γ ∙ f2 .snd ≡ f1 .snd))                    ≃∎
  where
    helper : {p' : f (f1 .fst) ≡ y}
           → (subst (λ x → f x ≡ y) refl (f1 .snd) ≡ p')
           ≡ (ap f refl ∙ p' ≡ f1 .snd)
    helper {p'} =
      subst (λ x → f x ≡ y) refl (f1 .snd) ≡ p' ≡⟨ ap₂ _≡_ (transport-refl _) refl ⟩
      (f1 .snd) ≡ p'                            ≡⟨ Iso→path (sym , iso sym (λ x → refl) (λ x → refl)) ⟩
      p' ≡ f1 .snd                              ≡⟨ ap₂ _≡_ (sym (∙-id-left _)) refl ⟩
      refl ∙ p' ≡ f1 .snd                       ≡⟨⟩
      ap f refl ∙ p' ≡ f1 .snd                  ∎

    lemma : {x' : _} {p' : _} → (γ : f1 .fst ≡ x')
          → (subst (λ x → f x ≡ _) γ (f1 .snd) ≡ p')
          ≡ (ap f γ ∙ p' ≡ f1 .snd)
    lemma {x'} {p'} path =
      J (λ x' γ → {p' : _} → (subst (λ x → f x ≡ _) γ (f1 .snd) ≡ p')
                           ≡ (ap f γ ∙ p' ≡ f1 .snd))
        helper path {p' = p'}
```
</details>

Then, given an element $y : B$, we can construct a fibre of of $f$, and,
using the above characterisation of equality, prove that this fibre is a
centre of contraction:

```
isHAE→isEquiv : {ℓ₁ ℓ₂ : _} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
              → isHAE f → isEquiv f
isHAE→isEquiv {A = A} {B} {f} (g , η , ε , zig) .isEqv y = contr fib contract where
  fib : fibre f y
  fib = g y , ε y
```

The fibre is given by $(g(y), ε(y))$, which we can prove equal to another
$(x, p)$ using a very boring calculation:

```
  contract : (fib₂ : fibre f y) → fib ≡ fib₂
  contract (x , p) = (fibre-paths e¯¹) .fst (x≡gy , path) where
    x≡gy = ap g (sym p) ∙ η x

    path : ap f (ap g (sym p) ∙ η x) ∙ p ≡ ε y
    path =
      ap f (ap g (sym p) ∙ η x) ∙ p               ≡⟨ ap₂ _∙_ (ap-comp-path (ap g (sym p)) (η x)) refl ∙ sym (∙-assoc _ _ _) ⟩
      ap (f ∘ g) (sym p) ∙ ap f (η x) ∙ p         ≡⟨ ap₂ _∙_ refl (ap₂ _∙_ (zig _) refl) ⟩ -- by the triangle identity
      ap (f ∘ g) (sym p) ∙ ε (f x)    ∙ p         ≡⟨ ap₂ _∙_ refl (homotopy-natural ε p)  ⟩ -- by naturality of ε
```

The calculation of `path`{.Agda} factors as a bunch of boring
adjustments to paths using the groupoid structure of types, and the two
interesting steps above: The triangle identity says that
$\mathrm{ap}(f)(\eta x) = \epsilon(f x)$, and naturality of $\epsilon$
lets us "push it past $p$" to get something we can cancel:

```
      ap (f ∘ g) (sym p) ∙ ap (f ∘ g) p ∙ ε y     ≡⟨ ∙-assoc _ _ _ ⟩
      (ap (f ∘ g) (sym p) ∙ ap (f ∘ g) p) ∙ ε y   ≡⟨ ap₂ _∙_ (sym (ap-comp-path {f = f ∘ g} (sym p) p)) refl ⟩
      ap (f ∘ g) (sym p ∙ p) ∙ ε y                ≡⟨ ap₂ _∙_ (ap (ap (f ∘ g)) (∙-inv-r _)) refl ⟩
      ap (f ∘ g) refl ∙ ε y                       ≡⟨⟩
      refl ∙ ε y                                  ≡⟨ ∙-id-left (ε y) ⟩
      ε y                                         ∎
```

Putting these together, we get an alternative definition of
`isIso→isEquiv`{.Agda}:

```
isIso→isEquiv' : {ℓ₁ ℓ₂ : _} {A : Type ℓ₁} {B : Type ℓ₂} {f : A → B}
               → isIso f → isEquiv f
isIso→isEquiv' = isHAE→isEquiv ∘ isIso→isHAE
```

<!--
```
_ = isIso→isEquiv
```
-->