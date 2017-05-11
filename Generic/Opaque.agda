module Generic.Opaque where

open import Prelude

-- * Opaque types

data Konst : Set where
  `ℕ `Bool `String : Konst

_≟Konst_ : ∀ (κ₁ κ₂ : Konst) → Dec (κ₁ ≡ κ₂)
`ℕ      ≟Konst `ℕ      = yes refl
`ℕ      ≟Konst `Bool   = no λ ()
`ℕ      ≟Konst `String = no λ ()
`Bool   ≟Konst `ℕ      = no λ ()
`Bool   ≟Konst `Bool   = yes refl
`Bool   ≟Konst `String = no λ ()
`String ≟Konst `String = yes refl
`String ≟Konst `ℕ      = no λ ()
`String ≟Konst `Bool   = no λ ()

⟦_⟧K : Konst → Set
⟦ `ℕ      ⟧K = ℕ
⟦ `Bool   ⟧K = Bool
⟦ `String ⟧K = String

_≟K_ :  ∀ {κ} → (k₁ k₂ : ⟦ κ ⟧K) → Dec (k₁ ≡ k₂)
_≟K_ {`ℕ}      n₁ n₂ = n₁ ≟N n₂
_≟K_ {`Bool}   b₁ b₂ = b₁ ≟B b₂
_≟K_ {`String} s₁ s₂ = s₁ ≟Str s₂ 

-- ** Differences over opaque types

TrivialK : Konst → Set
TrivialK κ = ⟦ κ ⟧K × ⟦ κ ⟧K

-- *** Application over opaque types

applyK : ∀{κ} → TrivialK κ → ⟦ κ ⟧K → Maybe ⟦ κ ⟧K
applyK {κ} (k₁ , k₂) k with k₁ ≟K k₂
... | yes _ = just k
... | no  _ with k₁ ≟K k
... | yes _ = just k₂
... | no ¬p = nothing

-- *** Cost of opaque diff

costK : ∀{κ} → TrivialK κ → ℕ
costK {κ} (k₁ , k₂) with k₁ ≟K k₂
... | yes _ = 0
... | no  _ = 2
