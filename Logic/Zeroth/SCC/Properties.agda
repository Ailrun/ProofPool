-- Properties of Sequent Calculus with Cut
module Logic.Zeroth.SCC.Properties where

open import Logic.Zeroth.Base
open import Logic.Zeroth.SCC

⟶₀-resp-∈⇒∈ : (∀ {A} → A ∈ Γ → A ∈ Γ′) → Γ ⟶₀ B → Γ′ ⟶₀ B
⟶₀-resp-∈⇒∈ f (init₀ B∈)         = init₀ (f B∈)
⟶₀-resp-∈⇒∈ f (⊥ₚ₀L  ⊥∈)         = ⊥ₚ₀L (f ⊥∈)
⟶₀-resp-∈⇒∈ f (∧ₚ₀R  ⟶B ⟶C)      = ∧ₚ₀R (⟶₀-resp-∈⇒∈ f ⟶B) (⟶₀-resp-∈⇒∈ f ⟶C)
⟶₀-resp-∈⇒∈ f (∧ₚ₀L₁ B∧C∈ B⟶)    = ∧ₚ₀L₁ (f B∧C∈) (⟶₀-resp-∈⇒∈ (∈⇒∈-ext f) B⟶)
⟶₀-resp-∈⇒∈ f (∧ₚ₀L₂ B∧C∈ C⟶)    = ∧ₚ₀L₂ (f B∧C∈) (⟶₀-resp-∈⇒∈ (∈⇒∈-ext f) C⟶)
⟶₀-resp-∈⇒∈ f (∨ₚ₀R₁ ⟶B)         = ∨ₚ₀R₁ (⟶₀-resp-∈⇒∈ f ⟶B)
⟶₀-resp-∈⇒∈ f (∨ₚ₀R₂ ⟶C)         = ∨ₚ₀R₂ (⟶₀-resp-∈⇒∈ f ⟶C)
⟶₀-resp-∈⇒∈ f (∨ₚ₀L  B∨C∈ B⟶ C⟶) = ∨ₚ₀L (f B∨C∈) (⟶₀-resp-∈⇒∈ (∈⇒∈-ext f) B⟶) (⟶₀-resp-∈⇒∈ (∈⇒∈-ext f) C⟶)
⟶₀-resp-∈⇒∈ f (→ₚ₀R  B⟶C)        = →ₚ₀R (⟶₀-resp-∈⇒∈ (∈⇒∈-ext f) B⟶C)
⟶₀-resp-∈⇒∈ f (→ₚ₀L  B→C∈ ⟶B C⟶) = →ₚ₀L (f B→C∈) (⟶₀-resp-∈⇒∈ f ⟶B) (⟶₀-resp-∈⇒∈ (∈⇒∈-ext f) C⟶)
⟶₀-resp-∈⇒∈ f (cut₀  ⟶B B⟶)      = cut₀ (⟶₀-resp-∈⇒∈ f ⟶B) (⟶₀-resp-∈⇒∈ (∈⇒∈-ext f) B⟶)

⟶₀wk : Γ′ ++ Γ ⟶₀ B → Γ′ ++ A ∷ Γ ⟶₀ B
⟶₀wk {Γ′} ⟶B = ⟶₀-resp-∈⇒∈ (∈-++-∷ Γ′ _) ⟶B

⟶₀wk′ : Γ′ ++ Γ ⟶₀ A → Γ′ ++ Γ″ ++ Γ ⟶₀ A
⟶₀wk′ {Γ′} ⟶A = ⟶₀-resp-∈⇒∈ (∈-++-++ Γ′ _) ⟶A

⟶₀ct : Γ′ ++ A ∷ A ∷ Γ ⟶₀ B → Γ′ ++ A ∷ Γ ⟶₀ B
⟶₀ct {Γ′} ⟶B = ⟶₀-resp-∈⇒∈ (∈-++-dedupe₁ Γ′) ⟶B

⟶₀ex : Γ′ ++ A ∷ B ∷ Γ ⟶₀ C → Γ′ ++ B ∷ A ∷ Γ ⟶₀ C
⟶₀ex {Γ′} ⟶C = ⟶₀-resp-∈⇒∈ (∈-++-swap Γ′) ⟶C
