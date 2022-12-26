{-# OPTIONS --without-K #-}

module types where

open import lists
open import syn

Ctx : ℕ → Set
Ctx = 𝐶𝑡𝑥 (𝒞Alg ℕ Ty zero λ {n} A → suc n)

Ren : {n m : ℕ} → Ctx n → Ctx m → Subset n m → Set
Ren = 𝑅𝑒𝑛 (ℛAlg Subset weakenTy done (λ A X → yes X) (λ A X → no X))

W₁Ren : {n m : ℕ} {G : Ctx n} {D : Ctx m} {X : Subset n m}
  {T : Ty n} → Ren G D X → Ren (G ⊹ T) D (no X)
W₁Ren {T = T} σ = no T σ

W₂Ren : {n m : ℕ} {G : Ctx n} {D : Ctx m} {X : Subset n m}
  {T : Ty m} → Ren G D X → Ren (G ⊹ weakenTy X T) (D ⊹ T) (yes X)
W₂Ren {T = T} σ = yes T σ

data Var : {n : ℕ} (G : Ctx n) (m : Subset n 1) (T : Ty n) → Set where
  𝑧𝑣 : {n : ℕ} {G : Ctx n} {T : Ty n} →
    Var (G ⊹ T) (yes all-no) (WTy T)
  𝑠𝑣 : {n : ℕ} {G : Ctx n} {T S : Ty n} {v : Subset n 1} →
    Var G v S → Var (G ⊹ T) (no v) (WTy S)

data VCtx : {n : ℕ} → Ctx n → Set
data VTms : {n m : ℕ} → Ctx n → Tms n m → Ctx m → Set
data VTy : {n : ℕ} → Ctx n → Ty n → Set
data VTm : {n : ℕ} → Ctx n → Tm n → Ty n → Set

data VCtx where
  ∅ : VCtx ∅
  _⊹_ : {n : ℕ} {G : Ctx n} {T : Ty n} → VCtx G → VTy G T → VCtx (G ⊹ T)

data VTms where
  ! : {n : ℕ} {G : Ctx n} → VTms G ! ∅
  _⊕_ : {n m : ℕ} {G : Ctx n} {D : Ctx m} {ES : Tms n m} {E : Tm n}
    {T : Ty m} (σ : VTms G ES D) (t : VTm G E (T [ ES ]Ty)) →
    VTms G (ES ⊕ E) (D ⊹ T)

data VTy where
  R-Ty : {n : ℕ} {G : Ctx n} → VTy G 𝒰
  R-Π : {n : ℕ} {G : Ctx n} {T : Ty n} {S : Ty (suc n)} →
    VTy G T → VTy (G ⊹ T) S → VTy G (Π T S)
  R-El : {n : ℕ} {G : Ctx n} {E : Tm n} → VTm G E 𝒰 → VTy G (El E)

data VTm where
  R-Var : {n : ℕ} {G : Ctx n} {T : Ty n} {m : Subset n 1} →
    Var G m T → VTm G (V m) T
  R-Lam : {n : ℕ} {G : Ctx n} {E : Tm (suc n)} {T : Ty n} {S : Ty (suc n)}
    (t : VTm (G ⊹ T) E S) → VTm G (Lam E) (Π T S)
  R-App : {n : ℕ} {G : Ctx n} {E₁ E₂ : Tm n} {T : Ty n} {S : Ty (suc n)}
    (t : VTm G E₁ (Π T S)) (s : VTm G E₂ T) →
    VTm G (App E₁ E₂) (S [ idTms ⊕ E₂ ]Ty)

weakenVTm : {n m : ℕ} {X : Subset n m}
  {G : Ctx n} {D : Ctx m} {E : Tm m} {T : Ty m} →
  Ren G D X → VTm D E T → VTm G (weakenTm X E) (weakenTy X T)
weakenVTm σ (R-Var v) = {!!}
weakenVTm σ (R-Lam t) = R-Lam (weakenVTm (W₂Ren σ) t)
weakenVTm σ (R-App t s) = {!R-App (weakenVTm σ t) (weakenVTm σ s)!}

weakenVTy : {n m : ℕ} {X : Subset n m} {G : Ctx n} {D : Ctx m} {T : Ty m} →
  Ren G D X → VTy D T → VTy G (weakenTy X T)
weakenVTy σ R-Ty = R-Ty
weakenVTy σ (R-Π A B) = R-Π (weakenVTy σ A) (weakenVTy (W₂Ren σ) B)
weakenVTy σ (R-El t) = R-El (weakenVTm σ t)

