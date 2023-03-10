{-# OPTIONS --without-K --rewriting #-}

module types where

open import lists
open import syn

Ctx : β β Set
Ctx = πΆπ‘π₯ (πAlg β Ty zero Ξ» {n} A β suc n)

Ren : {n m : β} β Ctx n β Ctx m β Subset n m β Set
Ren = πππ (βAlg Subset weakenTy done (Ξ» A X β yes X) (Ξ» A X β no X))

WβRen : {n m : β} {G : Ctx n} {D : Ctx m} {X : Subset n m}
  {T : Ty n} β Ren G D X β Ren (G βΉ T) D (no X)
WβRen {T = T} Ο = no T Ο

WβRen : {n m : β} {G : Ctx n} {D : Ctx m} {X : Subset n m}
  {T : Ty m} β Ren G D X β Ren (G βΉ weakenTy X T) (D βΉ T) (yes X)
WβRen {T = T} Ο = yes T Ο

idRen : {n : β} {G : Ctx n} β Ren G G all-yes
idRen {G = β} = done
idRen {G = G βΉ A} = WβRen idRen

data Var : {n : β} (G : Ctx n) (v : Subset n 1) (T : Ty n) β Set where
  π§π£ : {n : β} {G : Ctx n} {T : Ty n} β
    Var (G βΉ T) (yes all-no) (WTy T)
  π π£ : {n : β} {G : Ctx n} {T S : Ty n} {v : Subset n 1} β
    Var G v S β Var (G βΉ T) (no v) (WTy S)

deriveVar : {n m : β} {G : Ctx n} {D : Ctx m}
  {X : Subset n m} {v : Subset m 1} {T : Ty m} β
  Ren G D X β Var D v T β Var G (trans X v) (weakenTy X T)
deriveVar (yes A Ο) π§π£ = π§π£ 
deriveVar (yes A Ο) (π π£ v) = π π£ (deriveVar Ο v)
deriveVar (no A Ο) v = π π£ (deriveVar Ο v)

data VCtx : {n : β} β Ctx n β Set
data VTms : {n m : β} β Ctx n β Tms n m β Ctx m β Set
data VTy : {n : β} β Ctx n β Ty n β Set
data VTm : {n : β} β Ctx n β Tm n β Ty n β Set

data VCtx where
  β : VCtx β
  _βΉ_ : {n : β} {G : Ctx n} {T : Ty n} β VCtx G β VTy G T β VCtx (G βΉ T)

data VTms where
  ! : {n : β} {G : Ctx n} β VTms G ! β
  _β_ : {n m : β} {G : Ctx n} {D : Ctx m} {ES : Tms n m} {E : Tm n}
    {T : Ty m} (Ο : VTms G ES D) (t : VTm G E (T [ ES ]Ty)) β
    VTms G (ES β E) (D βΉ T)

data VTy where
  R-Ty : {n : β} {G : Ctx n} β VTy G π°
  R-Ξ  : {n : β} {G : Ctx n} {T : Ty n} {S : Ty (suc n)} β
    VTy G T β VTy (G βΉ T) S β VTy G (Ξ  T S)
  R-El : {n : β} {G : Ctx n} {E : Tm n} β VTm G E π° β VTy G (El E)

data VTm where
  R-Var : {n : β} {G : Ctx n} {T : Ty n} {m : Subset n 1} β
    Var G m T β VTm G (V m) T
  R-Lam : {n : β} {G : Ctx n} {E : Tm (suc n)} {T : Ty n} {S : Ty (suc n)}
    (t : VTm (G βΉ T) E S) β VTm G (Lam E) (Ξ  T S)
  R-App : {n : β} {G : Ctx n} {Eβ Eβ : Tm n} {T : Ty n} {S : Ty (suc n)}
    (t : VTm G Eβ (Ξ  T S)) (s : VTm G Eβ T) β
    VTm G (App Eβ Eβ) (S [ idTms β Eβ ]Ty)

weakenVTm : {n m : β} {X : Subset n m}
  {G : Ctx n} {D : Ctx m} {E : Tm m} {T : Ty m} β
  Ren G D X β VTm D E T β VTm G (weakenTm X E) (weakenTy X T)
weakenVTm Ο (R-Var v) = R-Var (deriveVar Ο v)
weakenVTm Ο (R-Lam t) = R-Lam (weakenVTm (WβRen Ο) t)
weakenVTm Ο (R-App t s) = R-App (weakenVTm Ο t) (weakenVTm Ο s)

weakenVTy : {n m : β} {X : Subset n m} {G : Ctx n} {D : Ctx m} {T : Ty m} β
  Ren G D X β VTy D T β VTy G (weakenTy X T)
weakenVTy Ο R-Ty = R-Ty
weakenVTy Ο (R-Ξ  A B) = R-Ξ  (weakenVTy Ο A) (weakenVTy (WβRen Ο) B)
weakenVTy Ο (R-El t) = R-El (weakenVTm Ο t)

WVTy : {n : β} {G : Ctx n} {D : Ctx n} {T S : Ty n} β
  VTy G T β VTy (G βΉ S) (WTy T)
WVTy A = weakenVTy (WβRen idRen) A

WβVTms : {n m : β} {G : Ctx n} {D : Ctx m} {ES : Tms n m}
  {T : Ty n} β VTms G ES D β VTms (G βΉ T) (WβTms ES) D
WβVTms ! = !
WβVTms (Ο β t) = WβVTms Ο β weakenVTm (WβRen idRen) t

WβVTms : {n m : β} {G : Ctx n} {D : Ctx m} {ES : Tms n m}
  {T : Ty m} β VTms G ES D β VTms (G βΉ (T [ ES ]Ty)) (WβTms ES) (D βΉ T)
WβVTms Ο = WβVTms Ο β R-Var π§π£

idVTms : {n : β} {G : Ctx n} β VTms G idTms G
idVTms {G = β} = !
idVTms {G = G βΉ A} = WβVTms idVTms

deriveTm : {n m : β} {G : Ctx n} {D : Ctx m}
  {ES : Tms n m} {v : Subset m 1} {T : Ty m} β
  VTms G ES D β Var D v T β VTm G (π§Vec (derive ES v)) (T [ ES ]Ty)
deriveTm (Ο β t) π§π£ = t
deriveTm (Ο β t) (π π£ v) = deriveTm Ο v

_[_]VTm : {n m : β} {G : Ctx n} {D : Ctx m}
  {ES : Tms n m} {E : Tm m} {T : Ty m} β
  VTm D E T β VTms G ES D β VTm G (E [ ES ]Tm) (T [ ES ]Ty)
R-Var v [ Ο ]VTm = deriveTm Ο v
R-Lam t [ Ο ]VTm = R-Lam (t [ WβVTms Ο ]VTm)
R-App t s [ Ο ]VTm = R-App (t [ Ο ]VTm) (s [ Ο ]VTm)

_[_]VTy : {n m : β} {G : Ctx n} {D : Ctx m}
  {ES : Tms n m} {T : Ty m} β
  VTy D T β VTms G ES D β VTy G (T [ ES ]Ty)
R-Ty [ Ο ]VTy = R-Ty
R-Ξ  A B [ Ο ]VTy = R-Ξ  (A [ Ο ]VTy) (B [ WβVTms Ο ]VTy)
R-El t [ Ο ]VTy = R-El (t [ Ο ]VTm)
