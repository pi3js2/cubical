{-# OPTIONS --safe --experimental-lossy-unification #-}

{-
This file contains
1. The Thom isomorphism (various related forms of it)
2. The Gysin sequence
-}
open import Cubical.Cohomology.EilenbergMacLane.Base
open import Cubical.Cohomology.EilenbergMacLane.Groups.Sn
open import Cubical.Cohomology.EilenbergMacLane.CupProduct

open import Cubical.Homotopy.EilenbergMacLane.CupProduct
open import Cubical.Homotopy.EilenbergMacLane.CupProductTensor
  renaming (_⌣ₖ_ to _⌣ₖ⊗_ ; ⌣ₖ-0ₖ to ⌣ₖ-0ₖ⊗ ; 0ₖ-⌣ₖ to 0ₖ-⌣ₖ⊗)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.EilenbergMacLane.GradedCommTensor
  hiding (⌣ₖ-comm)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
open import Cubical.Homotopy.EilenbergMacLane.Base
open import Cubical.Homotopy.EilenbergMacLane.Properties
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base

open import Cubical.Functions.Morphism
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Isomorphism

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SetTruncation as ST
open import Cubical.HITs.Truncation as TR
open import Cubical.HITs.Sn
open import Cubical.HITs.Pushout
open import Cubical.HITs.EilenbergMacLane1.Base
open import Cubical.HITs.Susp
open import Cubical.HITs.S1

open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order hiding (eq)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool hiding (_≤_)

open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing

open import Cubical.HITs.RPn
open import Cubical.Homotopy.EilenbergMacLane.Order2

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.HLevels
open import Cubical.Foundations.Function
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.SmashProduct

open import Cubical.Cohomology.EilenbergMacLane.GenSmash

open import Cubical.Foundations.Univalence


module Cubical.Cohomology.EilenbergMacLane.Steenrod where

open import Cubical.HITs.Join

data abr' (A : Bool → Type) : Type where
  ins' : (b : Bool) → A b → A (not b) → abr' A
  gl'₁ : (a : A true) (b : A false) → ins' true a b ≡ ins' false b a
  gl'₂ : (a : A false) (b : A true) → ins' false a b ≡ ins' true b a

  -- xs


  -- (x : X) × ((x : X) → A x)  --->
   --     |
    --    v
  -- Σ[ x ∈ X ] (A x × A ?) ,,, Σ[ x ∈ A x ] 


module _ (X : RP∞) (A : fst X → Type) where
  data abr (X : RP∞) (A : fst X → Type)  : Type where
    inss : (x : fst X) → A x → A (not* X x) → abr X A
    gl : (x : fst X) (a : _) (b : _)
      → inss x a b
       ≡ inss (not* X x) b (subst A (sym (not*not* X x)) a)

  abr→Atrue : (A : Bool → Type) → abr Bool* A → A true
  abr→Atrue A (inss false y l) = l
  abr→Atrue A (inss true y l) = y
  abr→Atrue A (gl false a b i) = b
  abr→Atrue A (gl true a b i) = transportRefl a (~ i)

  typs : (X : RP∞) (x : fst X) (A : fst X → Type) → abr X A → A x
  typs = J2-elem _ .fst abr→Atrue

  typs' : (X : RP∞) (A : fst X → Type) → abr X A → (x : fst X) → A x
  typs' X A p x = typs X x A p


-- true , const -> true , true
-- false , const -> false , false
-- true , not ->  true , false
-- false , not , -> false ,true 

{-
  uncurry λ X
    → elim→Set
         (λ _ → isSetΠ λ _ → isSet⊎ {!!} {!!})
         {!!}
         {!!}
         -}

module _ (X Y : RP∞) where
  toFunz : (fst Y ⊎ (fst X ≃ fst Y)) → fst X → fst Y
  toFunz (inl y) _ = y
  toFunz (inr z) = fst z

isEq-toFunz : (X Y : RP∞) → isEquiv (toFunz X Y)
isEq-toFunz = RP∞pt→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _)
  (RP∞pt→Prop (λ _ → isPropIsEquiv _)
    (isoToIsEquiv myIso))
  where
  invFunz : Bool × Bool → (Bool ⊎ (Bool ≃ Bool))
  invFunz (false , false) = inl false
  invFunz (false , true) = inr notEquiv
  invFunz (true , false) = inr (idEquiv _)
  invFunz (true , true) = inl true

  myIso : Iso _ _
  Iso.fun myIso = toFunz Bool* Bool*
  Iso.inv myIso f = invFunz (f true , f false)
  Iso.rightInv myIso f =
    funExt (h (f true) (f false)) ∙ sym (f≡ f)
    where
    mkbool : {A : Type} (x y : A) → Bool → A
    mkbool x y true = x
    mkbool x y false = y

    f≡ : {A : Type} (f : Bool → A) → f ≡ mkbool (f true) (f false)
    f≡ f i false = f false
    f≡ f i true = f true

    h : (x y z : Bool) → toFunz Bool* Bool* (invFunz (x , y)) z ≡ mkbool x y z
    h false false false = refl
    h false false true = refl
    h false true false = refl
    h false true true = refl
    h true false false = refl
    h true false true = refl
    h true true false = refl
    h true true true = refl
  Iso.leftInv myIso (inl false) = refl
  Iso.leftInv myIso (inl true) = refl
  Iso.leftInv myIso (inr x) =
    ((λ i → invFunz (fst (Iso.leftInv Bool≃Charac x (~ i)) true
      , fst (Iso.leftInv Bool≃Charac x (~ i)) false))
      ∙ h (Iso.fun Bool≃Charac x))
    ∙
    (λ i → inr (Iso.leftInv Bool≃Charac x i))
    where
    h : (t : Bool) → invFunz (fst (Iso.inv Bool≃Charac t) true
                             , fst (Iso.inv Bool≃Charac t) false)
                    ≡ inr (Iso.inv Bool≃Charac t)
    h false = refl
    h true = refl

toFunz-Eq : (X Y : RP∞)
  → (fst Y ⊎ (fst X ≃ fst Y)) ≃ (fst X → fst Y)
toFunz-Eq X Y = toFunz X Y , isEq-toFunz X Y

toFunz-ind : ∀ {ℓ} (X Y : RP∞) (A : (fst X → fst Y) → Type ℓ)
  → ((x : _) → A (toFunz X Y x))
  → (x : _) → A x
toFunz-ind X Y A x f =
  subst A (secEq (_ , isEq-toFunz X Y) f) (x (invEq (_ , isEq-toFunz X Y) f))

module _ {ℓ : Level} (X : RP∞) (A : fst X → Type ℓ) where
  data jo : Type ℓ where
    makel : {x : fst X} → A x → jo
    maker : ((x : _) → A x) → jo
    pusher : {x : fst X} (f : ((x : _) → A x)) → makel (f x) ≡ maker f

  jo* : Type ℓ
  jo* = Pushout {A = fst X × ((x : _) → A x)}
                {B = Σ[ x ∈ fst X ] A x}
                {C = ((x : _) → A x)}
                (λ f → fst f , snd f (fst f))
                snd

eval-⊎ : (X Y : RP∞)
  → fst Y ⊎ (fst X ≃ fst Y)
  → (x : fst X)
  → fst Y
eval-⊎ X Y (inl y) x = y
eval-⊎ X Y (inr g) x = fst g x

DD : {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Type ℓ)
  → ((x : fst X) → Σ (fst Y) (A x))
  → Σ[ f ∈ (fst Y ⊎ (fst X ≃ fst Y)) ]
       ((x : fst X) → A x (eval-⊎ X Y f x))
fst (DD X Y A g) = invEq (toFunz-Eq X Y) (fst ∘ g)
snd (DD X Y A g) x = subst (A x) help (g x .snd)
  where
  hh' : (r : fst Y ⊎ (fst X ≃ fst Y)) (x : fst X)
    → eval-⊎ X Y r x ≡ toFunz X Y r x 
  hh' (inl x₁) x = refl
  hh' (inr x₁) x = refl

  help : fst (g x)
       ≡ eval-⊎ X Y (invEq (toFunz-Eq X Y) (λ x₁ → fst (g x₁))) x
  help =
      funExt⁻ (sym (secEq (toFunz-Eq X Y) (fst ∘ g))) x
    ∙ sym (hh' (invEq (toFunz-Eq X Y) (λ x₁ → fst (g x₁))) x)
  {- J2-elem _ .fst
    (J2-elem _ .fst
      λ A g → {!invEq (toFunz-Eq Bool* Bool*) g!})
    where
    k : (r : fst Bool* ⊎ (fst Bool* ≃ fst Bool*))
      → eval-⊎ Bool* Bool* r true ≡ toFunz Bool* Bool* r true
    k (inl x) = refl
    k (inr x) = refl
-}

module _ {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Type ℓ) where
  ¬' = not* X

  A' B' : fst X → Type ℓ
  A' x = Σ[ y ∈ fst Y ] A x y
  B' x = (y : _) → A x y
{-
  data mjo' : Type ℓ where
    aa : (fst Y ⊎ (fst X ≃ fst Y) → mjo') → mjo' -- ((x : fst X) → A' x) → mjo
    bb : ((x : fst X) → B' x) → mjo'
    ab : (x : fst X) → A' x → B' (¬' x) → mjo'
    ar : {!!}
    {- (x : fst X) (a : (k : fst X) → A' k) (b : B' (¬' x))
      → snd (a (¬' x)) ≡ b _ →  aa a ≡ ab _ (a x) b -}
    br : {!!}
      {- (x : fst X) (a : A' x) (b : (k : fst X) → B' k)
      → a .snd ≡ b x (fst a)
      → ab x a (b (¬' x)) ≡ bb b -}
    rr : {!!}
    {- (a : (x : fst X) → A' x) (b : (x : fst X) → B' x)
         (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
      → aa a ≡ bb b -}
    rr' : {!!}
    {- (a : (x : fst X) → A' x) (b : (x : fst X) → B' x)
         (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
         (x : fst X)
         → PathP (λ i → ar x a (b (¬' x)) (c _) i ≡ bb b)
                  (rr a b c) (br x (a x) b (c x))
                  -}
-}
  data mjo : Type ℓ where
    aa : ((x : fst X) → A' x) → mjo
    bb : ((x : fst X) → B' x) → mjo
    ab : (x : fst X) → A' x → B' (¬' x) → mjo
    ar : (x : fst X) (a : (k : fst X) → A' k) (b : B' (¬' x))
      → snd (a (¬' x)) ≡ b _ →  aa a ≡ ab _ (a x) b
    br : (x : fst X) (a : A' x) (b : (k : fst X) → B' k)
      → a .snd ≡ b x (fst a)
      → ab x a (b (¬' x)) ≡ bb b
    rr : (a : (x : fst X) → A' x) (b : (x : fst X) → B' x)
         (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
      → aa a ≡ bb b
    rr' : (a : (x : fst X) → A' x) (b : (x : fst X) → B' x)
         (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
         (x : fst X)
         → PathP (λ i → ar x a (b (¬' x)) (c _) i ≡ bb b)
                  (rr a b c) (br x (a x) b (c x))

  Σf = Σ[ f ∈ (fst Y ⊎ (fst X ≃ fst Y)) ]
         ((x : fst X) → A x (eval-⊎ X Y f x))

  data mjo* : Type ℓ where
    aa* : Σf → mjo*
    bb* : ((x : fst X) → B' x) → mjo*
    ab* : (x : fst X) (y : fst Y) → A x y → B' (¬' x) → mjo*
    ar* : (x : fst X) (fh : Σf) (b : B' (¬' x))
      → fh .snd (¬' x) ≡ b _
      → aa* fh ≡ ab* x (eval-⊎ X Y (fh .fst) x) (fh .snd x) b
    br* : (x : fst X) (y : fst Y) (a : A x y)
          (b : (k : fst X) → B' k)
       → a ≡ b x y
       → ab* x y a (b (¬' x)) ≡ bb* b
    rr* : (fh : Σf) (b : (x : fst X) → B' x)
          (c : (x : fst X) → fh .snd x ≡ b x _)
          → aa* fh ≡ bb* b
    rr** : (fh : Σf) (b : (x : fst X) → B' x)
          (c : (x : fst X) → fh .snd x ≡ b x _)
          (x : fst X)
       → PathP (λ i → ar* x fh (b (¬' x)) (c (¬' x)) i ≡ bb* b)
                (rr* fh b c)
                (br* x (eval-⊎ X Y (fh .fst) x) (fh .snd x) b (c x))

  TP = jo* Y λ y → jo* X λ x → A x y

  F1 : (x : fst Y ⊎ (fst X ≃ fst Y))
       (q : (x₁ : fst X) → A x₁ (eval-⊎ X Y x x₁))
       (y : fst Y) → jo* X (λ x₂ → A x₂ y)
  F1 x q y = {!!}

  THEF : mjo* → TP
  THEF (aa* (inl x , q)) = inl (x , inr q)
  THEF (aa* (inr x , q)) =
    inr λ y → inl (invEq x y
             , subst (A (invEq x y)) (secEq x y) (q (invEq x y)))
  THEF (bb* g) = inr λ y → inr (λ x → g x y)
  THEF (ab* x y xy bn) =
    inr (CasesRP Y y (inr (CasesRP X x xy (bn y)))
                     (inl ((¬' x) , bn (not* Y y))))
  THEF (ar* x (inl y , m) b x₁ i) = pst* i
    where
    pst* : Path TP (inl (y , inr m)) (inr
         (CasesRP Y y (inr (CasesRP X x (m x) (b y)))
          (inl (¬' x , b (not* Y y)))))
    pst* = {!λ i → !}
      ∙ push (y , CasesRP Y y (inr m) (inl (¬' x , b _)))
      ∙ {!!}
  THEF (ar* x (inr f , m) b x₁ i) = inr (pth i)
    where
    inr* : _ → TP
    inr* = inr
    pth : Path ((y : fst Y) → jo* X (λ x → A x y))
                (λ y →
            inl (invEq f y
              , subst (A (invEq f y)) (secEq f y) (m (invEq f y))))
                ((CasesRP Y (fst f x)
                  (inr (CasesRP X x (m x) (b (fst f x))))
                  (inl (¬' x , b (not* Y (fst f x))))))
    pth = funExt λ y'
      → {!!}

  THEF (br* x y a b x₁ i) = {!!}
  THEF (rr* (inl x , m) b c i) = {!c!}
    where
    help : Path TP (inl (x , inr m)) (inr (λ y → inr (λ x₁ → b x₁ y)))
    help = (λ i → inl (x , inr (λ x' → c x' i)))
         ∙ push (x , λ y → inr (λ x → b x y))
  THEF (rr* (inr x , m) b c i) = {!!}
  THEF (rr** fh b c x i i₁) = {!!}

{-
Σ[ f ∈ (fst Y ⊎ (fst X ≃ fst Y)) ]
       ((x : fst X) → A x (eval-⊎ X Y f x))
-}
  

--   mjo-ind'' : {!!}
--   mjo-ind'' = {!!}

--   module _ {ℓ : Level} {B : Type ℓ}
--            (bb' : ((x : fst X) → B' x) → B)
--            (ab' : (x₂ : fst X) → A' x₂ → B' (¬' x₂) → B)
--            (x : fst X)
--            (b : (k : fst X) → B' k)
--            (a : A' x)
--            (qdr : (n : (k : fst X) → A' k)
--             → n x .snd ≡ b x (n x .fst)
--             → ab' x (n x) (b (¬' x)) ≡ bb' b)
--            (x₁ : a .snd ≡ b x (fst a)) where
 
--     n : (k : fst X) → A' k
--     fst (n k) = a .fst
--     snd (n k) =
--       CasesRP X {A = λ k → A k (a .fst)}
--               x (a .snd) (b (¬' x) (a .fst)) k

--     n-x≡ : n x ≡ a
--     fst (n-x≡ i) = a .fst
--     snd (n-x≡ i) =
--       CasesRPβ X {A = λ k → A k (a .fst)}
--               x (a .snd) (b (¬' x) (a .fst)) .fst i

--     h* : ab' x a (b (¬' x)) ≡ bb' b
--     h* = cong (λ z → ab' x z (b (¬' x))) (sym n-x≡)
--       ∙ qdr n (cong snd n-x≡ ∙ x₁)
 

--   mjo-ind* : ∀ {ℓ} {B : Type ℓ}
--     → (aa' : ((x : fst X) → A' x) → B)
--     → (bb' : ((x : fst X) → B' x) → B)
--     → (ab' : (x : fst X) → A' x → B' (¬' x) → B)
--     → ((a : (k : fst X) → A' k)
--       → Σ[ br' ∈ ((b : (k : fst X) → B' k) (x : fst X) → a x .snd ≡ b x (a x .fst)
--                → ab' x (a x) (b (¬' x)) ≡ bb' b) ]
--           Σ[ ar' ∈ ((x : fst X) (b : B' (¬' x))
--       → snd (a (¬' x)) ≡ b _ →  aa' a ≡ ab' _ (a x) b) ]
--             ((b : (k : fst X) → B' k) (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
--           → Σ[ rr ∈ aa' a ≡ bb' b ] ((x : fst X)
--             → PathP (λ i → ar' x (b (¬' x)) (c _) i ≡ bb' b)
--                      rr (br' b x (c x) ))))
--     → mjo → B
--   mjo-ind* aa' bb' ab' qdr (aa x) = aa' x
--   mjo-ind* aa' bb' ab' qdr (bb x) = bb' x
--   mjo-ind* aa' bb' ab' qdr (ab x x₁ x₂) = ab' x x₁ x₂
--   mjo-ind* aa' bb' ab' qdr (ar x a b x₁ i) = qdr a .snd .fst x b x₁ i
--   mjo-ind* aa' bb' ab' qdr (br x a b x₁ i) =
--     h* bb' ab' x b a (λ n → qdr n .fst b x) x₁ i -- h i
--   mjo-ind* aa' bb' ab' qdr (rr a b c i) = qdr a .snd .snd b c .fst i
--   mjo-ind* aa' bb' ab' qdr (rr' a b c x i j) = {!qdr a .snd .snd b c .snd x!}
--     where
--     lem : h* bb' ab' x b (a x) (λ n₁ → qdr n₁ .fst b x) (c x)
--        ≡ fst (qdr a) b x (c x)
--     lem = {!!}
--     cb : PathP (λ i → qdr a .snd .snd b c .fst i
--                      ≡ h* bb' ab' x b (a x) (λ n₁ → qdr n₁ .fst b x) (c x) i)
--           (qdr a .snd .fst x (b (¬' x)) (c (¬' x)))
--           (refl {x = bb' b})
--     cb i j = hcomp (λ k → λ {(i = i0) → qdr a .snd .snd b c .snd x j (~ k)
--                             ; (i = i1) → bb' b
--                             ; (j = i0) → fst (qdr a .snd .snd b c) (~ k ∨ i)
--                             ; (j = i1) → {!qdr a .snd .snd b c .snd x j (~ k)!}})
--                    {!!}
--   mjo-ind' : ∀ {ℓ} {B : Type ℓ}
--     → (aa' : ((x : fst X) → A' x) → B)
--     → (bb' : ((x : fst X) → B' x) → B)
--     → (ab' : (x : fst X) → A' x → B' (¬' x) → B)
--     → (br' : (b : (k : fst X) → B' k)
--                (x : fst X) (a : A' x)
--               → a .snd ≡ b x (fst a)
--                  → ab' x a (b (¬' x)) ≡ bb' b)
--     → ((a : (k : fst X) → A' k)
--         → Σ[ ar' ∈ ((x : fst X) (a : (k : fst X) → A' k) (b : B' (¬' x))
--       → snd (a (¬' x)) ≡ b _ →  aa' a ≡ ab' _ (a x) b) ]
--             ((b : (k : fst X) → B' k) (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
--           → Σ[ rr ∈ aa' a ≡ bb' b ] ((x : fst X)
--             → PathP (λ i → ar' x a (b (¬' x)) (c _) i ≡ bb' b)
--                      rr (br' b x (a x) (c x)))))
--     → mjo → B
--   mjo-ind' aa' bb' ab' b' tr (aa x) = aa' x
--   mjo-ind' aa' bb' ab' b' tr (bb x) = bb' x
--   mjo-ind' aa' bb' ab' b' tr (ab x x₁ x₂) = ab' x x₁ x₂
--   mjo-ind' aa' bb' ab' b' tr (ar x a b x₁ i) = tr a .fst x a b x₁ i
--   mjo-ind' aa' bb' ab' b' tr (br x a b x₁ i) = b' b x a x₁ i
--   mjo-ind' aa' bb' ab' b' tr (rr a b c i) = tr a .snd b c .fst i
--   mjo-ind' aa' bb' ab' b' tr (rr' a b c x i i₁) = tr a .snd b c .snd x i i₁
-- {-
--   mjo-ind : ∀ {ℓ} {B : Type ℓ}
--     → (aa' : ((x : fst X) → A' x) → B)
--     → (bb' : ((x : fst X) → B' x) → B)
--     → (ab' : (x : fst X) → A' x → B' (¬' x) → B)
--     → (ar' : (x : fst X) (a : (k : fst X) → A' k) (b : B' (¬' x))
--       → snd (a (¬' x)) ≡ b _ →  aa' a ≡ ab' _ (a x) b)
--     → ((b : (k : fst X) → B' k)
--         → Σ[ br' ∈ ((x : fst X) (a : A' x)
--                  → a .snd ≡ b x (fst a)
--                  → ab' x a (b (¬' x)) ≡ bb' b) ]
--             ((a : (x : fst X) → A' x) (c : (x : fst X) → a x .snd ≡ b x (fst (a x)))
--           → Σ[ rr ∈ aa' a ≡ bb' b ] ((x : fst X)
--             → PathP (λ i → ar' x a (b (¬' x)) (c _) i ≡ bb' b)
--                      rr (br' x (a x) (c x)))))
--     → mjo → B
--   mjo-ind aa' bb' ab' ar' tr (aa x) = aa' x
--   mjo-ind aa' bb' ab' ar' tr (bb x) = bb' x
--   mjo-ind aa' bb' ab' ar' tr (ab x x₁ x₂) = ab' x x₁ x₂
--   mjo-ind aa' bb' ab' ar' tr (ar x a b x₁ i) = ar' x a b x₁ i
--   mjo-ind aa' bb' ab' ar' tr (br x a b x₁ i) = tr b .fst x a x₁ i
--   mjo-ind aa' bb' ab' ar' tr (rr a b c i) = tr b .snd a c .fst i
--   mjo-ind aa' bb' ab' ar' tr (rr' a b c x i i₁) = tr b .snd a c .snd x i i₁
--   -}

-- {-
-- module mjoind {ℓ} (X Y : RP∞) where
--   aa* : (A : fst X → fst Y → Type ℓ)
--   aa* = ?
-- -}
--   F : (f : fst X ≃ fst Y)
--     → ((x : _) → A x (fst f x))
--     → (y : fst Y)
--     → Σ (fst X) (λ x → A x y)
--   fst (F e f y) = invEq e y
--   snd (F e f y) = subst (A (invEq e y)) (secEq e y) (f (invEq e y))

--   M : (t : fst Y ⊎ (fst X ≃ fst Y))
--       → ((x : _) → A x (toFunz X Y t x))
--       → jo* Y λ y → jo* X λ x → A x y
--   M (inl x) p = inl (x , inr p)
--   M (inr x) p = inr λ y → inl (F x p y)

--   G : (fst X → fst Y) → fst Y ⊎ (fst X ≃ fst Y)
--   G = invEq (_ , isEq-toFunz X Y)

--   M₂ : (f : (x : fst X) → A' x) (x : fst X) → A x (toFunz X Y (G (λ x₁ → fst (f x₁))) x)
--   M₂ f x = subst (A x) (funExt⁻ (sym ((secEq (_ , isEq-toFunz X Y)) (fst ∘ f))) x)
--              (f x .snd)

--   test' : mjo → jo* Y λ y → jo* X λ x → A x y
--   test' =
--     mjo-ind' F1 F2 F3 F4
--       {!!}
--     where
--     TYP = jo* Y (λ y → jo* X (λ x → A x y))

--     F1 : ((x : fst X) → A' x) → TYP
--     F1 a = M (G (fst ∘ a)) (M₂ a)

--     F2 : ((x : fst X) → B' x) → TYP
--     F2 b = inr λ y → inr λ x → b x y

--     F3 : (x : fst X) → A' x → B' (¬' x) → TYP
--     F3 x (y , t) b = inl (y , inr (CasesRP X x t (b y)))

--     F4-gen : {!!}
--     F4-gen = {!!}

--     F4 : (b : (k : fst X) → B' k) (x : fst X) (a : A' x) →
--       a .snd ≡ b x (fst a) → F3 x a (b (¬' x)) ≡ F2 b
--     F4 b x (y , t) p =
--         {!!} -- cong (inl ∘ (y ,_)) {!!}
--       ∙ push (y , CasesRP Y y (inr (CasesRP X x t (b (¬' x) y))) (inr λ x → b x (not* Y y)))
--       ∙ {!!}
--       where
--       h : {!!} -- CasesRP Y y (inr (CasesRP X x t (b (¬' x) y))) (inr λ x → b x (not* Y y)) y ≡ {!inr !}
--       h = {!!}
  

--   test : mjo → jo* Y λ y → jo* X λ x → A x y
--   test (aa f) = M (G (fst ∘ f)) (M₂ f)
--   {- 
--     M (invEq (_ , isEq-toFunz X Y) (fst ∘ f))
--       λ x → subst (A x) (funExt⁻ (sym (secEq (_ , isEq-toFunz X Y) (fst ∘ f))) x)
--                      (f x .snd) -}
--   test (bb f) = inr λ y → inr λ x → f x y
--   test (ab x (y , a) f) = {!!}
--   test (ar x a b x₁ i) = {!!}
--   test (br x a b p i) = {!!}
--   test (rr a b c i) = Ml (G (λ x → fst (a x))) (M₂ a)
--     (funExt (λ x → (λ i → transp (λ j → A x (secEq (_ , isEq-toFunz X Y) (fst ∘ a) (i ∧ ~ j) x))
--                              (~ i) (b x (secEq (_ , isEq-toFunz X Y) (fst ∘ a) i x)))
--          ∙ cong (subst (A x) (funExt⁻ (sym ((secEq (_ , isEq-toFunz X Y)) (fst ∘ a))) x))
--              (sym (c x)))) i
--     where
--     inr* : _ → jo* Y λ y → jo* X λ x → A x y
--     inr* = inr

--     inl' : (y : _) → _ → jo* X λ x → A x y
--     inl' y = inl

--     Ml : (a : fst Y ⊎ (fst X ≃ fst Y)) (p : (x : fst X) → A x (toFunz X Y a x))
--       → (λ x → b _ _) ≡ p -- ((x : fst X) → p x ≡ b _ _)
--       → M a p
--       ≡ inr λ x → inr λ y → b y x
--     Ml (inl x) = J> push (x , λ y → inr λ x → b x y)
--     Ml (inr x) = J> cong inr* (funExt λ y
--        → cong (inl' y) (ΣPathP (refl
--                                , ((λ i → subst (A (invEq x y)) (λ j → secEq x y (j ∨ i))
--                                    (b (invEq x y) (secEq x y i ))) ∙ transportRefl (b (invEq x y) y))))
--       ∙ push ((invEq x y) , (λ x → b x y)))
--   test (rr' a b c x i i₁) = {!!}




-- module _ {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Type ℓ) where
--   data jo' : Type ℓ where
--     aa : ((x : fst X) → Σ[ y ∈ fst Y ] (A x y)) → jo'
--     bb : ((x : fst X) (y : _) → A x y) → jo'
--     ac : (m : (x : fst X) → fst Y
--        × ((y : _) → (A x y))) → aa (λ x → m x .fst , m x .snd (m x .fst))
--        ≡ bb λ x → m x .snd

--   jo'' : jo' → (x : fst X) → jo Y (A x)
--   jo'' (aa f) x = makel (f x .snd)
--   jo'' (bb g) x = maker (g x)
--   jo'' (ac m i) x = pusher {x = m x .fst} (m x .snd) i

-- t2 : ∀ {ℓ} (A : Bool → Bool → Type ℓ)
--   → Iso (jo' Bool* Bool* A)
--   ((x : _) → jo Bool* (A x))
-- Iso.fun (t2 A) = jo'' Bool* Bool* A
-- Iso.inv (t2 A) f = h (f true) (f false)
--   where
--   B→B : (x y : Bool) → Bool → Bool
--   B→B x y false = y
--   B→B x y true = x

--   B→B' : (x y : Bool) (t : Bool) → A true x → A false y → A t (B→B x y t)
--   B→B' x y false le ri = ri
--   B→B' x y true le ri = le


--   h : jo Bool* (A true) → jo Bool* (A false) → jo' Bool* Bool* A
--   h (makel {x = x} a) (makel {x = y} b) = aa λ t → B→B x y t , B→B' x y t a b
--   h (makel {x = x} a) (maker f) = {!!}
--   h (makel x) (pusher f i) = {!!}
--   h (maker x) y = {!!}
--   h (pusher f i) y = {!!}



-- Iso.rightInv (t2 A) = {!!}
-- Iso.leftInv (t2 A) = {!!}

-- isEq'' : {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Type ℓ)
--   → isEquiv ((jo'' X Y A))
-- isEq'' =
--   RP∞pt→Prop (λ _ → isPropΠ2 λ _ _ → isPropIsEquiv _)
--     (RP∞pt→Prop (λ _ → isPropΠ λ _ → isPropIsEquiv _ )
--       λ A → isoToIsEquiv (t2 A))

-- module palal' {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Type ℓ) where

-- --   to' : jo' → ((x : fst X) → jo Y (A x))
-- --   to' (aa f) x = makel {X = Y} {A = A x} {x = f x .fst} (f x .snd)
-- --   to' (bb f) x = maker (f x)

-- --   2-j : jo X (λ x → jo Y (A x)) → (jo Y λ y → jo X (λ x → A x y))
-- --   2-j (makel (makel x)) = makel (makel x)
-- --   2-j (makel (maker f)) = maker λ y → makel (f y)
-- --   2-j (makel (pusher {x = x} f i)) = {!!} -- maker λ y → makel {!f y!}
-- --   2-j (maker f) = {!f!}
-- --   2-j (pusher f i) = {!!}



-- -- joinish : ∀ {ℓ} (X : RP∞) (A : fst X → Type ℓ) → Type ℓ
-- -- joinish X A = Pushout {A = (x : _) → A x} {B = Σ _ A} {C = {!!}} {!!} {!!}


-- -- SM→Homogeneous≡ : ∀ {ℓ ℓ'} (X : RP∞) (x : fst X) {A : fst X → Pointed ℓ} {B : Pointed ℓ'}
-- --   → {f g : SM∙ X A →∙ B}
-- --   → isHomogeneous B
-- --   → ((t : (x : fst X) → A x .fst)
-- --   → fst f (inr t) ≡ fst g (inr t)) → f ≡ g -- f ≡ g
-- -- SM→Homogeneous≡ {ℓ = ℓ} {ℓ' = ℓ'} = J2-elem _ .fst f≡g
-- --   where
-- --   module _ {A : Bool → Pointed ℓ} {B : Pointed ℓ'} {f g : SM∙ Bool* A →∙ B}
-- --            (hom : isHomogeneous B)
-- --            (r : ((t : (x : fst Bool*) → A x .fst)
-- --               → fst f (inr t) ≡ fst g (inr t)))where
-- --     F = isoToEquiv (Iso-Smash-SM' {A = A})
-- --     G = Iso-Smash-SM'∙ {A = A} .snd

-- --     theIso : Iso (Smash∙ (A false) (A true) →∙ B) (SM∙ Bool* A →∙ B)
-- --     theIso = post∘∙equiv Iso-Smash-SM'∙

-- --     s = Iso.inv theIso

-- --     fs : (x : A true .fst) (y : A false .fst) (x₁ : Bool) → fst (A x₁)
-- --     fs x y true = x
-- --     fs x y false = y

-- --     lem : s f ≡ s g
-- --     lem = Smash→∙Homogeneous≡ hom λ x y
-- --       → cong (fst f) (Iso-Smash-SM'-proj' (fs y x))
-- --        ∙∙ r (fs y x)
-- --        ∙∙ sym (cong (fst g) (Iso-Smash-SM'-proj' (fs y x)))

-- --     f≡g : f ≡ g
-- --     f≡g = sym (Iso.rightInv theIso f)
-- --        ∙∙ cong (Iso.fun theIso) lem
-- --        ∙∙ Iso.rightInv theIso g



-- -- {-
-- --   ΣPathP ((funExt (λ { (inl x) → {!!}
-- --                      ; (inr x) → {!!}
-- --                      ; (push a i) → {!!}}))
-- --         , {!!})
-- -- -}


-- -- {-
-- -- module _ (I J : RP∞) (A : fst I → fst J → Pointed₀) where
-- --   ΠJA : fst I → Type
-- --   ΠJA i = (j : fst J) → A i j .fst

-- --   n : fst I → fst I
-- --   n = not* I

-- --   R : {i : fst I} → fst J → ΠJA i → Type
-- --   R {i = i} j f = Σ[ x ∈ fst (A i j) ] f ≡ CasesRP J j x (A i (not* J j) .snd)

-- --   data toSm : Type where
-- --     aa : ((i : fst I) → fst J) → toSm
-- --     bb : ((i : fst I) → ΠJA i) → toSm
-- --     ab : (i : fst I) →  fst J → ΠJA i → toSm
-- --     ar : (i : fst I) (a : fst I → fst J) (b : ΠJA i) → R (a i) b → aa a ≡ ab i (a i) b
-- --     br : (i : fst I) (a : fst J) (b : (i : fst I) → ΠJA i) → R a (b i) → ab i a (b (i)) ≡ bb b
-- --     rr : (a : (i : fst I) → fst J) (b : (i : fst I) → ΠJA i)
-- --       → ((i : fst I) → R (a i) (b i)) → aa a ≡ bb b
-- --     rr' :  (i : fst I) (a : (i : fst I) → fst J)
-- --            (b : (i : fst I) → ΠJA i)
-- --            (r : (i : fst I) → R (a i) (b i))
-- --         → PathP (λ k → aa a ≡ br i (a i) b (r i) (~ k)) (rr a b r) (ar i a (b (i)) (r (i)))

-- --   HH = SM J λ j → SM I (λ i → A i j) , inr λ i → A i j .snd
-- --   HH' : (j : fst J) → Type
-- --   HH' j = SM I (λ i → A i j)

-- --   ploink : toSm → SM J λ j → SM I (λ i → A i j) , inr λ i → A i j .snd
-- --   ploink (aa g) = inr λ j → inr λ i → A i j .snd -- inr λ j → inr {!!}
-- --   ploink (bb f) = inr λ j → inr λ i → f i j
-- --   ploink (ab i j t) = inl j
-- --   ploink (ar i a b (x , y) i₁) = {!!}
-- --     where

-- --     P1 : (j : _) → Path ((i : fst I) → A i j .fst) (λ i → A i j .snd) {!CasesRP J j ? ?!}
-- --     P1 = {!!}

-- --     PP' : (j : fst J) → (j ≡ a i) ⊎ (j ≡ {!a i!}) → Path (HH' j) (inr (λ i₂ → A i₂ j .snd)) (inr {!!}) -- (CasesRP I i (b j) (A (not* I i) j .snd)))
-- --     PP' j p = {!!}

-- --     PP : Path HH (inr (λ j → inr (λ i₂ → A i₂ j .snd))) (inl (a i))
-- --     PP = {!!} ∙ {!!} ∙ sym (push ((a i) , (inr (λ i₂ → A i₂ (a i) .snd))))
-- --   ploink (br i a b (x , y) i₁) = {!!}
-- --   ploink (rr g f h i) = {!!}
-- --     where
-- --     c2 : (j : fst J) → Path ((i : fst I) → A i j .fst)
-- --                         {!CasesRP I ? ?!}
-- --                         λ i₂ → CasesRP J (g i₂)
-- --                             (fst (h i₂)) (A i₂ (not* J (g i₂)) .snd) j
-- --     c2 j = {!!}

-- --     brr : Path ((j : fst J) → HH' j) (λ j → inr (λ i₁ → A i₁ j .snd)) λ j → inr (λ i₁ → f i₁ j)
-- --     brr = funExt λ j → ({!!} ∙ sym (push ({!!} , {!!})) ∙ {!!}) ∙ λ k → inr λ i → h i .snd (~ k) j
-- --   ploink (rr' i a b r k i₁) = {!!}



-- -- data asd (X : RP∞) (A : fst X → Type) (B : Type) : Type where
-- --   incc : ((x : fst X) → A x → A (not* X x) → B) → asd X A B
-- --   incr : ((x : fst X) → A x → B) → {!? !}
-- -- -}

-- -- SS₀ : Type
-- -- SS₀ = Bool

-- -- data genSusp {ℓ : Level} (X : RP∞) (A : Type ℓ) : Type ℓ where
-- --   pts : fst X → genSusp X A
-- --   mrd : (x : fst X) (a : A) → pts x ≡ pts (not* X x)

-- -- data seq-colim {ℓ : Level} (A : ℕ → Type ℓ) (f : (n : ℕ) → A n → A (suc n)) : Type ℓ where
-- --   mk : (n : ℕ) → A n → seq-colim A f
-- --   tr : (n : ℕ) (x : A n) → mk n x ≡ mk (suc n) (f n x)


-- -- SS-g : (X : RP∞) (n : ℕ) → Type
-- -- SS-g X zero = fst X
-- -- SS-g X (suc n) = genSusp X (SS-g X n)

-- -- SS-fun : (X : RP∞) (n : ℕ) → SS-g X n → SS-g X (suc n)
-- -- bataclan : (X : RP∞) (A : fst X → Pointed₀)
-- --   → ((x y : fst X) → isContr (A x ≡ A y))
-- --   → ∥ fst X ∥₁ → Pointed₀
-- -- bataclan X A t ∣ x ∣₁ = A x
-- -- bataclan X A t (squash₁ m a i) = PT.elim2 {P = λ a m → isContr (bataclan X A t a ≡ bataclan X A t m)} (λ _ _ → isPropIsContr) t m a .fst i

-- -- SS-fun X zero t = pts t
-- -- SS-fun X (suc n) (pts x) = pts x
-- -- SS-fun X (suc n) (mrd x a i) = mrd x (SS-fun X n a) i

-- -- SS-fun-const : (n : ℕ) (t : SS-g Bool* n)
-- --   → SS-fun Bool* n t ≡ pts true
-- -- SS-fun-const zero false = mrd false true
-- -- SS-fun-const zero true = refl
-- -- SS-fun-const (suc n) (pts false) = mrd false (pts true)
-- -- SS-fun-const (suc n) (pts true) = refl
-- -- SS-fun-const (suc n) (mrd false a i) j =
-- --   hcomp (λ k → λ {(i = i0) → mrd false (pts true) j
-- --                  ; (i = i1) → pts true
-- --                  ; (j = i0) → mrd false (SS-fun-const n a (~ k)) i
-- --                  ; (j = i1) → pts true})
-- --         (mrd false (pts true) (j ∨ i))
-- -- SS-fun-const (suc n) (mrd true a i) j =
-- --   hcomp (λ k → λ {(i = i0) → pts true
-- --                  ; (i = i1) → mrd false (pts true) j
-- --                  ; (j = i0) → mrd true (SS-fun-const n a (~ k)) i
-- --                  ; (j = i1) → pts true})
-- --         {!!} -- (mrd false (pts {!!}) {!i0!})

-- -- SSP = seq-colim (SS-g Bool*) (SS-fun Bool*)

-- -- SS-fun-const' : (n : ℕ) (t : SS-g Bool* n)
-- --   → Path SSP (mk (suc n) (SS-fun Bool* n t)) -- 
-- --               (mk (suc n) (pts true))
-- -- SS-fun-const' zero false = cong (mk 1) (mrd false true)
-- -- SS-fun-const' zero true = refl
-- -- SS-fun-const' (suc n) (pts false) = cong (mk (2 + n)) (mrd false (pts true))
-- -- SS-fun-const' (suc n) (pts true) = refl
-- -- SS-fun-const' (suc n) (mrd false a i) j =
-- --   hcomp (λ k → λ {(i = i0) → {!cong (mk (2 + n)) (mrd false (pts true)) k!} -- tr {f = SS-fun Bool*} (suc n) (mrd {!!} {!!} {!j!}) k
-- --                     ; (i = i1) → {!tr (suc n) (pts true) k ?!}
-- --                     ; (j = i0) → tr {f = SS-fun Bool*} (suc n) (mrd false a i) k -- 
-- --                     ; (j = i1) → {!!}})
-- --            {!!}
-- -- SS-fun-const' (suc n) (mrd true a i) j = {!!}
-- -- {-
-- --   hcomp (λ k → λ {(i = i0) → {!SS-fun-const' (suc n) (pts t) j!}
-- --                     ; (i = i1) → {!tr (suc n) (mrd t a i) k!}
-- --                     ; (j = i0) → tr (suc n) (mrd t a i) k
-- --                     ; (j = i1) → {!!}})
-- --            {!!}
-- -- -}
-- -- {-
-- -- i = i0 ⊢ SS-fun-const' (suc n) (pts t) j
-- -- i = i1 ⊢ SS-fun-const' (suc n) (pts (not* Bool* t)) j
-- -- j = i0 ⊢ mk (suc (suc n)) (SS-fun Bool* (suc n) (mrd t a i))
-- -- j = i1 ⊢ mk (suc (suc n)) (pts true)
-- -- -}
-- -- {-
-- --    mk (2 + n)
-- --     (hcomp (λ k → λ {(i = i0) → mrd false (pts true) j
-- --                     ; (i = i1) → pts true
-- --                     ; (j = i0) → mrd false (SS-fun-const n a (~ k)) i
-- --                     ; (j = i1) → pts true})
-- --            (mrd false (pts true) (j ∨ i)))

-- -- {-


-- -- -}
-- -- SS-fun-const' (suc n) (mrd true a i) j =
-- --   hcomp (λ k → λ {(i = i0) → mk (2 + n) (pts true)
-- --                  ; (i = i1) → mk (2 + n) (mrd false (pts true) j)
-- --                  ; (j = i0) → {!!}  -- mk (2 + n) (mrd true (SS-fun-const n a (~ k)) i)
-- --                  ; (j = i1) → mk (2 + n) (pts true)})
-- --          {!SS-fun-const' n a i0!} -}
-- -- {-
-- --   hcomp (λ k → λ {(i = i0) → mk (2 + n) (pts true)
-- --                  ; (i = i1) → mk (2 + n) (mrd false (pts true) j)
-- --                  ; (j = i0) → mk (2 + n) (mrd true (SS-fun-const n a (~ k)) i)
-- --                  ; (j = i1) → mk (2 + n) (pts true)})
-- --    (hcomp (λ k → λ {(i = i0) → {!!}
-- --                  ; (i = i1) → tr (suc n) {!pts true!} k
-- --                  ; (j = i0) → {!!}
-- --                  ; (j = i1) → {!!}})
-- --           {!!})
-- -- -}

-- -- contr : (n : ℕ) (t : SS-g Bool* (suc n)) → Path SSP (mk (suc n) t) (mk n {!!})
-- -- contr = {!!}
-- -- {-
-- -- fst contr = mk 0 true
-- -- snd contr (mk zero false) =
-- --   tr 0 true ∙∙ cong (mk 1) (mrd true true) ∙∙ sym (tr 0 false)
-- -- snd contr (mk zero true) = refl
-- -- snd contr (mk (suc zero) (pts false)) = tr 0 true ∙ cong (mk 1) (mrd true true)
-- -- snd contr (mk (suc zero) (pts true)) = tr 0 true
-- -- snd contr (mk (suc zero) (mrd false false i)) j = {!!}
-- -- snd contr (mk (suc zero) (mrd false true i)) j = {!!}
-- -- snd contr (mk (suc zero) (mrd true false i)) j = {!!}
-- -- snd contr (mk (suc zero) (mrd true true i)) j = {!!}
-- -- snd contr (mk (suc (suc n)) x) = {!!}
-- -- snd contr (tr zero false i) = {!!}
-- -- snd contr (tr zero true i) = {!!}
-- -- snd contr (tr (suc zero) x i) = {!!}
-- -- snd contr (tr (suc (suc n)) x i) = {!x!}
-- -- -}

-- -- BIG : ∀ {ℓ} (X Y : RP∞) (A : fst X → fst Y → Pointed ℓ)
-- --   → (x : fst X) (y : fst Y)
-- --   → Pointed ℓ
-- -- BIG X Y A x y =
-- --   Smash∙ (Smash∙ (A (not* X x) (not* Y y)) (A (not* X x) y))
-- --              (Smash∙ (A x (not* Y y)) (A x y))

-- -- myG-innerest : ∀ {ℓ ℓ'} (B : Pointed ℓ)  (A : fst Bool* → fst Bool* → Pointed ℓ') →
-- --       BIG Bool* Bool* A true true →∙ SM∙ Bool* (λ x₁ → SM∙ Bool* (A x₁))
-- -- myG-innerest B A = ≃∙map (Iso-Smash-SM'∙)
-- --             ∘∙ (Smash-map (≃∙map (Iso-Smash-SM'∙ {A = λ x → A false x}))
-- --                 (≃∙map (Iso-Smash-SM'∙ {A = λ x → A true x})) , refl)

-- -- myG-inner : ∀ {ℓ ℓ'} (B : Pointed ℓ) (Y : RP∞) (y : fst Y)
-- --   (A : fst Bool* → fst Y → Pointed ℓ') →
-- --       BIG Bool* Y A true y →∙ SM∙ Bool* (λ x₁ → SM∙ Y (A x₁))
-- -- myG-inner {ℓ' = ℓ'} B =
-- --   J2-elem (λ Y y → (A : fst Bool* → fst Y → Pointed ℓ') →
-- --       BIG Bool* Y A true y →∙ SM∙ Bool* (λ x₁ → SM∙ Y (A x₁))) .fst
-- --       (myG-innerest B)

-- -- myG :  ∀ {ℓ ℓ'} (B : Pointed ℓ)
-- --   (X : RP∞) (x : fst X)
-- --   (Y : RP∞) (y : fst Y)
-- --   (A : fst X → fst Y → Pointed ℓ')
-- --   → BIG X Y A x y
-- --   →∙ (SM∙ X (λ x → SM∙ Y (A x)))
-- -- myG {ℓ}{ℓ'} B = J2-elem (λ X x → (Y : RP∞) (y : fst Y)
-- --       (A : fst X → fst Y → Pointed ℓ') →
-- --       BIG X Y A x y →∙ SM∙ X (λ x₁ → SM∙ Y (A x₁)))
-- --       .fst
-- --       (myG-inner B)
-- --       {-
-- --       (J2-elem (λ Y y → (A : fst Bool* → fst Y → Pointed ℓ') →
-- --       BIG Bool* Y A true y →∙ SM∙ Bool* (λ x₁ → SM∙ Y (A x₁))) .fst
-- --       λ A → ≃∙map (Iso-Smash-SM'∙)
-- --             ∘∙ (Smash-map (≃∙map (Iso-Smash-SM'∙ {A = λ x → A false x}))
-- --                 (≃∙map (Iso-Smash-SM'∙ {A = λ x → A true x})) , refl))
-- -- -}
-- -- {-
-- --  J2-elem _ .fst
-- --   (J2-elem _ .fst λ A → ≃∙map (Iso-Smash-SM'∙)
-- --             ∘∙ (Smash-map (≃∙map (Iso-Smash-SM'∙ {A = λ x → A false x}))
-- --                 (≃∙map (Iso-Smash-SM'∙ {A = λ x → A true x})) , refl))
-- -- -}
-- -- theF : ∀ {ℓ ℓ'} (B : Pointed ℓ)
-- --   (X : RP∞) (x : fst X)
-- --   (Y : RP∞) (y : fst Y)
-- --   (A : fst X → fst Y → Pointed ℓ')
-- --   → (SM∙ X (λ x → SM∙ Y (A x)) →∙ B)
-- --   →  BIG X Y A x y →∙ B
-- -- theF B X x Y y A = _∘∙ myG B X x Y y A

-- -- myGβ : ∀ {ℓ ℓ'} (B : Pointed ℓ)
-- --   (X : RP∞) (x : fst X)
-- --   (Y : RP∞) (y : fst Y)
-- --   (A : fst X → fst Y → Pointed ℓ')
-- --   (f : (x : fst X) (y : fst Y) → A x y .fst)
-- --   → myG B X x Y y A .fst (proj (proj (f _ _) (f _ _)) (proj (f _ _) (f _ _)))
-- --     ≡ inr (λ x → inr λ y → f x y)
-- -- myGβ {ℓ} {ℓ'} B = J2-elem _ .fst (J2-elem _ .fst
-- --   λ A f → t A _
-- --         ∙ cong (Iso.fun (Iso-Smash-SM' {A = λ x → SM∙ Bool* (A x)}))
-- --                (λ i → proj (l1 A f i) (l2 A f i))
-- --         ∙ cong (inr* A) (funExt λ { false → transportRefl (inr (f false))
-- --                                   ; true → transportRefl (inr (f true))}))
-- --   where
-- --   inr* : (A : Bool → Bool → Pointed _) → _ → SM Bool* (λ x → SM∙ Bool* (A x))
-- --   inr* A = inr
-- --   module _ (A : fst Bool* → fst Bool* → Pointed ℓ')
-- --            (f : (x y : fst Bool*) → A x y .fst) where
-- --     l1 : Iso.fun (Iso-Smash-SM' {A = A false})
-- --           (proj (f false false) (f false true))
-- --        ≡ inr (f false)
-- --     l1  = Iso-Smash-SM'-proj' (f false)

-- --     l2 : Iso.fun (Iso-Smash-SM' {A = A true})
-- --           (proj (f true false) (f true true))
-- --        ≡ inr (f true)
-- --     l2 = Iso-Smash-SM'-proj' (f true)

-- --   help : myG B Bool* true ≡ myG-inner B
-- --   help = J2-elem (λ X x → (Y : RP∞) (y : fst Y)
-- --       (A : fst X → fst Y → Pointed ℓ') →
-- --       BIG X Y A x y →∙ SM∙ X (λ x₁ → SM∙ Y (A x₁)))
-- --       .snd (myG-inner B)
-- --       ∙ refl

-- --   help2 : myG-inner B Bool* true ≡ myG-innerest B
-- --   help2 = J2-elem (λ Y y → (A : fst Bool* → fst Y → Pointed ℓ') →
-- --       BIG Bool* Y A true y →∙ SM∙ Bool* (λ x₁ → SM∙ Y (A x₁))) .snd
-- --       (myG-innerest B)

-- --   t : (A : _) (z : _) → myG B Bool* true Bool* true A .fst z
-- --                       ≡  myG-innerest B A .fst z
-- --   t A z = (λ i → help i Bool* true A .fst z) ∙ (λ i → help2 i A .fst z)

-- -- theF-real : ∀ {ℓ ℓ'} (B : Pointed ℓ)
-- --   (X Y : RP∞)
-- --   (A : fst X → fst Y → Pointed ℓ')
-- --   → (SM∙ X (λ x → SM∙ Y (A x)) →∙ B)
-- --   → ((x : fst X) (y : fst Y) → BIG X Y A x y →∙ B)
-- -- theF-real B X Y A f x y = theF B X x Y y A f

-- -- theF-real-β : ∀ {ℓ ℓ'} (B : Pointed ℓ)
-- --   (X : RP∞) (Y : RP∞)
-- --   (A : fst X → fst Y → Pointed ℓ')
-- --   (r : _)
-- --   (f : (x : fst X) (y : fst Y) → A x y .fst)
-- --   (x : fst X) (y : fst Y)
-- --   → theF-real B X Y A r x y .fst ((proj (proj (f _ _) (f _ _)) (proj (f _ _) (f _ _))))
-- --   ≡ fst r (inr (λ x → inr λ y → f x y))
-- -- theF-real-β B X Y A r f x y = cong (fst r) (myGβ B X x Y y A f)

-- -- data _** (X : RP∞) : Type where
-- --   [[_]] : fst X → X **
-- --   sq : (x : fst X) → [[ x ]] ≡ [[ not* X x ]]

-- -- module _ (A : Bool* ** → Pointed₀) (ppp : (x : _) → PathP (λ i → A [[ notnot x (~ i) ]] .fst ≡ A [[ not x ]] .fst) (cong (fst ∘ A) (sq x)) (cong (fst ∘ A) (sym (sq (not x))))) where
-- --   module _ (Z : (x : _) → (fst (A x)) → Type) where
-- --     p1 : (a : _) (b : _) → PathP (λ i → (x : fst (A (sq false i))) → Z (sq false i) x) a b
-- --                          → PathP (λ i → (x : fst (A (sq true (~ i)))) → Z (sq true (~ i)) x) a b
-- --     p1 a b Q = toPathP (funExt λ x → {!!} ∙ {!!})

-- --     FF : S¹ → Bool* **
-- --     FF base = [[ true ]]
-- --     FF (loop i) = (sq true ∙ sq false) i

-- --     FF* : Bool* ** → S¹
-- --     FF* [[ false ]] = base
-- --     FF* [[ true ]] = base
-- --     FF* (sq false i) = loop i
-- --     FF* (sq true i) = base

-- --     Is1 : Iso (Bool* **) S¹
-- --     Iso.fun Is1 = FF*
-- --     Iso.inv Is1 = FF
-- --     Iso.rightInv Is1 base = refl
-- --     Iso.rightInv Is1 (loop i) j = (cong-∙ FF* (sq true) (sq false) ∙ sym (lUnit _)) j i 
-- --     Iso.leftInv Is1 [[ false ]] = sq true
-- --     Iso.leftInv Is1 [[ true ]] = refl
-- --     Iso.leftInv Is1 (sq false i) j = compPath-filler' (sq true) (sq false) (~ j) i
-- --     Iso.leftInv Is1 (sq true i) j = sq true (j ∧ i)

-- --     A* : (t : (x : _) → Z [[ true ]] x)
-- --        → PathP (λ i → (x : A ((sq true ∙ sq false) i) .fst) → Z ((sq true ∙ sq false) i) x) t t
-- --        → (x : _) (s : _)
-- --        → Z x s 
-- --     A* a b x s = {!!}

-- --     help1 : Iso ((x : _) (y : _) → Z x y)
-- --              (Σ[ a ∈ ((y : _) → Z [[ false ]] y) ]
-- --                Σ[ b ∈ ((y : _) → Z [[ true ]] y) ]
-- --                  PathP (λ i → (x : fst (A (sq false i))) → Z (sq false i) x) a b
-- --                × PathP (λ i → (x : fst (A (sq true i))) → Z (sq true i) x) b a)
-- --     help1 = {!!}
-- --   inda : (Z : (x : _) → (fst (A x)) → Type)
-- --        → ((x : _) → Z [[ false ]] x)
-- --        → (x : _) (y : _) → Z x y
-- --   inda Z a = {!!}

-- --   brs : (x : _) → (fst (A x)) → A [[ false ]] .fst
-- --   brs [[ false ]] p = p
-- --   brs [[ true ]] p = subst (fst ∘ A) (sq true) p
-- --   brs (sq false i) = h i
-- --     where
-- --     h : PathP (λ i → fst (A (sq false i)) → A [[ false ]] .fst) (idfun _) (subst (fst ∘ A) (sq true))
-- --     h = toPathP (funExt λ t → transportRefl _ ∙ {!!})
-- --   brs (sq true i) p = h i p
-- --     where
-- --     h : PathP (λ i → fst (A (sq true i)) → A [[ false ]] .fst) (subst (fst ∘ A) (sq true)) (idfun _)
-- --     h = {!!}

-- --   T : Iso (Σ _ (fst ∘ A)) (A [[ false ]] .fst)
-- --   Iso.fun T (x , p) = brs x p
-- --   Iso.inv T l = [[ false ]] , l
-- --   Iso.rightInv T l = refl
-- --   Iso.leftInv T = uncurry {!A* _ ? ?!}

-- -- -- BoolT : (A B : Type) → Bool → Type
-- -- -- BoolT A B false = A
-- -- -- BoolT A B true = B

-- -- -- data mYT (A : Bool → Pointed₀) (e : (x : _) → A x →∙ A (not x)) : Type where
-- -- --   constr : (x : Bool) → A x .fst → mYT A e
-- -- --   kil : (x : Bool) (r : A x .fst) → constr x r ≡ constr (not x) (e x .fst r)

-- -- -- hr : {!(A : Bool → Pointed₀) (e : (x : _) → A x →∙ A (not x)) → Σ[ x ∈ Bool ] ?!}
-- -- -- hr = {!!}

-- -- -- tte : (A : Bool → Type) → Iso (A false) (Σ[ F ∈ (Σ[ x ∈ Bool ] A x) ]
-- -- --   ((x : Bool) → {!F x ≡ ?!}))
-- -- -- tte = {!!}

-- -- -- my-gen-lem : {X : Type} (B C : Pointed₀) (A : X → Pointed₀) (e : (λ _ → B) ≡ A)
-- -- --   → (t : isEquiv {A = B →∙ C} {B = (x : X) → A x →∙ C}
-- -- --         λ f x → subst (_→∙ C) (funExt⁻ e x) f)

-- -- --   → (F : (x : X) → A x →∙ C)
-- -- --   → (b : fst B) (c : fst C)
-- -- --   → ((x : _) → F x .fst (transport (cong fst (funExt⁻ e x)) b) ≡ c)
-- -- --   → invEq (_ , t) F .fst b ≡ c
-- -- -- my-gen-lem {X = X} B C = J> transport (λ i → (t : isEquiv (λ f x → transportRefl f (~ i)))
-- -- --       (F : (x : X) → B →∙ C) (b : fst B) (c : fst C) →
-- -- --       ((x : X) →
-- -- --        F x .fst (transportRefl b (~ i)) ≡ c) →
-- -- --       invEq ((λ f x → transportRefl f (~ i)) , t) F .fst b ≡ c)
-- -- --         λ t f b → {!λ !}
-- -- --   where
-- -- --     module _ (t : isEquiv (λ (f : B →∙ C) (x : X) → f)) (F : X → B →∙ C) (b : fst B)
-- -- --       (c : fst C) where
-- -- --       h : isProp X
-- -- --       h x y = {!!}
-- -- --         where
-- -- --         f1 f2 : ((x₁ : X) → Σ (fst B → fst C) (λ f → f (snd B) ≡ snd C)) → B →∙ C
-- -- --         f1 F = F x
-- -- --         f2 F = F y

-- -- --         f1comp : invEq (_ , t) F ≡ F x
-- -- --         f1comp = {!!}

-- -- -- module _ {ℓ ℓ'} (B : Pointed ℓ) (isE : (X : _) (Y : _) (A : fst X → fst Y → Pointed ℓ') → isEquiv (theF-real B X Y A)) where
-- -- --   isEq* : (X : RP∞) (Y : RP∞) (A : fst X → fst Y → Pointed ℓ')
-- -- --     → (F : ((x : fst X) (y : fst Y) → BIG X Y A x y →∙ B))
-- -- --     → (f : (x : fst X) (y : fst Y) → A x y .fst)
-- -- --     → (b : fst B)
-- -- --     → Path (fst X → fst Y → _)
-- -- --          (λ x y → F x y .fst (((proj (proj (f _ _) (f _ _)) (proj (f _ _) (f _ _))))))
-- -- --          (λ _ _ → pt B)
-- -- --     → invEq (_ , isE X Y A) F .fst ((inr (λ x → inr λ y → f x y))) ≡ b
-- -- --   isEq* X Y A F f b p = {!p!} ∙ {!!}
-- -- --     where
-- -- --     G = invEq (_ , isE X Y A) F

-- -- --     h : F ≡ theF-real B X Y A G
-- -- --     h = sym (secEq (_ , isE X Y A) F)


-- -- -- module _ (X Y : RP∞) (A : fst X → fst Y → Pointed₀) where
-- -- --   -- →∙not² : (x : fst X) → A x →∙ A (not* X (not* X x))
-- -- --   -- fst (→∙not² x) = subst (fst ∘ A) (sym (not*not* X x))
-- -- --   -- snd (→∙not² x) = ?

-- -- --   Big : (x : fst X) (y : fst Y) → Pointed₀
-- -- --   Big x y = Smash∙ (Smash∙ (A x y) (A (not* X x) y))
-- -- --                    (Smash∙ (A x (not* Y y)) (A (not* X x) (not* Y y)))

-- -- --   SMFD : (B : Pointed₀) → Type
-- -- --   SMFD B = Σ[ f ∈ ((x : fst X) (y : fst Y)
-- -- --          → Big x y
-- -- --          →∙ B) ]
-- -- --     ∥ ((x : fst X) (y : fst Y) → ¬ f x y ≡ const∙ _ _) ∥₁

-- -- --   SM-non-const' : (B : Pointed₀) → Type
-- -- --   SM-non-const' B = Σ[ f ∈ SM∙ X (λ x → SM∙ Y (A x)) →∙ B ] ¬ f ≡ const∙ _ _

-- -- --   module _ (B : Pointed₀) (st : (x : fst X) (y : fst Y) → isSet (Big x y →∙ B))
-- -- --            (ispr : (x : fst X) (y : fst Y)
-- -- --            → isProp (Σ[ f ∈ (Big x y →∙ B) ] ¬ f ≡ const∙ _ B))
-- -- --            (hom : isHomogeneous B)
-- -- --            where

-- -- --     isPropSMFD : isProp (SMFD B)
-- -- --     isPropSMFD (f , p) (g , q) = Σ≡Prop (λ _ → squash₁)
-- -- --       (funExt λ x → funExt λ y → cong fst (ispr x y (f' x y) (g' x y)))
-- -- --       where
-- -- --       f' g' : (x : fst X) (y : fst Y) → Σ[ f ∈ (Big x y →∙ B) ] ¬ f ≡ const∙ _ B
-- -- --       f' x y = (f x y) , (λ t → PT.rec (λ {()}) (λ r → r x y t) p)
-- -- --       g' x y = g x y , λ t → PT.rec (λ {()}) (λ r → r x y t) q

-- -- --     G : (f : SM∙ X (λ x₁ → SM∙ Y (A x₁)) →∙ B)
-- -- --       → {!isHomogeneous→∙!}
-- -- --       → {!!}
-- -- --     G = {!!}

-- -- -- module _ (X : RP∞) (A : fst X → Pointed₀) where
-- -- --   →∙not² : (x : fst X) → A x →∙ A (not* X (not* X x))
-- -- --   fst (→∙not² x) = subst (fst ∘ A) (sym (not*not* X x))
-- -- --   snd (→∙not² x) j =
-- -- --     transp (λ i → fst (A (not*not* X x (~ i ∧ ~ j)))) j (snd (A (not*not* X x (~ j))))

-- -- --   SMF : (B : Pointed₀) → Type
-- -- --   SMF B = Σ[ f ∈ ((x : fst X) → Smash∙ (A x) (A (not* X x)) →∙ B) ]
-- -- --     ∥ ((x : fst X) → ¬ f x ≡ const∙ _ _) ∥₁

-- -- --   SM-non-const : (B : Pointed₀) → Type
-- -- --   SM-non-const B = Σ[ f ∈ (SM X A , inr λ x → A x .snd) →∙ B ] ¬ f ≡ const∙ _ _

-- -- --   module _ (B : Pointed₀) (st : (x : fst X) → isSet (Smash∙ (A x) (A (not* X x)) →∙ B))
-- -- --            (homl : (A B C : Pointed₀)
-- -- --           (f g : Smash∙ A B →∙ C)
-- -- --        → isHomogeneous C
-- -- --        → (((x : fst A) (y : fst B) → fst f (proj x y) ≡ fst g (proj x y)))
-- -- --        → f ≡ g)
-- -- --            (ispr : (x : fst X)
-- -- --            → isProp (Σ[ f ∈ (Smash∙ (A x) (A (not* X x)) →∙ B) ] ¬ f ≡ const∙ _ B))
-- -- --            (hom : isHomogeneous B)
-- -- --            where
-- -- --     isPropSMF : isProp (SMF B)
-- -- --     isPropSMF (f , p) (g , q) = Σ≡Prop (λ _ → squash₁) (funExt λ x → cong fst (ispr x (f' x) (g' x)))
-- -- --       where
-- -- --       f' g' : (x : fst X) → Σ[ f ∈ (Smash∙ (A x) (A (not* X x)) →∙ B) ] ¬ f ≡ const∙ _ B
-- -- --       f' x = (f x) , (PT.rec (isProp¬ _) (λ a → a x) p)
-- -- --       g' x = (g x) , (PT.rec (isProp¬ _) (λ a → a x) q)

-- -- --     St : SM-non-const B → SMF B
-- -- --     St (f , q) = (λ x → (λ { basel → pt B ; baser → pt B
-- -- --                            ; (proj a b) → fst f (inr (CasesRP X x a b))
-- -- --                            ; (gluel a i) → (cong (fst f) (sym (push (x , a)) ∙ push (x , pt (A x)))
-- -- --                                           ∙ {!snd f!}) i
-- -- --                            ; (gluer b i) → {!!}}) , refl)
-- -- --                 , {!!}

-- -- -- -- RPpt→BoolEquiv : {!!}
-- -- -- -- RPpt→BoolEquiv = {!!}


-- -- -- -- pss : (X : RP∞) (x : fst X) (Y : RP∞) (A : fst X → fst Y → Pointed₀)
-- -- -- --   → (Smash∙ (SM∙ Y (A x)) (SM∙ Y (A (not* X x))) →∙ SM∙ Y λ y → SM∙ X λ x → A x y)
-- -- -- -- pss = J2-elem _ .fst λ Y A
-- -- -- --   → (λ { basel → inr λ y → inl true
-- -- -- --         ; baser → inr λ y → inl false
-- -- -- --         ; (proj x y) → h Y A x y
-- -- -- --         ; (gluel (inl x) i) → {!!}
-- -- -- --         ; (gluel (inr x) i) → {!!}
-- -- -- --         ; (gluel (push a i₁) i) → {!!}
-- -- -- --         ; (gluer b i) → {!!}}) , {!refl!}
-- -- -- --   where
-- -- -- --   module _ (Y : RP∞) (A : fst Bool* → fst Y → Pointed₀) where
-- -- -- --     g-mid : (f : (x : fst Y) → A true x .fst)
-- -- -- --             (g : (x : fst Y) → A false x .fst)
-- -- -- --             (y : fst Y) (x : Bool) → A x y .fst
-- -- -- --     g-mid f g y false = g y
-- -- -- --     g-mid f g y true = f y

-- -- -- --     g : (f : (x : fst Y) → A true x .fst)
-- -- -- --       → SM Y (A false) → SM Y (λ y₁ → SM∙ Bool* (λ x₁ → A x₁ y₁))
-- -- -- --     g f (inl x) = inl x
-- -- -- --     g f (inr g) = inr (λ y → inr (g-mid f g y))
-- -- -- --     g f (push (y , g) i) =
-- -- -- --         (push (y , (inr (CasesRP Bool* true (f y) g)))
-- -- -- --       ∙ λ i → inr ((h ∙ F≡) (~ i))) i
-- -- -- --       where
-- -- -- --       inr* : (y₁ : fst Y) →  _ → SM Bool* (λ x₁ → A x₁ y₁)
-- -- -- --       inr* y₁ = inr

-- -- -- --       F : ((y₁ : fst Y) → SM Bool* (λ x₁ → A x₁ y₁))
-- -- -- --       F = (CasesRP Y {A = λ y₁ → SM Bool* (λ x₁ → A x₁ y₁)} y
-- -- -- --                      (inr (CasesRP Bool* true (f y) g))
-- -- -- --                      (inr (CasesRP Bool* true (f (not* Y y)) (A _ _ .snd))))

-- -- -- --       F≡ : F ≡ CasesRP Y {A = λ y₁ → SM Bool* (λ x₁ → A x₁ y₁)} y
-- -- -- --                      (inr (CasesRP Bool* true (f y) g))
-- -- -- --                      (inr (λ x → A x (not* Y y) .snd))
-- -- -- --       F≡ = funExt (λ z → CasesRP≡ Y y z refl (sym (push (true , (f (not* Y y))))
-- -- -- --                   ∙ push (true , A true (not* Y y) .snd)
-- -- -- --                   ∙ cong (inr* (not* Y y))
-- -- -- --                   (funExt λ { false → transportRefl (A false _ .snd)
-- -- -- --                             ; true → transportRefl (A true _ .snd)})))


-- -- -- --       h : Path ((y₁ : fst Y)
-- -- -- --         → SM Bool* (λ x₁ → A x₁ y₁))
-- -- -- --             (λ y₁ → inr (g-mid f
-- -- -- --                       (CasesRP Y y g (snd (A false (not* Y y)))) y₁))
-- -- -- --                F
-- -- -- --       h = funExt (CasesRP Y y (cong (inr* y)
-- -- -- --             (funExt (λ { false → CasesRPβ Y {A = λ y → fst (A false y)}
-- -- -- --                                    y g (snd (A false (not* Y y))) .fst
-- -- -- --                        ; true → refl}))
-- -- -- --             ∙ sym ((CasesRPβ Y {A = λ y₁ → SM Bool* (λ x₁ → A x₁ y₁)} y
-- -- -- --                  (inr λ { false → g ; true → f y})
-- -- -- --                  (inr (λ { false → A false _ .snd ; true → f (not* Y y)}))) .fst)
-- -- -- --             ∙ CasesRP≡ Y y _ (cong (inr* y)
-- -- -- --                                (funExt (λ { false → sym (transportRefl g)
-- -- -- --                                           ; true → sym (transportRefl (f y))})))
-- -- -- --                              (cong (inr* (not* Y y))
-- -- -- --                                (funExt (λ { false → sym (transportRefl (A false _ .snd))
-- -- -- --                                           ; true → sym (transportRefl (f (not* Y y)))}))))
-- -- -- --                  (cong (inr* (not* Y y)) (funExt (λ { false → CasesRPβ Y {A = λ y → A false y .fst} y g (snd (A false (not* Y y))) .snd
-- -- -- --                                                     ; true → refl}))
-- -- -- --                ∙∙ sym ((CasesRPβ Y {A = λ y₁ → SM Bool* (λ x₁ → A x₁ y₁)} y
-- -- -- --                  (inr λ { false → g ; true → f y})
-- -- -- --                  (inr (λ { false → A false _ .snd ; true → f (not* Y y)}))) .snd)
-- -- -- --                ∙∙ CasesRP≡ Y y _ (cong (inr* y) (funExt (λ { false → sym (transportRefl g)
-- -- -- --                                                            ; true → sym (transportRefl (f y))})))
-- -- -- --                                  (cong (inr* (not* Y y))
-- -- -- --                                    (funExt (λ { false → sym (transportRefl (A _ _ .snd))
-- -- -- --                                               ; true → sym (transportRefl (f (not* Y y)))})))))

-- -- -- --     F* G* : (y' : fst Y) (f : fst (A true y')) → (x : typ (SM∙ Y (A true))) → SM∙ Y (A false) →∙ (SM∙ Y (λ y₁ → SM∙ Bool* (λ x₁ → A x₁ y₁)))
-- -- -- --     F* y' f x = (λ _ → inl y') , (push (y' , (inr (λ x → A x y' .snd)))
-- -- -- --                                 ∙ {!!}
-- -- -- --                                 ∙ {!!})
-- -- -- --       where
-- -- -- --       f* : {!!}
-- -- -- --       f* = {!!}
-- -- -- --     G* y' f x = {!!}

-- -- -- --     h : typ (SM∙ Y (A true)) → typ (SM∙ Y (A false)) → SM Y (λ y₁ → SM∙ Bool* (λ x₁ → A x₁ y₁))
-- -- -- --     h (inl x) y = inl x
-- -- -- --     h (inr f) y = g f y
-- -- -- --     h (push (y' , f) i) (inl x) = {!!}
-- -- -- --     h (push (y' , f) i) (inr x) = {!!}
-- -- -- --     h (push (y' , f) i) (push a i₁) = {!!}
-- -- -- -- {-
-- -- -- --   → (λ { basel → inr λ y → inl true ; baser → inr λ y → inl false
-- -- -- --        ; (proj (inl x) g) → inl x
-- -- -- --        ; (proj (inr f) (inl x)) → inl x
-- -- -- --        ; (proj (inr f) (inr g)) → inr λ y → inr λ { false → g y ; true → f y}
-- -- -- --        ; (proj (inr f) (push a i)) → {!!}
-- -- -- --        ; (proj (push a i) g) → {!!}
-- -- -- --        ; (gluel a i) → {!!}
-- -- -- --        ; (gluer b i) → {!!}}) , {!!} -}


-- -- -- -- -- ∑∑RP : (X Y : RP∞) (n : fst X → fst Y → ℕ) → ℕ
-- -- -- -- -- ∑∑RP = uncurry λ X
-- -- -- -- --   → rec→Set
-- -- -- -- --        (isSetΠ2 (λ _ _ → isSetℕ))
-- -- -- -- --        (λ e → λ Y n → ∑RP Y (n (invEq e false)) + ∑RP Y (n (invEq e true)))
-- -- -- -- --        (EquivJ (λ X e → (y : X ≃ Bool) →
-- -- -- -- --       (λ (Y : RP∞) (n : X → fst Y → ℕ)
-- -- -- -- --         → ∑RP Y (n (invEq e false)) + ∑RP Y (n (invEq e true))) ≡
-- -- -- -- --       (λ Y n → ∑RP Y (n (invEq y false)) + ∑RP Y (n (invEq y true))))
-- -- -- -- --       (BoolAutoElim refl
-- -- -- -- --         (funExt λ Y → funExt λ n
-- -- -- -- --           → +-comm _ _)))


-- -- -- -- -- gen⋁ : {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ)
-- -- -- -- --   → Type ℓ
-- -- -- -- -- gen⋁ X A = cofib {B = Σ (fst X) (fst ∘ A)} λ x → x , pt (A x)

-- -- -- -- -- gen⋁-comm : {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Pointed ℓ)
-- -- -- -- --   → gen⋁ X (λ x → gen⋁ Y (A x) , inl tt) → gen⋁ Y (λ y → gen⋁ X (λ x → A x y) , inl tt)
-- -- -- -- -- gen⋁-comm X Y A (inl x) = inl tt
-- -- -- -- -- gen⋁-comm X Y A (inr (x , inl y)) = inl tt
-- -- -- -- -- gen⋁-comm X Y A (inr (x , inr (y , z))) = inr (y , inr (x , z))
-- -- -- -- -- gen⋁-comm X Y A (inr (x , push a i)) = (push a ∙ λ i → inr (a , push x i)) i
-- -- -- -- -- gen⋁-comm X Y A (push a i) = inl tt

-- -- -- -- -- gen⋁-comm* : {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Pointed ℓ)
-- -- -- -- --   → Iso (gen⋁ X (λ x → gen⋁ Y (A x) , inl tt)) (gen⋁ Y (λ y → gen⋁ X (λ x → A x y) , inl tt))
-- -- -- -- -- Iso.fun (gen⋁-comm* X Y A) = gen⋁-comm X Y A
-- -- -- -- -- Iso.inv (gen⋁-comm* X Y A) = gen⋁-comm Y X λ y x → A x y
-- -- -- -- -- Iso.rightInv (gen⋁-comm* X Y A) (inl x) = refl
-- -- -- -- -- Iso.rightInv (gen⋁-comm* X Y A) (inr (x , inl x₁)) = push x
-- -- -- -- -- Iso.rightInv (gen⋁-comm* X Y A) (inr (x , inr x₁)) = refl
-- -- -- -- -- Iso.rightInv (gen⋁-comm* {ℓ} X Y A) (inr (x , push a i)) j = help j i
-- -- -- -- --   where
-- -- -- -- --   help : PathP (λ i → Path (gen⋁ Y (λ y → gen⋁ X (λ x → A x y) , inl tt)) (push x i) (inr (x , inr (a , pt (A a x)))))
-- -- -- -- --                (cong (gen⋁-comm X Y A) (push a ∙ λ i → inr (a , push x i)))
-- -- -- -- --                (λ i → inr (x , push a i))
-- -- -- -- --   help = (cong-∙ (gen⋁-comm X Y A) (push a) (λ i₁ → inr (a , push x i₁))
-- -- -- -- --        ∙ sym (lUnit _)
-- -- -- -- --        ∙ refl)
-- -- -- -- --        ◁ (λ i j → compPath-filler' {ℓ} {gen⋁ Y (λ y → gen⋁ X (λ x → A x y) , inl tt)}
-- -- -- -- --            (push x) (λ i₁ → inr (x , push a i₁)) (~ i) j)
-- -- -- -- -- Iso.rightInv (gen⋁-comm* X Y A) (push a i) = λ j → push a (i ∧ j)
-- -- -- -- -- Iso.leftInv (gen⋁-comm* X Y A) = {!!}

-- -- -- -- -- module _ {X : Type} {A : X → X → Pointed₀} (B : (x y : X) → A x y →∙ A y x)
-- -- -- -- --   (hom : (x y : X) → isHomogeneous (A x y))
-- -- -- -- --   (Bid : (x y : X) → (B y x ∘∙ B x y) ≡ id∙ _) where
-- -- -- -- --   TT : {!isProp ?!}
-- -- -- -- --   TT = {!!}

-- -- -- -- -- test2 : (X : RP∞) → (fst X × ℕ) → (fst X → ℕ)
-- -- -- -- -- test2 = {!!}

-- -- -- -- -- module _  {A : Type} (_+A_ : A → A → A)
-- -- -- -- --   (isEq+ : (x : A) → isEquiv (x +A_))
-- -- -- -- --   (is-comm : (x y : A) → x +A y ≡ y +A x)
-- -- -- -- --   (⋆ : A)
-- -- -- -- --   (rid : (x : A) → x +A ⋆ ≡ x)
-- -- -- -- --   (lid : (x : A) → ⋆ +A x ≡ x)
-- -- -- -- --   (rlid : lid ⋆ ≡ rid ⋆) where

-- -- -- -- --   +Eq : A → A ≃ A
-- -- -- -- --   +Eq x = (x +A_) , (isEq+ x)

-- -- -- -- --   B-gen : {!(x : A) → !}
-- -- -- -- --   B-gen = {!δ Δ ∇ !}
  
-- -- -- -- --   sf : (B : A → Type) (x : A) → PathP (λ i → ua (+Eq x) (~ i) → Type)
-- -- -- -- --                                        B
-- -- -- -- --                                        λ a → B (x +A a)
-- -- -- -- --   sf B x = toPathP (funExt λ a → cong B (transportRefl _))

-- -- -- -- --   thm : (B : A → Type) (x a : A) → B a → B (x +A a) 
-- -- -- -- --   thm B x a z = {!sf B x!}

-- -- -- -- -- module genSmash {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ)
-- -- -- -- --                 (f : (x : fst X) (a : fst (A x)) → (x : fst X) → A x .fst ) where
-- -- -- -- --   data ⋀∞gen  : Type ℓ where
-- -- -- -- --     proj : ((x : fst X) → A x .fst) → ⋀∞gen
-- -- -- -- --     base : fst X → ⋀∞gen
-- -- -- -- --     gl : (x : fst X) (a : fst (A x)) → proj (f x a) ≡ base x

-- -- -- -- --   proj* : ((x : fst X) → A x .fst) → ⋀∞gen
-- -- -- -- --   proj* = proj

-- -- -- -- -- module _ {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ) where
-- -- -- -- --   module M = genSmash X A (λ x a → CasesRP X {fst ∘ A} x a ((snd ∘ A) (not* X x)))
-- -- -- -- --   open M public renaming (⋀∞gen to ⋀∞)

-- -- -- -- --   ⋀∞∙ : Pointed _
-- -- -- -- --   fst ⋀∞∙ = ⋀∞
-- -- -- -- --   snd ⋀∞∙ = proj λ x → A x .snd


-- -- -- -- -- --
-- -- -- -- -- module _ {ℓ : Level} {A B C D : Pointed ℓ} where
-- -- -- -- --   data ×Smash : Type ℓ where
-- -- -- -- --     cent : ×Smash

-- -- -- -- --     ptsr : fst A → fst B → ×Smash
-- -- -- -- --     ptsl : fst C → fst D → ×Smash

-- -- -- -- --     centrl : (a : fst A) → ptsr a (pt B) ≡ cent
-- -- -- -- --     centrr : (b : fst B) → ptsr (pt A) b ≡ cent
-- -- -- -- --     centll : (c : fst C) → ptsl c (pt D) ≡ cent
-- -- -- -- --     centlr : (d : fst D) → ptsl (pt C) d ≡ cent

-- -- -- -- --     pts : fst A → fst B → fst C → fst D → ×Smash

-- -- -- -- --     gluell : (b : fst B) (c : fst C) (d : fst D) → pts (pt A) b c d ≡ ptsl c d
-- -- -- -- --     gluelr : (a : fst A) (c : fst C) (d : fst D) → pts a (pt B) c d ≡ ptsl c d

-- -- -- -- --     gluerl : (a : fst A) (b : fst B) (d : fst D) → pts a b (pt C) d ≡ ptsr a b
-- -- -- -- --     gluerr : (a : fst A) (b : fst B) (c : fst C) → pts a b c (pt D) ≡ ptsr a b

-- -- -- -- --     hgluell : (a : fst A) (c : fst C) → PathP (λ i → gluerr a (pt B) c i ≡ centll c i) (gluelr a c (pt D)) (centrl a)
-- -- -- -- --     hgluelr : (a : fst A) (d : fst D) → PathP (λ i → gluelr a (pt C) d i ≡ centrl a i) (gluerl a (pt B) d) (centlr d)
-- -- -- -- --     hgluerl : (b : fst B) (c : fst C) → PathP (λ i → gluell b c (pt D) i ≡ centrr b i) (gluerr (pt A) b c) (centll c)
-- -- -- -- --     hgluerr : (b : fst B) (d : fst D) → PathP (λ i → gluell b (pt C) d i ≡ centrr b i) (gluerl (pt A) b d) (centlr d)
    

-- -- -- -- -- tq : {!(!}
-- -- -- -- -- tq = {!!}
    
    

-- -- -- -- -- module _ {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Pointed ℓ) where
-- -- -- -- --   tr : {!{A : fst X → Type ℓ} ((x : fst X) → A x) → ?!}
-- -- -- -- --   tr = {!!}

-- -- -- -- --   TTT = ((x : fst X) → ⋀∞ Y (A x))
-- -- -- -- --   data ΠgenSmash* : Type ℓ where
-- -- -- -- --     [_]* : ((x : fst X) (y : fst Y) → A x y .fst) → ΠgenSmash* -- pts
-- -- -- -- --     cent : fst X → fst Y → ΠgenSmash*
-- -- -- -- --     bases : (x : fst X) → ((y : fst Y) → A x y .fst) → ΠgenSmash*
-- -- -- -- --     cenrs : (x : fst X) (y : fst Y) (a : A x y .fst) → bases x (CasesRP Y y a (A x (not* Y y) .snd)) ≡ cent x y
-- -- -- -- --     gluez : (x : fst X) (y : fst Y) (y' : fst Y) (aₗ : A x y .fst) (ar : A x (not* Y y) .fst) (a' : A (not* X x) y .fst) --  (f : (y : _) → A x y .fst) (a' : A (not* X x) y .fst)
-- -- -- -- --       → [ CasesRP X x (CasesRP Y y aₗ ar) (CasesRP Y y a' (A (not* X x) (not* Y y) .snd))  ]* ≡ bases x (CasesRP Y y aₗ ar)
-- -- -- -- --     gluez-coh : (x : fst X) (y : fst Y) (a : A x y .fst) (f : {!Σ[ y ∈ Y ] !} → {!!}) -- (b : A (not* X x) y .fst) (b : A (not* X x) (not* Y y) .fst)
-- -- -- -- --       → {!!} -- (gluez x y (CasesRP Y y a (A x (not* Y y) .snd)) a') {!!}
-- -- -- -- --     gluez-coh' : (x : fst X) (y : fst Y) (a : A x y .fst) (b : A (not* X x) (not* Y y) .fst)
-- -- -- -- --       → {!!} -- PathP (λ i → {!!} ≡ {!!}) (gluez x y {!!} {!!}) {!!} 

-- -- -- -- --       {-
-- -- -- -- --       a₀ 
-- -- -- -- --       -}
    

-- -- -- -- -- -- data unord {ℓ : Level} (X : RP∞) (A : fst X → Type ℓ) (B : Type ℓ) : Type ℓ where
-- -- -- -- -- --   killa : ((x : fst X) → A x → B) → unord X A B
-- -- -- -- -- --   bz : (B × B → B) → unord X A B


-- -- -- -- -- -- unordEq : {ℓ : Level} (X : RP∞) (A : fst X → Type ℓ) (a : (x : fst X) → A x)
-- -- -- -- -- --   → (a : (x : fst X) → A x) → Type
-- -- -- -- -- -- unordEq X A a a' = {!!}

-- -- -- -- -- -- gen* : (X : RP∞) (A : fst X → Type) (B : Type)
-- -- -- -- -- --   → (f : ((x : fst X) → A x) → B)
-- -- -- -- -- --   → Σ[ f ∈ ((x : fst X) → A x → A (not* X x) → B) ]
-- -- -- -- -- --       ((x : fst X) (a : A x) (a' : A (not* X x)) → Σ[ b ∈ B ] {!!}) -- → Σ[ g ∈ {!f x a a'!} ] {!!})
-- -- -- -- -- -- gen* = {!!}

-- -- -- -- -- -- 2CaseBool : {ℓ : Level} (A : Bool → Pointed ℓ)
-- -- -- -- -- --   → (x : Bool) → fst (A x) → (x₁ : Bool) → A x₁ .fst
-- -- -- -- -- -- 2CaseBool A false p false = p
-- -- -- -- -- -- 2CaseBool A false p true = A true .snd
-- -- -- -- -- -- 2CaseBool A true p false = A false .snd
-- -- -- -- -- -- 2CaseBool A true p true = p

-- -- -- -- -- -- data coeq {ℓ ℓ' : Level} (A : Type ℓ) (R : A → A → Type ℓ') : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- --   [_]' : A → coeq A R
-- -- -- -- -- --   eq/ : (a a' : A) → R a a' → [ a ]' ≡ [ a' ]'

-- -- -- -- -- -- open import Cubical.Data.Empty
-- -- -- -- -- -- push-rel : {A B C : Type} (f : A → B) (g : A → C) → B ⊎ C → B ⊎ C → Type
-- -- -- -- -- -- push-rel {C = C} f g (inl x) (inl x₁) = ⊥
-- -- -- -- -- -- push-rel {A = A} f g (inl b) (inr c) = Σ[ x ∈ A ] (f x ≡ b) × (g x ≡ c)
-- -- -- -- -- -- push-rel {C = C} f g (inr x) (inl x₁) = ⊥
-- -- -- -- -- -- push-rel {C = C} f g (inr x) (inr x₁) = ⊥

-- -- -- -- -- -- module _ {A B C : Type} {f : A → B} {g : A → C} where
-- -- -- -- -- --   private
-- -- -- -- -- --     t : Pushout f g → coeq (B ⊎ C) (push-rel f g)
-- -- -- -- -- --     t (inl x) = [ inl x ]'
-- -- -- -- -- --     t (inr x) = [ inr x ]'
-- -- -- -- -- --     t (push a i) = eq/ (inl (f a)) (inr (g a)) (a , (refl , refl)) i
-- -- -- -- -- --     s : coeq (B ⊎ C) (push-rel f g) → Pushout f g
-- -- -- -- -- --     s [ inl x ]' = inl x
-- -- -- -- -- --     s [ inr x ]' = inr x
-- -- -- -- -- --     s (eq/ (inl x₁) (inr x₂) x i) = (sym (cong inl (snd x .fst)) ∙∙ push (fst x) ∙∙ cong inr (snd x .snd)) i
-- -- -- -- -- --     s (eq/ (inr x₁) (inl x₂) () i)
-- -- -- -- -- --     s (eq/ (inr x₁) (inr x₂) () i)

  
-- -- -- -- -- --     Pushout≃Coeq : Iso (Pushout f g) (coeq (B ⊎ C) (push-rel f g))
-- -- -- -- -- --     Iso.fun Pushout≃Coeq = t
-- -- -- -- -- --     Iso.inv Pushout≃Coeq = s
-- -- -- -- -- --     Iso.rightInv Pushout≃Coeq [ inl x ]' = refl
-- -- -- -- -- --     Iso.rightInv Pushout≃Coeq [ inr x ]' = refl
-- -- -- -- -- --     Iso.rightInv Pushout≃Coeq (eq/ (inl x₁) (inr x₂) x i) = flipSquare (help x) i 
-- -- -- -- -- --       where
-- -- -- -- -- --       help : (x : _) → cong t (sym (cong inl (snd x .fst)) ∙∙ push (fst x) ∙∙ cong inr (snd x .snd)) ≡ eq/ (inl x₁) (inr x₂) x
-- -- -- -- -- --       help x = cong-∙∙ t (sym (cong inl (snd x .fst))) (push (fst x)) (cong inr (snd x .snd))
-- -- -- -- -- --              ∙ (λ i → (λ j → [ inl (snd x .fst (i ∨ ~ j)) ]')
-- -- -- -- -- --                     ∙∙ eq/ (inl (snd x .fst i)) (inr (snd x .snd i)) ((fst x) , ((λ j → snd x .fst (i ∧ j)) , ((λ j → snd x .snd (i ∧ j)))))
-- -- -- -- -- --                     ∙∙ λ j → [ inr (snd x .snd (i ∨ j)) ]')
-- -- -- -- -- --              ∙ sym (rUnit _)
-- -- -- -- -- --     Iso.rightInv Pushout≃Coeq (eq/ (inr x₁) (inl x₂) () i)
-- -- -- -- -- --     Iso.rightInv Pushout≃Coeq (eq/ (inr x₁) (inr x₂) () i)
-- -- -- -- -- --     Iso.leftInv Pushout≃Coeq (inl x) = refl
-- -- -- -- -- --     Iso.leftInv Pushout≃Coeq (inr x) = refl
-- -- -- -- -- --     Iso.leftInv Pushout≃Coeq (push a i) j = rUnit (push a) (~ j) i

-- -- -- -- -- -- {-
-- -- -- -- -- -- data SM {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ) : Type ℓ where
-- -- -- -- -- --   l : ((x : fst X) → A x .fst) → SM X A
-- -- -- -- -- --   r : {!!}
-- -- -- -- -- --   c : {!!}
-- -- -- -- -- -- -}
-- -- -- -- -- -- module _ {ℓ ℓ' : Level} (X : RP∞) (A : fst X → Type ℓ) (R : (x : fst X) → A x → A x → Type ℓ')
-- -- -- -- -- --   (coh₁ : (x : fst X) (f : ((x : fst X) → A x)) → f ≡ CasesRP X x (f x) (f (not* X x)) )
-- -- -- -- -- --   (coh₂ : (x : fst X) (f g : ((x : fst X) → A x)) → CasesRP X {A = A} x (g x) (f (not* X x)) ≡ CasesRP X (not* X x) (f (not* X x)) (g (not* X (not* X x))))
-- -- -- -- -- --   (coh₃ : (x : fst X) (g : ((x : fst X) → A x)) → g ≡ CasesRP X (not* X x) (g (not* X x)) (g (not* X (not* X x)))) where
-- -- -- -- -- --   data Π-coeq  : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- --     [_] : ((x : fst X) → A x) → Π-coeq
-- -- -- -- -- --     p : (x : fst X) (a a' : A x) (b : A (not* X x)) → R x a a' → [ CasesRP X x a b ] ≡ [ CasesRP X x a' b ]
-- -- -- -- -- --     -- alt: (f g : _) (x : _) → f x = g x → R (¬ x) (f (not x)) (g (not x)) → [ f ] ≡ [ g ]
-- -- -- -- -- --     q : (f g : (x : fst X) → A x) → ((x : fst X) → R x (f x) (g x)) → [ f ] ≡ [ g ]
-- -- -- -- -- --     q' : (x : fst X) (f g : (x : fst X) → A x) (r : ((x : fst X) → R x (f x) (g x)) )
-- -- -- -- -- --       → PathP (λ i → [ coh₁ x f i ] ≡ [ coh₃ x g i ]) (q f g r)
-- -- -- -- -- --                    (p x (f x) (g x) (f (not* X x)) (r x)
-- -- -- -- -- --                 ∙∙ cong [_] (coh₂ x f g)
-- -- -- -- -- --                 ∙∙ p (not* X x) (f (not* X x)) (g (not* X x)) (g (not* X (not* X x))) (r (not* X x)))

-- -- -- -- -- --   data Π-coeq'  : Type (ℓ-max ℓ ℓ') where
-- -- -- -- -- --     [_] : ((x : fst X) → A x) → Π-coeq'
-- -- -- -- -- --     zZz : (f g : (x : fst X) → A x) (x : _) → f x ≡ g x → R (not* X x) (f (not* X x)) (g (not* X x)) → [ f ] ≡ [ g ]
-- -- -- -- -- --     q : (f g : (x : fst X) → A x) → ((x : fst X) → R x (f x) (g x)) → [ f ] ≡ [ g ]
-- -- -- -- -- --     q' : (x : fst X) (f g : (x : fst X) → A x) (r : ((x : fst X) → R x (f x) (g x)) )
-- -- -- -- -- --       → PathP (λ i → {!!} ≡ {!!}) (q f g r) {!zZz f g x !} -- {- (x : fst X) (f g : (x : fst X) → A x) (r : ((x : fst X) → R x (f x) (g x)) )
 

-- -- -- -- -- -- SM : {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ) → Type ℓ
-- -- -- -- -- -- SM X A = Pushout {A = Σ (fst X) (fst ∘ A)} fst λ x → CasesRP X {A = fst ∘ A} (fst x) (snd x) (snd (A (not* X (fst x))))

-- -- -- -- -- -- module _ {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Pointed₀)
-- -- -- -- -- --   (c1 : _) (c2 : _) (c3 : _) where
-- -- -- -- -- --   F : (x : fst X) (y : fst Y) → (fst Y ⊎ ((x₁ : fst Y) → (fst ∘ A x) x₁)) → fst (A x y)
-- -- -- -- -- --   F x y (inl z) = snd (A x y)
-- -- -- -- -- --   F x y (inr z) = z y

-- -- -- -- -- --   F-lem : (x x* : fst X) (y y₁ y' : fst Y) (f : _)
-- -- -- -- -- --     → F x y₁ (CasesRP X {A = λ x → fst Y ⊎ ((y : fst Y) → fst (A x y))} x* {!inl y!} {!!} x) ≡ {!!} 
-- -- -- -- -- --   F-lem = {!!}

-- -- -- -- -- --   SM* : Π-coeq X _ (λ x → (push-rel fst (λ y → CasesRP Y {A = fst ∘ (A x)} (fst y) (snd y) (snd (A x (not* Y (fst y))))))) c1 c2 c3
-- -- -- -- -- --     → SM Y λ y → SM X (λ x → A x y) , inr λ x → A x y .snd
-- -- -- -- -- --   SM* [ f ] = inr λ y → inr λ x → F x y (f x)
-- -- -- -- -- --   SM* (p x (inl y) (inr f) G ((y' , r) , P , Q) i) = {!cool x y f G y' P r Q i!}
-- -- -- -- -- --     where
-- -- -- -- -- --     cool : (x : fst X) (y : fst Y) (f : (x' : _) → fst (A x x'))
-- -- -- -- -- --       → (G : fst Y ⊎ ((x₁ : fst Y) → (fst ∘ A (not* X x)) x₁))
-- -- -- -- -- --       → (y' : fst Y) (P : y' ≡ y) (y₁ : fst Y)
-- -- -- -- -- --       (r : fst (A x y'))
-- -- -- -- -- --       (Q : CasesRP Y y' r (snd (A x (not* Y y'))) ≡ f)
-- -- -- -- -- --       → Path (SM X (λ x₁ → A x₁ y₁))
-- -- -- -- -- --               (inr (λ x₁ → F x₁ y₁ (CasesRP X x (inl y) G x₁)))
-- -- -- -- -- --               (inr (λ x₁ → F x₁ y₁ (CasesRP X x (inr f) G x₁)))
-- -- -- -- -- --     cool x y f (inl x₁) y' P y₁ r Q = {!!} ∙∙ push (x , (f y₁)) ∙∙ {!f y'!}
-- -- -- -- -- --     cool x y f (inr x₁) y' P y₁ r Q = {!!} ∙ sym (push (x , (f y₁))) ∙ {!!} -- refl
-- -- -- -- -- --   SM* (p x (inr x₁) (inl x₂) G () i)
-- -- -- -- -- --   SM* (p x (inr x₁) (inr x₂) G () i)
-- -- -- -- -- --   SM* (q f g x i) = {!g!}
-- -- -- -- -- --   SM* (q' x f g r i i₁) = {!!}

-- -- -- -- -- -- TOSM : (X Y : RP∞) (A : fst X → fst Y → Pointed₀) → {!!}
-- -- -- -- -- -- TOSM = {!!}

-- -- -- -- -- -- module _ {ℓ : Level} (A : Bool → Pointed ℓ) where
-- -- -- -- -- --   open genSmash renaming (⋀∞gen to ⋀∞)
-- -- -- -- -- --   ⋀∞→Smash : ⋀∞ Bool* A (2CaseBool A)
-- -- -- -- -- --            → Smash (A true) (A false)
-- -- -- -- -- --   ⋀∞→Smash (proj f) = proj (f true) (f false)
-- -- -- -- -- --   ⋀∞→Smash (base false) = baser
-- -- -- -- -- --   ⋀∞→Smash (base true) = basel
-- -- -- -- -- --   ⋀∞→Smash (gl false a i) = gluer a i
-- -- -- -- -- --   ⋀∞→Smash (gl true a i) = gluel a i

-- -- -- -- -- --   toBool→ : (x : A true .fst) (y : A false .fst) → (x : Bool) → A x .fst
-- -- -- -- -- --   toBool→ x y false = y
-- -- -- -- -- --   toBool→ x y true = x

-- -- -- -- -- --   toBool→≡₁ : (x : A true .fst) → toBool→ x (pt (A false)) ≡ 2CaseBool A true x
-- -- -- -- -- --   toBool→≡₁ x = funExt λ { false → refl ; true → refl}

-- -- -- -- -- --   toBool→≡₂ : (x : A false .fst) → toBool→ (pt (A true)) x ≡ 2CaseBool A false x
-- -- -- -- -- --   toBool→≡₂ x = funExt λ { false → refl ; true → refl}

-- -- -- -- -- --   Smash→⋀∞ : Smash (A true) (A false)
-- -- -- -- -- --     → ⋀∞ Bool* A (2CaseBool A)
-- -- -- -- -- --   Smash→⋀∞ basel = base true
-- -- -- -- -- --   Smash→⋀∞ baser = base false
-- -- -- -- -- --   Smash→⋀∞ (proj x y) = proj (toBool→ x y)
-- -- -- -- -- --   Smash→⋀∞ (gluel a i) = ((λ i → proj (toBool→≡₁ a i)) ∙ gl true a) i
-- -- -- -- -- --   Smash→⋀∞ (gluer b i) = ((λ i → proj (toBool→≡₂ b i)) ∙ gl false b) i

-- -- -- -- -- --   Smash→⋀∞→Smash : (x : Smash (A true) (A false)) → ⋀∞→Smash (Smash→⋀∞ x) ≡ x
-- -- -- -- -- --   Smash→⋀∞→Smash basel = refl
-- -- -- -- -- --   Smash→⋀∞→Smash baser = refl
-- -- -- -- -- --   Smash→⋀∞→Smash (proj x y) = refl
-- -- -- -- -- --   Smash→⋀∞→Smash (gluel a i) j = help j i
-- -- -- -- -- --     where
-- -- -- -- -- --     help : cong (⋀∞→Smash) ((λ i → proj (toBool→≡₁ a i)) ∙ gl true a)
-- -- -- -- -- --          ≡ gluel a
-- -- -- -- -- --     help = cong-∙ ⋀∞→Smash (λ i → proj (toBool→≡₁ a i)) (gl true a)
-- -- -- -- -- --          ∙ sym (lUnit _)
-- -- -- -- -- --   Smash→⋀∞→Smash (gluer b i) j = help j i
-- -- -- -- -- --     where
-- -- -- -- -- --     help : cong (⋀∞→Smash) ((λ i → proj (toBool→≡₂ b i)) ∙ gl false b)
-- -- -- -- -- --          ≡ gluer b
-- -- -- -- -- --     help = cong-∙ ⋀∞→Smash (λ i → proj (toBool→≡₂ b i)) (gl false b)
-- -- -- -- -- --          ∙ sym (lUnit _)

-- -- -- -- -- --   toBool→diag : (f : ((x : Bool) → A x .fst))
-- -- -- -- -- --     →  (toBool→ (f true) (f false)) ≡ f
-- -- -- -- -- --   toBool→diag f = funExt λ { false → refl ; true → refl}

-- -- -- -- -- --   ⋀∞→Smash→⋀∞ : (x : ⋀∞ Bool* A (2CaseBool A))
-- -- -- -- -- --     → (Smash→⋀∞ (⋀∞→Smash x)) ≡ x
-- -- -- -- -- --   ⋀∞→Smash→⋀∞ (proj x) i = proj (toBool→diag x i)
-- -- -- -- -- --   ⋀∞→Smash→⋀∞ (base false) = refl
-- -- -- -- -- --   ⋀∞→Smash→⋀∞ (base true) = refl
-- -- -- -- -- --   ⋀∞→Smash→⋀∞ (gl false a i) j = lem j i
-- -- -- -- -- --     where
-- -- -- -- -- --     help' : toBool→diag (2CaseBool A false a) ≡ toBool→≡₂ a
-- -- -- -- -- --     help' = cong funExt (funExt λ { false → refl ; true → refl})


-- -- -- -- -- --     lem : PathP (λ j → Path (⋀∞ Bool* A (2CaseBool A))
-- -- -- -- -- --                              (proj (toBool→diag (2CaseBool A false a) j))
-- -- -- -- -- --                              (base false))
-- -- -- -- -- --                 (((λ i₁ → proj (toBool→≡₂ a i₁)) ∙ gl false a)) (gl false a)
-- -- -- -- -- --     lem = cong (_∙ gl false a) (λ i j → proj (help' (~ i) j))
-- -- -- -- -- --         ◁ λ i j → compPath-filler'
-- -- -- -- -- --           (λ i → proj (toBool→diag (2CaseBool A false a) i))
-- -- -- -- -- --           (gl false a) (~ i) j

-- -- -- -- -- --   ⋀∞→Smash→⋀∞ (gl true a i) j = lem j i
-- -- -- -- -- --     where
-- -- -- -- -- --     help' : toBool→diag (2CaseBool A true a) ≡ toBool→≡₁ a
-- -- -- -- -- --     help' = cong funExt (funExt λ { false → refl ; true → refl})


-- -- -- -- -- --     lem : PathP (λ j → Path (⋀∞ Bool* A (2CaseBool A))
-- -- -- -- -- --                              (proj (toBool→diag (2CaseBool A true a) j))
-- -- -- -- -- --                              (base true))
-- -- -- -- -- --                 (((λ i₁ → proj (toBool→≡₁ a i₁)) ∙ gl true a)) (gl true a)
-- -- -- -- -- --     lem = cong (_∙ gl true a) (λ i j → proj (help' (~ i) j))
-- -- -- -- -- --         ◁ λ i j → compPath-filler'
-- -- -- -- -- --           (λ i → proj (toBool→diag (2CaseBool A true a) i))
-- -- -- -- -- --           (gl true a) (~ i) j

-- -- -- -- -- --   ⋀∞≃Smash : Iso (⋀∞ Bool* A (2CaseBool A)) (Smash (A true) (A false))
-- -- -- -- -- --   Iso.fun ⋀∞≃Smash = ⋀∞→Smash
-- -- -- -- -- --   Iso.inv ⋀∞≃Smash = Smash→⋀∞
-- -- -- -- -- --   Iso.rightInv ⋀∞≃Smash = Smash→⋀∞→Smash
-- -- -- -- -- --   Iso.leftInv ⋀∞≃Smash = ⋀∞→Smash→⋀∞


-- -- -- -- -- -- myInd : {!∀ {ℓ} {A : Type ℓ} → ?!}
-- -- -- -- -- -- myInd = {!!}

-- -- -- -- -- -- pathF : {A : Type} (x y : A) → (B : x ≡ y → Pointed₀) → ((p : _) → B p .fst)
-- -- -- -- -- -- pathF {A = A} x y B p = transport (λ i → (B : x ≡ p i → Pointed₀) (q : _) → B q .fst) (λ B q → l2 x x q B) B p
-- -- -- -- -- --   where
-- -- -- -- -- --   l2 : (x y : A) (q : x ≡ y) (B : x ≡ y → Pointed₀) → B q .fst
-- -- -- -- -- --   l2 x = J> λ B → B refl .snd

-- -- -- -- -- -- data myDat {ℓ} (A : Bool → Type ℓ) : Type ℓ where
-- -- -- -- -- --   incl : Σ[ r ∈ Bool ] (A r × A (not r)) → myDat A
-- -- -- -- -- --   idr : (p : Σ[ r ∈ Bool ] (A r × A (not r)))
-- -- -- -- -- --     → incl p
-- -- -- -- -- --      ≡ incl ((not (fst p)) , ((p .snd .snd) , (subst A (sym (notnot (fst p))) (p .snd .fst))))

-- -- -- -- -- -- Σ-r : {A : Bool → Type} → Iso ((x : _) → A x) (myDat A)
-- -- -- -- -- -- Iso.fun Σ-r f = incl (true , ((f true) , (f false)))
-- -- -- -- -- -- Iso.inv Σ-r (incl (false , r , s)) false = r
-- -- -- -- -- -- Iso.inv Σ-r (incl (true , r , s)) false = s
-- -- -- -- -- -- Iso.inv Σ-r (incl (false , r , s)) true = s
-- -- -- -- -- -- Iso.inv Σ-r (incl (true , r , s)) true = r
-- -- -- -- -- -- Iso.inv Σ-r (idr (false , r , s) i) false = transportRefl r (~ i)
-- -- -- -- -- -- Iso.inv Σ-r (idr (true , r , s) i) false = s
-- -- -- -- -- -- Iso.inv Σ-r (idr (false , r , s) i) true = s
-- -- -- -- -- -- Iso.inv Σ-r (idr (true , r , s) i) true = transportRefl r (~ i)
-- -- -- -- -- -- Iso.rightInv Σ-r (incl (false , r , s)) = (λ i → incl (true , s , transportRefl r (~ i))) ∙ sym (idr (false , r , s)) -- idr (true , s , r) ∙ λ i → incl (false , r , transportRefl s i)
-- -- -- -- -- -- Iso.rightInv Σ-r (incl (true , r , s)) = refl
-- -- -- -- -- -- Iso.rightInv Σ-r (idr (false , r , s) i) j = {!!}
-- -- -- -- -- -- Iso.rightInv Σ-r (idr (true , r , s) i) j = {!!}
-- -- -- -- -- -- Iso.leftInv Σ-r f = {!!} -- funExt λ { false → refl ; true → refl}


-- -- -- -- -- -- module _ {ℓ : Level} (X : RP∞) (A : fst X → Pointed ℓ) where
-- -- -- -- -- --   module M = genSmash X A (λ x a → CasesRP X {fst ∘ A} x a ((snd ∘ A) (not* X x)))
-- -- -- -- -- --   open M public renaming (⋀∞gen to ⋀∞)

-- -- -- -- -- --   ⋀∞∙ : Pointed _
-- -- -- -- -- --   fst ⋀∞∙ = ⋀∞
-- -- -- -- -- --   snd ⋀∞∙ = proj λ x → A x .snd

-- -- -- -- -- -- ΣRP = Σ[ X ∈ RP∞ ] (Σ[ A ∈ (fst X → Pointed₀) ] ⋀∞ X A)

-- -- -- -- -- -- TTT : (e : RP∞ ≡ RP∞) (x : RP∞) → RP∞
-- -- -- -- -- -- TTT e = transport e



-- -- -- -- -- -- BOol× : (A : Bool → Type) → Iso ((x : Bool) → A x) (Σ[ x ∈ Bool ] (A x))
-- -- -- -- -- -- Iso.fun (BOol× A) f = {!!}
-- -- -- -- -- -- Iso.inv (BOol× A) = {!!}
-- -- -- -- -- -- Iso.rightInv (BOol× A) = {!!}
-- -- -- -- -- -- Iso.leftInv (BOol× A) = {!!}

-- -- -- -- -- -- T* : (e : RP∞ ≡ RP∞) → ΣRP ≡ ΣRP
-- -- -- -- -- -- T* e i = {!Σ[ X ∈ e i ] (Σ[ A ∈ (fst X → Pointed₀) ] ⋀∞ X A)!}
-- -- -- -- -- --   where
-- -- -- -- -- --   C : PathP (λ j → {!Σ[ !}) ((x : RP∞) → Pointed₀) ((x : RP∞) → Pointed₀)
-- -- -- -- -- --   C = {!!}

-- -- -- -- -- -- module _ {ℓ : Level} (X Y : RP∞) (A : fst X → fst Y → Pointed ℓ) where
-- -- -- -- -- --   F : ⋀∞∙ X (λ x → ⋀∞∙ Y (A x)) .fst → ⋀∞∙ Y (λ y → ⋀∞∙ X (λ x → A x y)) .fst
-- -- -- -- -- --   F (genSmash.proj f) = proj λ y → {!!}
-- -- -- -- -- --   F (genSmash.base x) = {!!}
-- -- -- -- -- --   F (genSmash.gl x a i) = {!!}

-- -- -- -- -- -- -- -- anId : {ℓ : Level} (A : Bool → Pointed ℓ)
-- -- -- -- -- -- -- --   → Path ((x : Bool) (a : fst (A x)) → (x : Bool) → A x .fst)
-- -- -- -- -- -- -- --           (λ x a → CasesRP Bool* {fst ∘ A} x a ((snd ∘ A) (not* Bool* x)))
-- -- -- -- -- -- -- --           (2CaseBool A)
-- -- -- -- -- -- -- -- anId A =
-- -- -- -- -- -- -- --   funExt λ { false → funExt λ a
-- -- -- -- -- -- -- --     → funExt λ { false → transportRefl a
-- -- -- -- -- -- -- --                 ; true → transportRefl (A true .snd)}
-- -- -- -- -- -- -- --                 ; true → funExt λ a
-- -- -- -- -- -- -- --          → funExt λ { false → transportRefl (A false .snd)
-- -- -- -- -- -- -- --                      ; true → transportRefl a}}

-- -- -- -- -- -- -- -- Iso-⋀∞Bool : ∀ {ℓ} (A : Bool → Pointed ℓ)
-- -- -- -- -- -- -- --   → Iso (⋀∞ Bool* A) (Smash (A true) (A false))
-- -- -- -- -- -- -- -- Iso-⋀∞Bool A =
-- -- -- -- -- -- -- --   compIso (pathToIso (cong (genSmash.⋀∞gen Bool* A) (anId A))) (⋀∞≃Smash A)

-- -- -- -- -- -- -- -- Iso-⋀∞Bool-funId : ∀ {ℓ} (A : Bool → Pointed ℓ)
-- -- -- -- -- -- -- --   (e : (x : fst Bool*) → A x .fst)
-- -- -- -- -- -- -- --   → Iso.fun (Iso-⋀∞Bool A) (proj e) ≡ proj (e true) (e false)
-- -- -- -- -- -- -- -- Iso-⋀∞Bool-funId A e i = proj (transportRefl (e true) i) (transportRefl (e false) i)

-- -- -- -- -- -- -- -- Kgen : (X : RP∞) (n : fst X → ℕ) → Pointed₀
-- -- -- -- -- -- -- -- Kgen X n = EM∙ ℤ/2 (∑RP X n)

-- -- -- -- -- -- -- -- K∙ = EM∙ ℤ/2
-- -- -- -- -- -- -- -- K = EM ℤ/2

-- -- -- -- -- -- -- -- module _ (⌣gen : (X : RP∞) (n : fst X → ℕ)
-- -- -- -- -- -- -- --        → ⋀∞∙ X (λ x → K∙ (n x))
-- -- -- -- -- -- -- --        →∙ K∙ (∑RP X n)) where
-- -- -- -- -- -- -- --   module _ (X : RP∞) (n : fst X → ℕ) where
-- -- -- -- -- -- -- --     Πpt :  (((x : fst X) → K (n x)) , λ x → 0ₖ (n x)) →∙ K∙ (∑RP X n)
-- -- -- -- -- -- -- --     fst Πpt f = ⌣gen X n .fst (proj f)
-- -- -- -- -- -- -- --     snd Πpt = ⌣gen X n .snd

-- -- -- -- -- -- -- --   lem' : (n : ℕ) (X : RP∞) → ∑RP X (λ _ → n) ≡ n + n
-- -- -- -- -- -- -- --   lem' n = RP∞pt→Prop (λ _ → isSetℕ _ _) refl

-- -- -- -- -- -- -- --   Sq : (n : ℕ) → K n × RP∞ → K (n + n)
-- -- -- -- -- -- -- --   Sq n (x , t) = subst K (lem' n t) (Πpt t (λ _ → n) .fst λ _ → x)

-- -- -- -- -- -- -- --   genconst : (t : RP∞) (n : fst t → ℕ)
-- -- -- -- -- -- -- --     → ((x : fst t) → K (n x)) → K (∑RP t n)
-- -- -- -- -- -- -- --   genconst t n s = Πpt t n .fst s

-- -- -- -- -- -- -- --   doubler : (t s : RP∞) (n : fst t → fst s → ℕ)
-- -- -- -- -- -- -- --        (a : (x : fst t) (y : fst s) → K (n x y))
-- -- -- -- -- -- -- --     → K (∑RP t (λ z → ∑RP s (n z)))
-- -- -- -- -- -- -- --   doubler t s n a =
-- -- -- -- -- -- -- --     genconst t (λ z → ∑RP s (n z))
-- -- -- -- -- -- -- --        λ x → genconst s (n x) (a x)

-- -- -- -- -- -- -- --   S'S' : (X Y : RP∞) (n : fst X → fst Y → ℕ) → (x : fst X) (y : fst Y)
-- -- -- -- -- -- -- --     → (K∙ (n x y) ⋀∙ K∙ (n x (not* Y y))) ⋀ (K∙ (n (not* X x) y) ⋀∙ K∙ (n (not* X x) (not* Y y))) → K (∑RP X (λ x → ∑RP Y (n x))) 
-- -- -- -- -- -- -- --   S'S' X Y n x y (inl x₁) = {!!}
-- -- -- -- -- -- -- --   S'S' X Y n x y (inr (inl x₁ , b)) = {!!}
-- -- -- -- -- -- -- --   S'S' X Y n x y (inr (inr x₁ , inl x₂)) = {!!}
-- -- -- -- -- -- -- --   S'S' X Y n x y (inr (inr x₁ , inr x₂)) = Πpt X (λ x → ∑RP Y (n x)) .fst λ x' → Πpt Y (n x') .fst λ y → {!⌣gen X ? .fst ? .fst ?!} --  ⌣gen X (λ x → {!n x y!}) .fst (proj {!!})
-- -- -- -- -- -- -- --   S'S' X Y n x y (inr (inr x₁ , push a i)) = {!!}
-- -- -- -- -- -- -- --   S'S' X Y n x y (inr (push a i , b)) = {!!}
-- -- -- -- -- -- -- --   S'S' X Y n x y (push a i) = {!!}

-- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- --   SS : (X Y : RP∞) (n : fst X → fst Y → ℕ) → Pointed₀ 
-- -- -- -- -- -- -- --   SS X Y n = ⋀∞∙ X λ x → ⋀∞∙ Y λ y → K∙ (n x y)

-- -- -- -- -- -- -- --   SS' : (X Y : RP∞) (n : fst X → fst Y → ℕ) → Pointed₀ 
-- -- -- -- -- -- -- --   SS' X Y n = ⋀∞∙ Y λ y → ⋀∞∙ X λ x → K∙ (n x y)

-- -- -- -- -- -- -- --   test123 : (X : RP∞) (A : fst X → Pointed₀) → Susp (Susp (⋀∞ X A)) → ⋀∞ X (λ x → Susp∙ (fst (A x)))
-- -- -- -- -- -- -- --   test123 X A north = proj λ _ → north
-- -- -- -- -- -- -- --   test123 X A south = proj λ _ → south
-- -- -- -- -- -- -- --   test123 X A (merid north i) = {!!}
-- -- -- -- -- -- -- --   test123 X A (merid south i) = {!!}
-- -- -- -- -- -- -- --   test123 X A (merid (merid a i₁) i) = {!!}

-- -- -- -- -- -- -- --   SS→ : (X Y : RP∞) (n : fst X → fst Y → ℕ)
-- -- -- -- -- -- -- --     → SS X Y n .fst
-- -- -- -- -- -- -- --     → K (∑RP X (λ x → ∑RP Y (n x)))
-- -- -- -- -- -- -- --   SS→ X Y n (genSmash.proj f) =
-- -- -- -- -- -- -- --     genconst X (λ x → ∑RP Y (n x))
-- -- -- -- -- -- -- --       λ x → ⌣gen Y (n x) .fst (f x)
-- -- -- -- -- -- -- --   SS→ X Y n (genSmash.base x) = 0ₖ (∑RP X (λ x₁ → ∑RP Y (n x₁)))
-- -- -- -- -- -- -- --   SS→ X Y n (genSmash.gl x (genSmash.proj x₁) i) = {!!}
-- -- -- -- -- -- -- --   SS→ X Y n (genSmash.gl x (genSmash.base x₁) i) = {!!}
-- -- -- -- -- -- -- --   SS→ X Y n (genSmash.gl x (genSmash.gl x₁ a i) j) = {!!}

-- -- -- -- -- -- -- --   SS→* : (X Y : RP∞) (n : fst X → fst Y → ℕ)
-- -- -- -- -- -- -- --     → SS X Y n .fst
-- -- -- -- -- -- -- --     → K (∑RP Y (λ y → ∑RP X (λ x → n x y)))
-- -- -- -- -- -- -- --   SS→* X Y n (genSmash.proj x) =
-- -- -- -- -- -- -- --     ⌣gen Y (λ y → ∑RP X (λ x₁ → n x₁ y)) .fst
-- -- -- -- -- -- -- --       (proj λ y → {!x ?!})
-- -- -- -- -- -- -- --   SS→* X Y n (genSmash.base x) = {!!}
-- -- -- -- -- -- -- --   SS→* X Y n (genSmash.gl x a i) = {!!}

-- -- -- -- -- -- -- -- hPropFib : ∀ {ℓ} (X : RP∞) (A : fst X → fst X → Pointed ℓ)
-- -- -- -- -- -- -- --   → ((x y : _) → isProp (typ (A x y)))
-- -- -- -- -- -- -- --   → hProp ℓ
-- -- -- -- -- -- -- -- hPropFib = uncurry (λ X
-- -- -- -- -- -- -- --   → rec→Set {!!}
-- -- -- -- -- -- -- --     (λ e A pr → A (invEq e true) (invEq e false) .fst , {!!})
-- -- -- -- -- -- -- --     λ e g → funExt λ A → funExt λ z → Σ≡Prop {!!} {!!})
-- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- module _ (⌣gen : (X : RP∞) (n : fst X → ℕ)
-- -- -- -- -- -- -- --        → ⋀∞∙ X (λ x → K∙ (n x))
-- -- -- -- -- -- -- --        →∙ K∙ (∑RP X n)) where
-- -- -- -- -- -- -- --   h : (m : ℕ) (x : K m) (y y' : RP∞)
-- -- -- -- -- -- -- --     → Sq ⌣gen (m + m) ((Sq ⌣gen m (x , y')) , y)
-- -- -- -- -- -- -- --      ≡ Sq ⌣gen (m + m) ((Sq ⌣gen m (x , y)) , y')
-- -- -- -- -- -- -- --   h m x y y' = {!Πpt ⌣gen y (λ _ → m + m) .fst (λ _ → Sq ⌣gen m (x , y'))!}

-- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- SqA : (n : ℕ) → K n × RP∞ → K (n + n)
-- -- -- -- -- -- -- -- Sq n (x , t) = subst K (lem' n t) (Πpt t (λ _ → n) .fst λ _ → x)
-- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- flipBool : {X : Type₀} → X ≃ Bool → X ≃ Bool
-- -- -- -- -- -- -- -- -- flipBool e = compEquiv e notEquiv

-- -- -- -- -- -- -- -- -- notComm : (X : RP∞) (e : fst X ≃ Bool)
-- -- -- -- -- -- -- -- --   → not* X (invEq e true) ≡ invEq e false
-- -- -- -- -- -- -- -- -- notComm =
-- -- -- -- -- -- -- -- --   RP∞pt→Prop (λ X → isPropΠ λ _ → isSetRPpt X _ _)
-- -- -- -- -- -- -- -- --     λ e → {!funExt⁻ (cong fst (Iso.leftInv Bool≃Charac (invEquiv e))) x!} ∙∙ {!!} ∙∙ funExt⁻ (cong invEq (Iso.leftInv Bool≃Charac e)) false

-- -- -- -- -- -- -- -- -- liftHom : (X : RP∞) (A : fst X → Pointed₀) (C : Type)
-- -- -- -- -- -- -- -- --   → (e : fst X ≃ Bool)
-- -- -- -- -- -- -- -- --   → (((x : fst X) → A x .fst) → C)
-- -- -- -- -- -- -- -- --   → A (invEq e true) .fst → A (invEq e false) .fst → C
-- -- -- -- -- -- -- -- -- liftHom X A C e f x y =
-- -- -- -- -- -- -- -- --   f (CasesRP X (invEq e true) x (subst (fst ∘ A) (sym (notComm X e)) y))

-- -- -- -- -- -- -- -- -- test123 : (A B C : Pointed₀)
-- -- -- -- -- -- -- -- --   → Iso (A →∙ (B →∙ C ∙))
-- -- -- -- -- -- -- -- --       (Σ[ f ∈ (fst A → fst B → fst C) ]
-- -- -- -- -- -- -- -- --         Σ[ l ∈ ((x : fst A) → f x (pt B) ≡ pt C) ]
-- -- -- -- -- -- -- -- --           Σ[ r ∈ ((y : fst B) → f (pt A) y ≡ pt C) ]
-- -- -- -- -- -- -- -- --               PathP (λ i → r (pt B) i ≡ snd C)
-- -- -- -- -- -- -- -- --                (l (pt A)) (λ _ → pt C) )
-- -- -- -- -- -- -- -- -- Iso.fun (test123 A B C) f = (λ x y → f .fst x .fst y)
-- -- -- -- -- -- -- -- --                           , ((λ x → f .fst x .snd)
-- -- -- -- -- -- -- -- --                           , (λ y i → f .snd i .fst y)
-- -- -- -- -- -- -- -- --                           , cong snd (snd f))
-- -- -- -- -- -- -- -- -- Iso.inv (test123 A B C) = {!!}
-- -- -- -- -- -- -- -- -- Iso.rightInv (test123 A B C) = {!!}
-- -- -- -- -- -- -- -- -- Iso.leftInv (test123 A B C) = {!!}

-- -- -- -- -- -- -- -- -- ind* : (X : RP∞) → fst X → fst X ≃ Bool
-- -- -- -- -- -- -- -- -- ind* X x = isoToEquiv (iso (F⁻ X x) (F X x) (F-F X x .snd) (F-F X x .fst))
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   F : (X : RP∞) → fst X → Bool → fst X
-- -- -- -- -- -- -- -- --   F X x false = not* X x
-- -- -- -- -- -- -- -- --   F X x true = x

-- -- -- -- -- -- -- -- --   F⁻ : (X : RP∞) → fst X → fst X → Bool
-- -- -- -- -- -- -- -- --   F⁻ X x = CasesRP X x true false

-- -- -- -- -- -- -- -- --   F-F : (X : RP∞) (x : fst X) → ((y : fst X) → F X x (F⁻ X x y) ≡ y) × ((y : Bool) → F⁻ X x (F X x y) ≡ y)
-- -- -- -- -- -- -- -- --   F-F =
-- -- -- -- -- -- -- -- --     uncurry λ X → PT.elim (λ p
-- -- -- -- -- -- -- -- --       → isPropΠ λ _ → isProp× (isPropΠ (λ _ → isSetRPpt (X , p) _ _))
-- -- -- -- -- -- -- -- --          (isPropΠ (λ _ → isSetBool _ _)))
-- -- -- -- -- -- -- -- --       (EquivJ (λ X x₁ → (x₂ : X) → ((y : X) → F (X , ∣ x₁ ∣₁) x₂ (F⁻ (X , ∣ x₁ ∣₁) x₂ y) ≡ y) ×
-- -- -- -- -- -- -- -- --       ((y : Bool) → F⁻ (X , ∣ x₁ ∣₁) x₂ (F (X , ∣ x₁ ∣₁) x₂ y) ≡ y))
-- -- -- -- -- -- -- -- --         λ { false → (λ { false → refl ; true → refl}) , λ { false → refl ; true → refl}
-- -- -- -- -- -- -- -- --           ; true → (λ { false → refl ; true → refl}) , λ { false → refl ; true → refl}})

-- -- -- -- -- -- -- -- -- ind** : ∀ {ℓ} (A : (X : RP∞) → fst X → Type ℓ)
-- -- -- -- -- -- -- -- --   → Σ[ F ∈ (A Bool* true → (x : _) (y : _) → A x y) ] ((p : A Bool* true) → F p Bool* true ≡ p)
-- -- -- -- -- -- -- -- -- ind** A = (λ p x y → subst A' (sym (Path1 x y)) p)
-- -- -- -- -- -- -- -- --         , λ p → cong (λ x → subst A' (sym x) p) Path1≡refl ∙ transportRefl p
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   help : (x : RP∞) (y : fst x) → x ≡ Bool*
-- -- -- -- -- -- -- -- --   help x y = Σ≡Prop (λ _ → squash₁) (ua (ind* x y))

-- -- -- -- -- -- -- -- --   ind*-lem : ind* Bool* true ≡ idEquiv _
-- -- -- -- -- -- -- -- --   ind*-lem = Σ≡Prop isPropIsEquiv (funExt λ { false → refl ; true → refl})

-- -- -- -- -- -- -- -- --   abstract
-- -- -- -- -- -- -- -- --     help-base : help Bool* true ≡ refl 
-- -- -- -- -- -- -- -- --     help-base = (λ i → Σ≡Prop (λ _ → squash₁) (ua (ind*-lem i)))
-- -- -- -- -- -- -- -- --       ∙ ΣSquareSet (λ _ → isProp→isSet squash₁) uaIdEquiv

-- -- -- -- -- -- -- -- --   p2 : (x : RP∞) (y : fst x) → PathP (λ i → help x y i .fst) y true
-- -- -- -- -- -- -- -- --   p2 = uncurry λ X → PT.elim (λ _ → isPropΠ λ _ → isOfHLevelPathP' 1 isSetBool _ _)
-- -- -- -- -- -- -- -- --     (EquivJ (λ X x → (y : X) →
-- -- -- -- -- -- -- -- --       PathP (λ i → help (X , ∣ x ∣₁) y i .fst) y true)
-- -- -- -- -- -- -- -- --         λ { false → toPathP refl ; true → toPathP refl})

-- -- -- -- -- -- -- -- --   p2-pp : PathP (λ i → PathP (λ X → help-base i X .fst) true true) (p2 Bool* true) refl
-- -- -- -- -- -- -- -- --   p2-pp = isOfHLevelPathP' 0 (isOfHLevelPathP' 1 isSetBool _ _) _ _ .fst

-- -- -- -- -- -- -- -- --   A' : Σ RP∞ fst → Type _
-- -- -- -- -- -- -- -- --   A' (x , p) = A x p

-- -- -- -- -- -- -- -- --   Path1 : (x : RP∞) (y : fst x) → Path (Σ RP∞ fst) (x , y) (Bool* , true)
-- -- -- -- -- -- -- -- --   Path1 x y = ΣPathP ((help x y ) , (p2 x y))

-- -- -- -- -- -- -- -- --   Path1≡refl : Path1 Bool* true ≡ refl
-- -- -- -- -- -- -- -- --   Path1≡refl = ΣSquareSet (λ X → isSetRPpt X) help-base

-- -- -- -- -- -- -- -- --   pst' : (x : RP∞) (y : fst x) → A x y ≡ A Bool* true
-- -- -- -- -- -- -- -- --   pst' x y i = A (help x y i) (p2 x y i)

-- -- -- -- -- -- -- -- -- bakam : (A B C : Pointed₀)
-- -- -- -- -- -- -- -- --   → isHomogeneous C
-- -- -- -- -- -- -- -- --   → isSet (A →∙ (B →∙ C ∙))
-- -- -- -- -- -- -- -- --   → isSet
-- -- -- -- -- -- -- -- --         (Σ[ f ∈ (fst A → (fst B → fst C)) ]
-- -- -- -- -- -- -- -- --          (Σ[ l ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
-- -- -- -- -- -- -- -- --            Σ[ r ∈ ((a : fst A) → f a (pt B) ≡ pt C) ]
-- -- -- -- -- -- -- -- --              ∥ PathP (λ i → l (pt B) i ≡ pt C) (r (pt A)) refl ∥₂))
-- -- -- -- -- -- -- -- -- bakam A B C hom c =
-- -- -- -- -- -- -- -- --   uncurry λ f1 → uncurry λ l1 → uncurry
-- -- -- -- -- -- -- -- --     λ r1 → ST.elim (λ _ → isSetΠ λ _ → isProp→isSet isPropIsProp)
-- -- -- -- -- -- -- -- --       λ q1
-- -- -- -- -- -- -- -- --       → uncurry λ f2 → uncurry λ l2 → uncurry
-- -- -- -- -- -- -- -- --     λ r2 → ST.elim (λ _ → isProp→isSet isPropIsProp)
-- -- -- -- -- -- -- -- --       λ q2 → {!!}
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   T' : Type _
-- -- -- -- -- -- -- -- --   T' = Σ[ q ∈ Σ[ f ∈ (fst A → (fst B → fst C)) ]
-- -- -- -- -- -- -- -- --                (Σ[ l ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
-- -- -- -- -- -- -- -- --                 ((a : fst A) → f a (pt B) ≡ pt C)) ]
-- -- -- -- -- -- -- -- --         ∥ PathP (λ i → q .snd .fst (pt B) i ≡ pt C) (q .snd .snd (pt A)) refl ∥₂

-- -- -- -- -- -- -- -- --   T = (Σ[ f ∈ (fst A → (fst B → fst C)) ]
-- -- -- -- -- -- -- -- --          (Σ[ l ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
-- -- -- -- -- -- -- -- --            Σ[ r ∈ ((a : fst A) → f a (pt B) ≡ pt C) ]
-- -- -- -- -- -- -- -- --              ∥ PathP (λ i → l (pt B) i ≡ pt C) (r (pt A)) refl ∥₂))


-- -- -- -- -- -- -- -- --   to : (A →∙ (B →∙ C ∙)) → T
-- -- -- -- -- -- -- -- --   to f = (λ x y → fst f x .fst y)
-- -- -- -- -- -- -- -- --        , ((λ b → λ i → snd f i .fst b)
-- -- -- -- -- -- -- -- --        , ((λ a → fst f a .snd) , ∣ cong snd (snd f) ∣₂)) -- (f , l , r , ∣ p ∣₂)

-- -- -- -- -- -- -- -- --   back : T → A →∙ (B →∙ C ∙)
-- -- -- -- -- -- -- -- --   back = uncurry λ f → uncurry λ l → uncurry λ r → ST.rec c λ q → (λ x → f x , r x) , (λ i → (λ b → l b i) , (q i))



-- -- -- -- -- -- -- -- --   ptsd : isSet T'
-- -- -- -- -- -- -- -- --   ptsd = λ {((f , l , r) , p) → J> λ y → {!!}}
-- -- -- -- -- -- -- -- --   {- uncurry λ {(f , l  , r)
-- -- -- -- -- -- -- -- --     → ST.elim (λ _ → isSetΠ λ _ → isProp→isSet isPropIsProp)
-- -- -- -- -- -- -- -- --          λ q1 → uncurry λ {(f2 , l2  , r2)
-- -- -- -- -- -- -- -- --     → ST.elim (λ _ → isProp→isSet isPropIsProp)
-- -- -- -- -- -- -- -- --       λ q2 → λ p q → ΣSquareSet (λ _ → squash₂)
-- -- -- -- -- -- -- -- --         {!c (back (f , (l , (r , ∣ q1 ∣₂)))) ((back (f , (l , (r , ∣ q1 ∣₂))))) !}}}
-- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- --   open import Cubical.Functions.Embedding



-- -- -- -- -- -- -- -- --   back-emb : isEmbedding back
-- -- -- -- -- -- -- -- --   back-emb x y = isoToIsEquiv (iso _ (h x y)
-- -- -- -- -- -- -- -- --     (λ q → {!!})
-- -- -- -- -- -- -- -- --      λ q → {!!})
-- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- --     h : (x y : _) → back x ≡ back y → x ≡ y
-- -- -- -- -- -- -- -- --     h x y p = {!!} --  ΣPathP ((λ i a b → {!p i .fst a .fst b!}) , {!!}) -- →∙Homogeneous≡ (isHomogeneous→∙ hom) (funExt λ a → →∙Homogeneous≡ hom (λ i b → fst (q i) a b))

-- -- -- -- -- -- -- -- --     h⁻ : {!!}
-- -- -- -- -- -- -- -- --     h⁻ = {!!}


-- -- -- -- -- -- -- -- -- foo : ∀ {ℓ} (A : (X : RP∞) → fst X → Type ℓ) → Iso ((x : _) (y : _) → A x y) (A Bool* true)
-- -- -- -- -- -- -- -- -- Iso.fun (foo A) F = F Bool* true
-- -- -- -- -- -- -- -- -- Iso.inv (foo A) = ind** A .fst
-- -- -- -- -- -- -- -- -- Iso.rightInv (foo A) p = ind** A .snd p
-- -- -- -- -- -- -- -- -- Iso.leftInv (foo A) F = funExt λ X → funExt (help X)
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   help : (X : RP∞) (y : fst X) → ind** A .fst (F Bool* true) X y ≡ F X y
-- -- -- -- -- -- -- -- --   help = ind** (λ X y → ind** A .fst (F Bool* true) X y ≡ F X y) .fst (ind** A .snd (F Bool* true))


-- -- -- -- -- -- -- -- -- majp : {!(A : (X : RP∞) (x : fst X) → Pointed₀) (B : (X : RP∞) (x : fst X) → Pointed₀) → ?!}
-- -- -- -- -- -- -- -- -- majp = {!!}

-- -- -- -- -- -- -- -- -- ind**a : (A : (X : RP∞) (x : fst X) → Pointed₀) (B : (X : RP∞) (x : fst X) → Pointed₀)
-- -- -- -- -- -- -- -- --   → (((X : RP∞) (x : fst X) → A X x .fst) → (X : RP∞) (x : fst X) → B X x .fst)
-- -- -- -- -- -- -- -- --   → Σ[ X ∈ RP∞ ] (⋀∞ X (A X)) → Σ[ X ∈ RP∞ ] ((x : fst X) → B X x .fst)
-- -- -- -- -- -- -- -- -- ind**a A B ind (X , genSmash.proj x) = {!x!} , (ind (λ X q → {!!}) X )
-- -- -- -- -- -- -- -- -- ind**a A B ind (X , genSmash.base x) = {!!}
-- -- -- -- -- -- -- -- -- ind**a A B ind (X , genSmash.gl x a i) = {!!}

-- -- -- -- -- -- -- -- -- module _ (A : (X : RP∞) → (x : fst X) → (Y : RP∞) → (y : fst Y) → (fst X → fst Y → ℕ) → Pointed₀)
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   l' : (X : RP∞) (Y : RP∞) (n : fst X → fst Y → ℕ) → Type _
-- -- -- -- -- -- -- -- --   l' X Y n = ⋀∞ X λ x → ⋀∞ Y (λ y → A X x Y y n) , proj (λ y → A X x Y y n .snd)

-- -- -- -- -- -- -- -- --   r' : (X : RP∞) (Y : RP∞) (n : fst X → fst Y → ℕ) → Type _
-- -- -- -- -- -- -- -- --   r' X Y n = ⋀∞ Y λ y → ⋀∞ X (λ x → A X x Y y n) , proj (λ x → A X x Y y n .snd)

-- -- -- -- -- -- -- -- --   IS1 : (Y : RP∞) → Iso ((X : RP∞) (x₁ : fst X) → (n : fst X → fst Y → ℕ) → ⋀∞ Y (λ Y₁ → A X x₁ Y Y₁ n)) ((n : Bool → fst Y → ℕ) → ⋀∞ Y (λ Y₁ → A Bool* true Y Y₁ n))
-- -- -- -- -- -- -- -- --   IS1 Y = foo _

-- -- -- -- -- -- -- -- --   blahem : (X : RP∞) (Y : RP∞) (n : fst X → fst Y → ℕ) →
-- -- -- -- -- -- -- -- --       l' X Y n → r' X Y n
-- -- -- -- -- -- -- -- --   blahem X Y n (genSmash.proj x) = proj λ y → {!!}
-- -- -- -- -- -- -- -- --   blahem X Y n (genSmash.base x) = {!!}
-- -- -- -- -- -- -- -- --   blahem X Y n (genSmash.gl x a i) = {!!}

-- -- -- -- -- -- -- -- -- BiHom' : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- BiHom' X A C =
-- -- -- -- -- -- -- -- --   Σ[ f ∈ (((x : fst X) → A x .fst) → C .fst) ]
-- -- -- -- -- -- -- -- --     Σ[ g ∈ ((e : fst X ≃ Bool)
-- -- -- -- -- -- -- -- --       → A (invEq e true) →∙ (A (invEq e false) →∙ C ∙)) ]
-- -- -- -- -- -- -- -- --       {!!}

-- -- -- -- -- -- -- -- -- RPfun-gen : (X : RP∞) (A : fst X → Pointed₀) (x : fst X)
-- -- -- -- -- -- -- -- --   → A x .fst
-- -- -- -- -- -- -- -- --   → (x' : fst X) → Dec (x ≡ x') → A x' .fst
-- -- -- -- -- -- -- -- -- RPfun-gen X A x a x' (yes p) = subst (fst ∘ A) p a
-- -- -- -- -- -- -- -- -- RPfun-gen X A x a x' (no ¬p) = A x' .snd

-- -- -- -- -- -- -- -- -- RPfun : (X : RP∞) (A : fst X → Pointed₀) (x : fst X)
-- -- -- -- -- -- -- -- --   → A x .fst
-- -- -- -- -- -- -- -- --   → (x : fst X) → A x .fst
-- -- -- -- -- -- -- -- -- RPfun X A x p y = RPfun-gen X A x p y (decPt X x y)

-- -- -- -- -- -- -- -- -- RPfun-const : (X : RP∞) (A : fst X → Pointed₀) (x₀ : fst X)
-- -- -- -- -- -- -- -- --   → (x : fst X)
-- -- -- -- -- -- -- -- --   → (p : Dec (x₀ ≡ x))
-- -- -- -- -- -- -- -- --   → RPfun-gen X A x₀ (A x₀ .snd) x p
-- -- -- -- -- -- -- -- --    ≡ A x .snd
-- -- -- -- -- -- -- -- -- RPfun-const X A x₀ x (yes p) i =
-- -- -- -- -- -- -- -- --   transp (λ j → fst (A (p (i ∨ j)))) i (A (p i) .snd)
-- -- -- -- -- -- -- -- -- RPfun-const X A x₀ x (no ¬p) = refl

-- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- BiHom* : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- BiHom* X A C =
-- -- -- -- -- -- -- -- --   Σ[ c ∈ (fst X → fst C) ]
-- -- -- -- -- -- -- -- --   Σ[ f ∈ ((((x : fst X) → A x .fst) , λ x → A x .snd) →∙ C) ]
-- -- -- -- -- -- -- -- --     ((x : fst X) (a : A x .fst) → fst f (RPfun X A x a) ≡ c x)
-- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- isBihom : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀)
-- -- -- -- -- -- -- -- --   → (((x : fst X) → A x .fst) , λ x → A x .snd) →∙ C → Type
-- -- -- -- -- -- -- -- -- isBihom X A C f =
-- -- -- -- -- -- -- -- --   Σ[ c ∈ (fst X → fst C) ]
-- -- -- -- -- -- -- -- --     ((x : fst X) (a : A x .fst) → fst f (RPfun X A x a) ≡ c x)

-- -- -- -- -- -- -- -- -- BiHom* : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- BiHom* X A C = Σ[ f ∈ ((((x : fst X) → A x .fst) , λ x → A x .snd) →∙ C) ]
-- -- -- -- -- -- -- -- --     isBihom X A C f

-- -- -- -- -- -- -- -- -- BiHom's : (X Y : RP∞) (A : fst X → fst Y → Pointed₀) (C : Pointed₀)
-- -- -- -- -- -- -- -- --   → BiHom* X (λ x → ((y : fst Y) → A x y .fst) , (λ y → A x y .snd)) C
-- -- -- -- -- -- -- -- --   → Type
-- -- -- -- -- -- -- -- -- BiHom's X Y A C (F , c) =
-- -- -- -- -- -- -- -- --   Σ[ l ∈ ((x : fst X) (f : (y : _) → A x y .fst) → {!F .fst !}) ] {!is!}
-- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- --   c' : {!!}
-- -- -- -- -- -- -- -- --   c' = {!!}

-- -- -- -- -- -- -- -- -- QHom** : (X Y : RP∞) (A : fst X → fst Y → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- QHom** X Y A C = Σ[ F ∈ BiHom* X (λ x → BiHom* Y (λ y → A x y) C , {!!}) C ] {!!}

-- -- -- -- -- -- -- -- -- -- BiHom** : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- BiHom** X A C =
-- -- -- -- -- -- -- -- -- --   Σ[ f ∈ ((((x : fst X) → A x .fst) , snd ∘ A) →∙ C) ]
-- -- -- -- -- -- -- -- -- --    Σ[ f-coh ∈ ((x : fst X) (z : A x .fst) → fst f (RPfun X A x z) ≡ pt C) ]
-- -- -- -- -- -- -- -- -- --      ((x : fst X)
-- -- -- -- -- -- -- -- -- --        → PathP (λ i → fst f (λ x' → RPfun-const X A x x' (decPt X x x') (~ i)) ≡ pt C)
-- -- -- -- -- -- -- -- -- --                 (f .snd) (f-coh x (A x .snd)))

-- -- -- -- -- -- -- -- -- -- 4-elt : Type₁
-- -- -- -- -- -- -- -- -- -- 4-elt = Σ[ X ∈ Type ] ∥ X ≃ Bool × Bool ∥₁

-- -- -- -- -- -- -- -- -- -- isSet-4 : (x : 4-elt) → isSet (fst x)
-- -- -- -- -- -- -- -- -- -- isSet-4 = uncurry λ X → PT.elim (λ _ → isPropIsOfHLevel 2)
-- -- -- -- -- -- -- -- -- --   λ p → subst isSet (sym (ua p))
-- -- -- -- -- -- -- -- -- --     (isSet× isSetBool isSetBool)

-- -- -- -- -- -- -- -- -- -- perm : (X : 4-elt) → hSet ℓ-zero
-- -- -- -- -- -- -- -- -- -- perm = uncurry λ X → {!PT.rec ? ?!}

-- -- -- -- -- -- -- -- -- -- Z ONE TWO THREE : Bool × Bool
-- -- -- -- -- -- -- -- -- -- Z = false , false
-- -- -- -- -- -- -- -- -- -- ONE = true , false
-- -- -- -- -- -- -- -- -- -- TWO = false , true
-- -- -- -- -- -- -- -- -- -- THREE = true , true

-- -- -- -- -- -- -- -- -- -- suc' : Bool × Bool → Bool × Bool
-- -- -- -- -- -- -- -- -- -- suc' (false , false) = ONE
-- -- -- -- -- -- -- -- -- -- suc' (false , true) = THREE
-- -- -- -- -- -- -- -- -- -- suc' (true , false) = TWO
-- -- -- -- -- -- -- -- -- -- suc' (true , true) = Z

-- -- -- -- -- -- -- -- -- -- data sub2 (X : 4-elt) : Type where
-- -- -- -- -- -- -- -- -- --   [_,_] : (x y : fst X) → ¬ (x ≡ y) → sub2 X
-- -- -- -- -- -- -- -- -- --   pz : (x y : fst X) (p : ¬ (x ≡ y))
-- -- -- -- -- -- -- -- -- --     → [ x , y ] p ≡ [ y , x ] (p ∘ sym)

-- -- -- -- -- -- -- -- -- -- isCyclic : (X : 4-elt)
-- -- -- -- -- -- -- -- -- --   → (fst X ≃ Bool × Bool)
-- -- -- -- -- -- -- -- -- --   → hProp ℓ-zero
-- -- -- -- -- -- -- -- -- -- isCyclic =
-- -- -- -- -- -- -- -- -- --   uncurry λ X
-- -- -- -- -- -- -- -- -- --    → rec→Set
-- -- -- -- -- -- -- -- -- --        {!X!}
-- -- -- -- -- -- -- -- -- --        {!X!}
-- -- -- -- -- -- -- -- -- --        {!X!}
-- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- --   F : (X : Type) → X ≃ Bool × Bool → X ≃ Bool × Bool → hProp ℓ-zero
-- -- -- -- -- -- -- -- -- --   fst (F X e p) = {!!}
-- -- -- -- -- -- -- -- -- --   snd (F X e p) = {!p!}

-- -- -- -- -- -- -- -- -- -- sub2-4 : (X : 4-elt) → sub2 X
-- -- -- -- -- -- -- -- -- --   → {!1,2,3,4!}
-- -- -- -- -- -- -- -- -- -- sub2-4 = {!!}

-- -- -- -- -- -- -- -- -- -- sub2* : (X : 4-elt) → isSet (sub2 X)
-- -- -- -- -- -- -- -- -- -- sub2* =
-- -- -- -- -- -- -- -- -- --   uncurry (λ X → PT.elim (λ p → isPropIsOfHLevel 2)
-- -- -- -- -- -- -- -- -- --    (EquivJ (λ X x → isSet (sub2 (X , ∣ x ∣₁)))
-- -- -- -- -- -- -- -- -- --     {!!}))

-- -- -- -- -- -- -- -- -- -- bram : (X : 4-elt) → fst X → fst X
-- -- -- -- -- -- -- -- -- -- bram = {!!}

-- -- -- -- -- -- -- -- -- -- BiHom^ : (x : 4-elt) → fst x → fst x
-- -- -- -- -- -- -- -- -- -- BiHom^ = uncurry λ X
-- -- -- -- -- -- -- -- -- --   → elim→Set (λ p → isSetΠ λ _ → isSet-4 (X , p))
-- -- -- -- -- -- -- -- -- --       (λ e x → invEq e (suc' (fst e x)))
-- -- -- -- -- -- -- -- -- --       λ e e' → funExt λ x → {!e .fst x ≡ ?!}

-- -- -- -- -- -- -- -- -- -- QuadHomIso* : (X : 4-elt) {A : fst X → Pointed₀}  (C : Pointed₀) → Type₁ 
-- -- -- -- -- -- -- -- -- -- QuadHomIso* X {A = A} C =
-- -- -- -- -- -- -- -- -- --   Σ[ F ∈ (((x : fst X) → A x .fst) → typ C) ]
-- -- -- -- -- -- -- -- -- --   Σ[ Fl ∈ {!!} ]
-- -- -- -- -- -- -- -- -- --   {!!}

-- -- -- -- -- -- -- -- -- -- Q* : (X Y : RP∞) (A : fst X → fst Y → Pointed₀) (B : Pointed₀)
-- -- -- -- -- -- -- -- -- --   → Type 
-- -- -- -- -- -- -- -- -- -- Q* X Y A B =
-- -- -- -- -- -- -- -- -- --   Σ[ F ∈ (((x : fst X) (y : fst Y) → A x y .fst) → B .fst) ]
-- -- -- -- -- -- -- -- -- --     Σ[ e ∈ ((y : fst Y)
-- -- -- -- -- -- -- -- -- --             (f : (x : fst X) → A x y .fst)
-- -- -- -- -- -- -- -- -- --          → {!!}) ]
-- -- -- -- -- -- -- -- -- --       {!!}

-- -- -- -- -- -- -- -- -- -- -- QuadHomIso : {A B C D E : Pointed₀}
-- -- -- -- -- -- -- -- -- -- --   → Iso (A →∙ (B →∙ C →∙ D →∙ E ∙ ∙ ∙))
-- -- -- -- -- -- -- -- -- -- --          (Σ[ f ∈ (fst A → fst B → fst C → fst D → fst E) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-a ∈ ((b : fst B) (c : fst C) (d : fst D) → f (pt A) b c d ≡ pt E) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-b ∈ ((a : fst A) (c : fst C) (d : fst D) → f a (pt B) c d ≡ pt E) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-c ∈ ((a : fst A) (b : fst B) (d : fst D) → f a b (pt C) d ≡ pt E) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-d ∈ ((a : fst A) (b : fst B) (c : fst C) → f a b c (pt D) ≡ pt E) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-ab ∈ ((c : fst C) (d : fst D)
-- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-a (pt B) c d i ≡ pt E) (f-b (pt A) c d) refl) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-bc ∈ ((a : fst A) (d : fst D)
-- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-b a (pt C) d i ≡ pt E) (f-c a (pt B) d) refl) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-cd ∈ ((a : fst A) (b : fst B)
-- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-c a b (pt D) i ≡ pt E) (f-d a b (pt C)) refl) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-ac ∈ ((b : fst B) (d : fst D)
-- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-a b (pt C) d i ≡ pt E) (f-c (pt A) b d) refl) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-ad ∈ ((b : fst B) (c : fst C)
-- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-a b c (pt D) i ≡ pt E) (f-d (pt A) b c) refl) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-bd ∈ ((a : fst A) (c : fst C)
-- -- -- -- -- -- -- -- -- -- --             → PathP (λ i → f-b a c (pt D) i ≡ pt E) (f-d a (pt B) c) refl) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-bcd ∈ ((a : typ A)
-- -- -- -- -- -- -- -- -- -- --             → Cube (f-cd a (pt B)) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- --                     (f-bd a (pt C)) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- --                     (f-bc a (pt D)) (λ _ _ → pt E)) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-acd ∈ ((b : typ B)
-- -- -- -- -- -- -- -- -- -- --             → Cube (f-cd (pt A) b) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- --                     (f-ad b (pt C)) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- --                     (f-ac b (pt D)) (λ _ _ → pt E)) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-abd ∈ ((c : typ C)
-- -- -- -- -- -- -- -- -- -- --             → Cube (f-bd (pt A) c) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- --                     (f-ad (pt B) c) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- --                     (f-ab c (pt D)) (λ _ _ → pt E)) ]
-- -- -- -- -- -- -- -- -- -- --           Σ[ f-abc ∈ ((d : typ D)
-- -- -- -- -- -- -- -- -- -- --             → Cube (f-bc (pt A) d) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- --                     (f-ac (pt B) d) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- --                     (f-ab (pt C) d) (λ _ _ → pt E)) ]
-- -- -- -- -- -- -- -- -- -- --           PathP (λ i
-- -- -- -- -- -- -- -- -- -- --            → Cube (f-acd (pt B) i) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- --                    (f-abd (pt C) i) (λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- --                    (f-abc (pt D) i) λ _ _ → pt E)
-- -- -- -- -- -- -- -- -- -- --             (f-bcd (pt A))
-- -- -- -- -- -- -- -- -- -- --             refl)
-- -- -- -- -- -- -- -- -- -- -- Iso.fun (QuadHomIso {A} {B} {C} {D} {E}) f =
-- -- -- -- -- -- -- -- -- -- --   (λ x y z w → f .fst x .fst y .fst z .fst w)
-- -- -- -- -- -- -- -- -- -- --   , ((λ b c d i → f .snd i .fst b .fst c .fst d)
-- -- -- -- -- -- -- -- -- -- --   , (λ a c d i → f .fst a .snd i .fst c .fst d)
-- -- -- -- -- -- -- -- -- -- --   , ((λ a b d i → f .fst a .fst b .snd i .fst d)
-- -- -- -- -- -- -- -- -- -- --   , ((λ a b c → f .fst a .fst b .fst c .snd)
-- -- -- -- -- -- -- -- -- -- --   , ((λ c d i j → f .snd i .snd j .fst c .fst d)
-- -- -- -- -- -- -- -- -- -- --   , (λ a d i j → f .fst a .snd i .snd j .fst d)
-- -- -- -- -- -- -- -- -- -- --   , (λ a b i j → f .fst a .fst b .snd i .snd j)
-- -- -- -- -- -- -- -- -- -- --   , ((λ b d i j → f .snd i .fst b .snd j .fst d)
-- -- -- -- -- -- -- -- -- -- --   , (λ b c i → f .snd i .fst b .fst c .snd)
-- -- -- -- -- -- -- -- -- -- --   , (λ a c i → f .fst a .snd i .fst c .snd)
-- -- -- -- -- -- -- -- -- -- --   , ((λ a i j k → f .fst a .snd i .snd j .snd k)
-- -- -- -- -- -- -- -- -- -- --   , (λ b i j k  → f .snd i .fst b .snd j .snd k)
-- -- -- -- -- -- -- -- -- -- --   , (λ c i j k → f .snd i .snd j .fst c .snd k)
-- -- -- -- -- -- -- -- -- -- --   , (λ d i j k → f .snd i .snd j .snd k .fst d)
-- -- -- -- -- -- -- -- -- -- --   , λ i j k w → f .snd i .snd j .snd k .snd w))))))
-- -- -- -- -- -- -- -- -- -- -- Iso.inv (QuadHomIso {A} {B} {C} {D} {E})
-- -- -- -- -- -- -- -- -- -- --   (f , f-a , f-b , f-c , f-d , f-ab , f-bc , f-cd , f-ac , f-ad , f-bd
-- -- -- -- -- -- -- -- -- -- --      , f-bcd , f-acd , f-abd , f-abc , co) =
-- -- -- -- -- -- -- -- -- -- --        (λ a → (λ b → (λ c → (λ d → f a b c d)
-- -- -- -- -- -- -- -- -- -- --          , f-d a b c)
-- -- -- -- -- -- -- -- -- -- --            , λ i → (λ d → f-c a b d i)
-- -- -- -- -- -- -- -- -- -- --                   , (f-cd a b i))
-- -- -- -- -- -- -- -- -- -- --           , λ i → (λ c → (λ d → f-b a c d i)
-- -- -- -- -- -- -- -- -- -- --                  , f-bd a c i)
-- -- -- -- -- -- -- -- -- -- --                  , (λ j → (λ d → f-bc a d i j)
-- -- -- -- -- -- -- -- -- -- --                  , (f-bcd a i j)))
-- -- -- -- -- -- -- -- -- -- --      , λ i → (λ b → (λ c → (λ d → f-a b c d i)
-- -- -- -- -- -- -- -- -- -- --             , f-ad b c i)
-- -- -- -- -- -- -- -- -- -- --             , λ j → (λ d → f-ac b d i j)
-- -- -- -- -- -- -- -- -- -- --                    , f-acd b i j)
-- -- -- -- -- -- -- -- -- -- --             , (λ j → (λ c → (λ d → f-ab c d i j)
-- -- -- -- -- -- -- -- -- -- --                     , (f-abd c i j))
-- -- -- -- -- -- -- -- -- -- --                     , (λ k → (λ d → f-abc d i j k)
-- -- -- -- -- -- -- -- -- -- --                     , (co i j k)))
-- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (QuadHomIso {A} {B} {C} {D} {E}) _ = refl
-- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (QuadHomIso {A} {B} {C} {D} {E}) _ = refl

-- -- -- -- -- -- -- -- -- -- -- TriHom* : {!!}
-- -- -- -- -- -- -- -- -- -- -- TriHom* = {!!}


-- -- -- -- -- -- -- -- -- -- -- Bool→ : ∀ {ℓ} → (A : (x : Bool) → Type ℓ)
-- -- -- -- -- -- -- -- -- -- --   → Iso ((x : Bool) → A x) (A true × A false)
-- -- -- -- -- -- -- -- -- -- -- Iso.fun (Bool→ A) f = f true , f false
-- -- -- -- -- -- -- -- -- -- -- Iso.inv (Bool→ A) (a , b) false = b
-- -- -- -- -- -- -- -- -- -- -- Iso.inv (Bool→ A) (a , b) true = a
-- -- -- -- -- -- -- -- -- -- -- Iso.rightInv (Bool→ A) _ = refl
-- -- -- -- -- -- -- -- -- -- -- Iso.leftInv (Bool→ A) f = funExt λ { false → refl ; true → refl}


-- -- -- -- -- -- -- -- -- -- -- Iso-BiHom** : (A : Bool → Pointed₀) (C : Pointed₀)
-- -- -- -- -- -- -- -- -- -- --   → Iso (BiHom** Bool* A C)
-- -- -- -- -- -- -- -- -- -- --          ((Σ[ f ∈ (A true .fst × A false .fst → fst C) ]
-- -- -- -- -- -- -- -- -- -- --            Σ[ l ∈ ((x : A true .fst) → f (x , A false .snd) ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- --              Σ[ r ∈ ((b : A false .fst) → f (A true .snd , b) ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- --                PathP (λ i → r (A false .snd) i ≡ pt C) (l (A true .snd)) refl)) 
-- -- -- -- -- -- -- -- -- -- -- Iso-BiHom** A C =
-- -- -- -- -- -- -- -- -- -- --   compIso
-- -- -- -- -- -- -- -- -- -- --     (compIso
-- -- -- -- -- -- -- -- -- -- --       (invIso (Σ-cong-iso-fst (Σ-cong-iso-fst (invIso (domIso (Bool→ (fst ∘ A)))))))
-- -- -- -- -- -- -- -- -- -- --       (Σ-cong-iso-snd λ f → invIso
-- -- -- -- -- -- -- -- -- -- --         (Σ-cong-iso-fst (invIso (Bool→ (λ x → (z : A x .fst) →
-- -- -- -- -- -- -- -- -- -- --           f .fst (RPfun Bool* A x z true , RPfun Bool* A x z false) ≡ pt C))))))
-- -- -- -- -- -- -- -- -- -- --     (compIso
-- -- -- -- -- -- -- -- -- -- --       Σ-assoc-Iso
-- -- -- -- -- -- -- -- -- -- --       (Σ-cong-iso-snd
-- -- -- -- -- -- -- -- -- -- --         λ f → {!!}))

-- -- -- -- -- -- -- -- -- -- -- →∙→∙Iso : ∀ {ℓ ℓ' ℓ''} {A : Pointed ℓ} {B : Pointed ℓ'} {C : Pointed ℓ''}
-- -- -- -- -- -- -- -- -- -- --   → Iso (A →∙ (B →∙ C ∙))
-- -- -- -- -- -- -- -- -- -- --          (Σ[ f ∈ (fst A → fst B → fst C) ]
-- -- -- -- -- -- -- -- -- -- --            Σ[ l ∈ ((x : fst A) → f x (pt B) ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- --              Σ[ r ∈ ((b : fst B) → f (pt A) b ≡ pt C) ]
-- -- -- -- -- -- -- -- -- -- --                PathP (λ i → r (pt B) i ≡ pt C) (l (pt A)) refl)
-- -- -- -- -- -- -- -- -- -- -- Iso.fun →∙→∙Iso f =
-- -- -- -- -- -- -- -- -- -- --      (λ x y → f .fst x .fst y)
-- -- -- -- -- -- -- -- -- -- --    , ((λ x → f .fst x .snd)
-- -- -- -- -- -- -- -- -- -- --    , ((λ y i → f .snd i .fst y)
-- -- -- -- -- -- -- -- -- -- --    , cong snd (snd f)))
-- -- -- -- -- -- -- -- -- -- -- Iso.inv →∙→∙Iso = {!!}
-- -- -- -- -- -- -- -- -- -- -- Iso.rightInv →∙→∙Iso = {!!}
-- -- -- -- -- -- -- -- -- -- -- Iso.leftInv →∙→∙Iso = {!!}

-- -- -- -- -- -- -- -- -- -- -- BiHom**-bool : {!BiHom**!}
-- -- -- -- -- -- -- -- -- -- -- BiHom**-bool = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- BiBiHom : (X Y : RP∞) (A : fst X → fst Y → Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- --   (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- -- BiBiHom X Y A C =
-- -- -- -- -- -- -- -- -- -- -- --   Σ[ F ∈ (((x : fst X) (y : fst Y) → A x y .fst)
-- -- -- -- -- -- -- -- -- -- -- --               , λ x y → A x y .snd)
-- -- -- -- -- -- -- -- -- -- -- --           →∙ C ]
-- -- -- -- -- -- -- -- -- -- -- --   Σ[ pts ∈ (fst Y → fst C × fst C)  ]
-- -- -- -- -- -- -- -- -- -- -- --   Σ[ l∧ ∈ ((x : fst X) → BiHom* Y (A x) C) ] 
-- -- -- -- -- -- -- -- -- -- -- --   Σ[ r ∈ ((y : fst Y) → ((x : fst X) → A x y .fst) → fst C) ]
-- -- -- -- -- -- -- -- -- -- -- --   Σ[ F-lr ∈ ((y : fst Y) (f : ((x : fst X) → A x y .fst))
-- -- -- -- -- -- -- -- -- -- -- --            → F .fst (λ x → RPfun Y (A x) y (f x)) ≡ r y f) ]
-- -- -- -- -- -- -- -- -- -- -- --   Σ[ l∧-r ∈ ((x : fst X) (y : fst Y) (z : A x y .fst) 
-- -- -- -- -- -- -- -- -- -- -- --              → r y (RPfun X (λ x → A x y) x z) ≡ l∧ x .fst y) ]
-- -- -- -- -- -- -- -- -- -- -- --   Σ[ F-coh ∈ ((x : fst X) (f : (y : fst Y) → A x y .fst)
-- -- -- -- -- -- -- -- -- -- -- --                → F .fst
-- -- -- -- -- -- -- -- -- -- -- --                  (RPfun X (λ x → (((y : fst Y) → A x y .fst) , λ y → A x y .snd))
-- -- -- -- -- -- -- -- -- -- -- --                         x f)
-- -- -- -- -- -- -- -- -- -- -- --                 ≡ l∧ x .snd .fst .fst f) ]
-- -- -- -- -- -- -- -- -- -- -- --   Σ[ high ∈ ((x : fst X) (y : fst Y) (z : A x y .fst)
-- -- -- -- -- -- -- -- -- -- -- --       → PathP (λ i → F-coh x (RPfun Y (A x) y z) i ≡ l∧-r x y z i)
-- -- -- -- -- -- -- -- -- -- -- --                (cong (F .fst) (funExt
-- -- -- -- -- -- -- -- -- -- -- --                  (λ x' → funExt λ y'
-- -- -- -- -- -- -- -- -- -- -- --                    → cool x y z x' y' (decPt X x x') (decPt Y y y')))
-- -- -- -- -- -- -- -- -- -- -- --                ∙ F-lr y (RPfun X (λ x₁ → A x₁ y) x z))
-- -- -- -- -- -- -- -- -- -- -- --                (l∧ x .snd .snd y z)) ]
-- -- -- -- -- -- -- -- -- -- -- --   Σ[ l∧-pt ∈ ((x : fst X) → l∧ x .snd .fst .fst (λ y → A x y .snd) ≡ pts .fst) ]
-- -- -- -- -- -- -- -- -- -- -- --   Σ[ F-2r ∈ ((y : fst Y) (f : ((x : fst X) → A x y .fst))
-- -- -- -- -- -- -- -- -- -- -- --     → F .fst (λ x → RPfun Y (A x) y (f x)) ≡ pts .fst) ]
-- -- -- -- -- -- -- -- -- -- -- --     {!!}
-- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- --   cool : (x : fst X) (y : fst Y) (z : A x y .fst) (x' : fst X) (y' : fst Y)
-- -- -- -- -- -- -- -- -- -- -- --     → (p : Dec (x ≡ x')) (q : Dec (y ≡ y'))
-- -- -- -- -- -- -- -- -- -- -- --     → Path (A x' y' .fst)
-- -- -- -- -- -- -- -- -- -- -- --               ((RPfun-gen X
-- -- -- -- -- -- -- -- -- -- -- --        (λ x₁ → ((y₁ : fst Y) → A x₁ y₁ .fst) , (λ y₁ → A x₁ y₁ .snd)) x
-- -- -- -- -- -- -- -- -- -- -- --        (λ y' → RPfun-gen Y (A x) y z y' (decPt Y y y'))) x' p y')
-- -- -- -- -- -- -- -- -- -- -- --               (RPfun-gen Y (A x') y (RPfun-gen X (λ x → A x y) x z x' p) y' q)
-- -- -- -- -- -- -- -- -- -- -- --   cool x y z x' y' (yes p) (yes q) =
-- -- -- -- -- -- -- -- -- -- -- --       (λ j → subst2 (λ x₁ y' → A x₁ y' .fst) p
-- -- -- -- -- -- -- -- -- -- -- --                (λ i → transportRefl y' (i ∨ j))
-- -- -- -- -- -- -- -- -- -- -- --                      (RPfun-gen Y (A x) y z (transportRefl y' j)
-- -- -- -- -- -- -- -- -- -- -- --                        (decPt Y y (transportRefl y' j))))
-- -- -- -- -- -- -- -- -- -- -- --       ∙ cong (subst (λ x₁ → A x₁ y' .fst) p)
-- -- -- -- -- -- -- -- -- -- -- --            (cong (RPfun-gen Y (A x) y z y')
-- -- -- -- -- -- -- -- -- -- -- --              (isPropDec (isSetRPpt Y y y') (decPt Y y y') (yes q)))
-- -- -- -- -- -- -- -- -- -- -- --       ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- --       ∙ {!!}
-- -- -- -- -- -- -- -- -- -- -- --   cool x y z x' y' (yes p) (no ¬q) = {!(λ y'' → RPfun-gen Y (A x) y z y'' (decPt Y y y'')) y'!}
-- -- -- -- -- -- -- -- -- -- -- --   cool x y z x' y' (no ¬p) q = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- module _ (A B C D E : Pointed₀) (ptl ptr : fst E)
-- -- -- -- -- -- -- -- -- -- -- --          (l∧ r∧ : typ (Smash⋆ C D) → fst E) -- ok
-- -- -- -- -- -- -- -- -- -- -- --          (l r : typ A → typ B → typ E) -- ok
-- -- -- -- -- -- -- -- -- -- -- --          (F : typ A → typ B → typ C → typ D → typ E) -- ok
-- -- -- -- -- -- -- -- -- -- -- --          (F-l : (x : typ A) (y : fst B) (c : fst C)
-- -- -- -- -- -- -- -- -- -- -- --            → F x y c (pt D)
-- -- -- -- -- -- -- -- -- -- -- --            ≡ l x y)
-- -- -- -- -- -- -- -- -- -- -- --          (F-r : (x : typ A) (y : fst B) (d : fst D)
-- -- -- -- -- -- -- -- -- -- -- --            → F x y (pt C) d
-- -- -- -- -- -- -- -- -- -- -- --            ≡ r x y)
-- -- -- -- -- -- -- -- -- -- -- --          (l∧-l : (a : typ A) → l a (pt B) ≡ l∧ basel)
-- -- -- -- -- -- -- -- -- -- -- --          (r∧-r : (a : typ A) → r a (pt B) ≡ l∧ baser)
-- -- -- -- -- -- -- -- -- -- -- --          (Fg : (a : typ A) (x : fst C) (y : fst D) → F a (pt B) x y ≡ l∧ (proj x y))
-- -- -- -- -- -- -- -- -- -- -- --          (Gg : (b : typ B) (x : fst C) (y : fst D) → F (pt A) b x y ≡ r∧ (proj x y))
-- -- -- -- -- -- -- -- -- -- -- --          (Fg-high-l : (a : typ A) (c : fst C)
-- -- -- -- -- -- -- -- -- -- -- --            → PathP (λ i → Fg a c (pt D) i ≡ l∧-l a i)
-- -- -- -- -- -- -- -- -- -- -- --                 (F-l a (pt B) c)
-- -- -- -- -- -- -- -- -- -- -- --                 (cong l∧ (gluel c)))
-- -- -- -- -- -- -- -- -- -- -- --          (Fg-high-r : (a : typ A) (d : fst D)
-- -- -- -- -- -- -- -- -- -- -- --            → PathP (λ i → Fg a (pt C) d i ≡ r∧-r a i)
-- -- -- -- -- -- -- -- -- -- -- --                 (F-r a (pt B) d) -- ()
-- -- -- -- -- -- -- -- -- -- -- --                 (cong l∧ (gluer d)))
-- -- -- -- -- -- -- -- -- -- -- --          (l-r∧ : (b : typ B) → l (pt A) b ≡ r∧ basel)
-- -- -- -- -- -- -- -- -- -- -- --          (r-r∧ : (b : typ B) → r (pt A) b ≡ r∧ baser)
-- -- -- -- -- -- -- -- -- -- -- --          (l∧-pt : l∧ (proj (pt C) (pt D)) ≡ ptl)
-- -- -- -- -- -- -- -- -- -- -- --          (r∧-pt : r∧ (proj (pt C) (pt D)) ≡ ptl)
-- -- -- -- -- -- -- -- -- -- -- --          (F-2r : (x : typ A) (y : typ B) → F x y (pt C) (pt D) ≡ ptl)
-- -- -- -- -- -- -- -- -- -- -- --          where
-- -- -- -- -- -- -- -- -- -- -- --   test : Smash⋆ (Smash⋆ A B) (Smash⋆ C D) →∙ E
-- -- -- -- -- -- -- -- -- -- -- --   fst test basel = ptl -- ∙l
-- -- -- -- -- -- -- -- -- -- -- --   fst test baser = ptr -- ∙r
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj basel y) = l∧ y
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj baser y) = r∧ y
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (proj x y) basel) = l x y
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (proj x y) baser) = r x y
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (proj x y) (proj z w)) = F x y z w
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (proj x y) (gluel a i)) = F-l x y a i
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (proj x y) (gluer b i)) = F-r x y b i
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluel a i) basel) = l∧-l a i
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluel a i) baser) = r∧-r a i
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluel a i) (proj x y)) = Fg a x y i
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluel a i) (gluel b j)) = Fg-high-l a b i j
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluel a i) (gluer b j)) = Fg-high-r a b i j
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluer b i) basel) = l-r∧ b i
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluer b i) baser) = r-r∧ b i
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluer b i) (proj x y)) = Gg b x y i
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluer b i) (gluel c j)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   fst test (proj (gluer b i) (gluer d j)) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   fst test (gluel basel i) = l∧-pt i
-- -- -- -- -- -- -- -- -- -- -- --   fst test (gluel baser i) = r∧-pt i
-- -- -- -- -- -- -- -- -- -- -- --   fst test (gluel (proj x y) i) = F-2r x y i
-- -- -- -- -- -- -- -- -- -- -- --   fst test (gluel (gluel a j) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   fst test (gluel (gluer b j) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   fst test (gluer basel i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   fst test (gluer baser i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   fst test (gluer (proj x y) i) = {!F-2r!}
-- -- -- -- -- -- -- -- -- -- -- --   fst test (gluer (gluel a i₁) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   fst test (gluer (gluer b i₁) i) = {!!}
-- -- -- -- -- -- -- -- -- -- -- --   snd test = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- BiHomBool : (A : Bool → Pointed₀) (C : Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- --   → Iso (BiHom* Bool* A C) (Smash⋆ (A true) (A false) →∙ C)
-- -- -- -- -- -- -- -- -- -- -- -- -- BiHomBool A C =
-- -- -- -- -- -- -- -- -- -- -- -- --   compIso
-- -- -- -- -- -- -- -- -- -- -- -- --    (invIso (Σ-cong-iso-fst (invIso (Bool→ (λ _ → fst C)))))
-- -- -- -- -- -- -- -- -- -- -- -- --    (compIso
-- -- -- -- -- -- -- -- -- -- -- -- --      (Σ-cong-iso-snd
-- -- -- -- -- -- -- -- -- -- -- -- --       (λ c → invIso (Σ-cong-iso-fst
-- -- -- -- -- -- -- -- -- -- -- -- --         (compIso idIso
-- -- -- -- -- -- -- -- -- -- -- -- --           (Σ-cong-iso-fst (invIso (domIso (Bool→ (fst ∘ A)))))))))
-- -- -- -- -- -- -- -- -- -- -- -- --      (compIso
-- -- -- -- -- -- -- -- -- -- -- -- --        (Σ-cong-iso-snd (λ p
-- -- -- -- -- -- -- -- -- -- -- -- --          → Σ-cong-iso-snd λ r
-- -- -- -- -- -- -- -- -- -- -- -- --            → compIso
-- -- -- -- -- -- -- -- -- -- -- -- --              (Bool→ (λ x → (a : A x .fst) →
-- -- -- -- -- -- -- -- -- -- -- -- --               r .fst (Iso.fun (Bool→ (λ x → A x .fst)) (RPfun Bool* A x a))
-- -- -- -- -- -- -- -- -- -- -- -- --               ≡ Iso.inv (Bool→ (λ _ → fst C)) p x))
-- -- -- -- -- -- -- -- -- -- -- -- --              (pathToIso
-- -- -- -- -- -- -- -- -- -- -- -- --               (cong₂ _×_
-- -- -- -- -- -- -- -- -- -- -- -- --                 (λ i → (a : A true .fst)
-- -- -- -- -- -- -- -- -- -- -- -- --                   → r .fst ((transportRefl a i) , (A false .snd))
-- -- -- -- -- -- -- -- -- -- -- -- --                    ≡ fst p)
-- -- -- -- -- -- -- -- -- -- -- -- --                 λ i → (a : A false .fst)
-- -- -- -- -- -- -- -- -- -- -- -- --                   → r .fst (A true .snd , transportRefl a i)
-- -- -- -- -- -- -- -- -- -- -- -- --                    ≡ snd p))))
-- -- -- -- -- -- -- -- -- -- -- -- --        AS))
-- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- --   AS : Iso
-- -- -- -- -- -- -- -- -- -- -- -- --     (Σ[ p ∈ fst C × fst C ]
-- -- -- -- -- -- -- -- -- -- -- -- --       Σ[ f ∈ (A true ×∙ A false) →∙ C ]
-- -- -- -- -- -- -- -- -- -- -- -- --         ((a : A true .fst) → fst f (a , A false .snd) ≡ fst p)
-- -- -- -- -- -- -- -- -- -- -- -- --       × (((a : A false .fst) → fst f (A true .snd , a) ≡ snd p)))
-- -- -- -- -- -- -- -- -- -- -- -- --     (Smash⋆ (A true) (A false) →∙ C)
-- -- -- -- -- -- -- -- -- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) basel = c1
-- -- -- -- -- -- -- -- -- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) baser = c2
-- -- -- -- -- -- -- -- -- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) (proj x y) = f (x , y)
-- -- -- -- -- -- -- -- -- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) (gluel a i) = l a i
-- -- -- -- -- -- -- -- -- -- -- -- --   fst (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) (gluer b i) = r b i
-- -- -- -- -- -- -- -- -- -- -- -- --   snd (Iso.fun AS ((c1 , c2) , (f , p) , l , r)) = p
-- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv AS (f , p) = (f basel , f baser)
-- -- -- -- -- -- -- -- -- -- -- -- --     , ((λ x → f (proj (x .fst) (x .snd)))
-- -- -- -- -- -- -- -- -- -- -- -- --     , p)
-- -- -- -- -- -- -- -- -- -- -- -- --     , (λ a → cong f (gluel a))
-- -- -- -- -- -- -- -- -- -- -- -- --     , (λ a → cong f (gluer a))
-- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv AS (f , p) =
-- -- -- -- -- -- -- -- -- -- -- -- --     ΣPathP ((funExt (λ { basel → refl
-- -- -- -- -- -- -- -- -- -- -- -- --       ; baser → refl
-- -- -- -- -- -- -- -- -- -- -- -- --       ; (proj x y) → refl
-- -- -- -- -- -- -- -- -- -- -- -- --       ; (gluel a i) → refl
-- -- -- -- -- -- -- -- -- -- -- -- --       ; (gluer b i) → refl})) , refl)
-- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv AS _ = refl


-- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom : (X : RP∞) (A : fst X → Pointed₀) (C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHom X A C =
-- -- -- -- -- -- -- -- -- -- -- -- -- --   Σ[ f ∈ (((x : fst X) → A x .fst) → C .fst) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- --     Σ[ r ∈ ((e : fst X ≃ Bool) (x : {!!}) (y : _)
-- -- -- -- -- -- -- -- -- -- -- -- -- --       → liftHom X A (fst C) e f {!!} {!!} ≡ {!!}) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- --       ((e : fst X ≃ Bool)
-- -- -- -- -- -- -- -- -- -- -- -- -- --       → {!!} ≡ {!funExt⁻ (r (compEquiv e notEquiv) (A (invEq (compEquiv e notEquiv) true) .snd)) !})

-- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHomK : (X : RP∞) (n : fst X → ℕ) → hProp ℓ-zero
-- -- -- -- -- -- -- -- -- -- -- -- -- -- BiHomK = uncurry λ X → rec→Set (isSetΠ (λ _ → isSetHProp))
-- -- -- -- -- -- -- -- -- -- -- -- -- --   (λ f n → (Σ[ g ∈ ((K∙ (n (invEq f true))) ⋀∙ (K∙ (n (invEq f false))))
-- -- -- -- -- -- -- -- -- -- -- -- -- --                 →∙ K∙ (n (invEq f true)
-- -- -- -- -- -- -- -- -- -- -- -- -- --                       + n (invEq f false)) ]
-- -- -- -- -- -- -- -- -- -- -- -- -- --               {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- --             , {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- --   {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- PushT : (A B C : Pointed₀) → Type
-- -- -- -- -- -- -- -- -- -- -- -- -- -- PushT A B C = {!Pushout ? ?!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- data ASD (X Y : RP∞) (A : fst X → fst Y → Pointed₀) : Type where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   marp : ((x : _) (y : _) → A x y .fst) → ASD X Y A
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   marp' : (y : fst Y) (z : (x : fst X) → A x y .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → marp (λ x → CasesRP Y y (z x) (A x (not* Y y) .snd))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ≡ marp λ x y → A x y .snd

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mapInto : (X Y : RP∞) (A : fst X → fst Y → Pointed₀)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   → ASD X Y A  → ((y : fst Y) → ⋀∞ X (λ x → A x y)) 
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mapInto X Y A (marp x) = λ y → proj λ z → x z y
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mapInto X Y A (marp' y z i) p = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   lem : (λ (z₁ : fst X) → CasesRP Y {A = λ y → A z₁ y .fst} y (z z₁) (A z₁ (not* Y y) .snd) p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --       ≡ CasesRP X {!p !} {!!} {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   lem = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   (({!!} ∙ gl {X = X} {!z x!} {!!}) ∙ {!!}) i
-- -- -- -- -- -- -- -- -- -- -- -- -- -- --   -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i0 ⊢ proj (λ z₁ → CasesRP Y y (z z₁) (A z₁ (not* Y y) .snd) p)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- i = i1 ⊢ proj (λ z₁ → A z₁ p .snd)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- mapInto X Y A (marp x) y = proj (λ s → x s y)

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→' : (X Y : RP∞) (n : fst X → fst Y → ℕ)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → SS' X Y n .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     → K (∑RP Y (λ y → ∑RP X (λ x → n x y)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→' X Y n (genSmash.proj x) =
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     ⌣gen Y (λ y → ∑RP X (λ x₁ → n x₁ y)) .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       (proj λ y → {!⌣gen Y ?!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→' X Y n (genSmash.base x) = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   SS→' X Y n (genSmash.gl x a i) = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   {-
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help : ⌣gen X (λ x₁ → ∑RP Y (n x₁)) .fst (proj (λ x₂ →
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ⌣gen Y (n x₂) .fst
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             (CasesRP X x a (proj (λ x₃ → K∙ (n (not* X x) x₃) .snd)) x₂)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --          ≡ 0ₖ (∑RP X (λ x₁ → ∑RP Y (n x₁)))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --     help = cong (⌣gen X (λ x₁ → ∑RP Y (n x₁)) .fst)
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --               {!genSmash.gl x a !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --           ∙ {!a!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       where
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       lem : (z : _) → CasesRP X {A = λ x → ⋀∞ Y (λ X₁ → K∙ (n x X₁))}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --                x a (proj (λ x₃ → K∙ (n (not* X x) x₃) .snd)) z
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --             ≡ proj (CasesRP Y {!!} {!!} {!!})
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --       lem z = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   doublerMash : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   doublerMash = {!!}

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ⌣gen : {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- ⌣gen = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- myP : {!{ℓ : Level} (A : Bool → Pointed ℓ) → Iso (genSmash.⋀∞ !}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- myP = {!!}


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   ⋀∞Bool : Iso (⋀∞ Bool* A) (Smash (A true) (A false))
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.fun ⋀∞Bool = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.inv ⋀∞Bool = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.rightInv ⋀∞Bool = {!!}
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --   Iso.leftInv ⋀∞Bool = {!!}

