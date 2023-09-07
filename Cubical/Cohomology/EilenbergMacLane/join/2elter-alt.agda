{-# OPTIONS --safe --lossy-unification #-}

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
open import Cubical.Cohomology.EilenbergMacLane.join.prelims

open import Cubical.Cohomology.EilenbergMacLane.join.2elter
module Cubical.Cohomology.EilenbergMacLane.join.2elter-alt where
open import Cubical.HITs.Join
open import Cubical.Functions.FunExtEquiv


module 2-elter' {ℓ : Level} (I : RP∞' ℓ) (J : Type) (A : fst I → J → Type ℓ) where
  private
    I2 = snd I
  notI : fst I → fst I
  notI = I2 .fst .fst

  elimI : {B : fst I → Type ℓ} → _
  elimI {B} = I2 .fst .snd .snd B .fst

  elimIβ : {B : fst I → Type ℓ} → _
  elimIβ {B} = I2 .fst .snd .snd B .snd

  elimIη : {B : fst I → Type ℓ} (g : (x : _) → B x) (i : fst I) → elimI i (g i) (g (notI i)) ≡ g
  elimIη g i = funExt (elimI i (elimIβ i (g i) (g _) .fst) (elimIβ i (g i) (g _) .snd))

  elimIη-id : {B : fst I → Type ℓ} (g : (x : _) → B x) (i : fst I)
    → (funExt⁻ (elimIη g i) i  ≡ elimIβ i (g i) (g (notI i)) .fst)
    × (funExt⁻ (elimIη g i) (notI i)  ≡ elimIβ i (g i) (g (notI i)) .snd)
  elimIη-id = λ g i → elimIβ {B = λ i → _ ≡ _} i (elimIβ i (g i) (g _) .fst) (elimIβ i (g i) (g _) .snd)

  ΠR-baseB = Σ[ f ∈ (TotΠ λ i → Σ[ j ∈ J ] (A i j)) ]
        (Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
          ((i : fst I) → g i (f i .fst) ≡ f i .snd))

  eval : J ⊎ (fst I ≃ J) → fst I → J 
  eval = evalG

  ΠR-baseN1 =
    Σ[ fg ∈ (Σ[ f ∈ J ⊎ (fst I ≃ J) ] ((i : fst I) → A i (eval f i))) ]
        (Σ[ g ∈ ((i : fst I) (j : J) → A i j) ]
          ((i : fst I) → g i (eval (fst fg) i) ≡ snd fg i))

  ΠR-base-back = (J ⊎ (fst I ≃ J)) × ((i : fst I) (j : J) → A i j)

  ΠR-base-back→Σ : ΠR-base-back → Σ[ e ∈ J ⊎ (fst I ≃ J) ] ((i : fst I) → A i (eval e i))
  ΠR-base-back→Σ (f , g) = f , λ i → g i (eval f i)

  ΠR-base-back→Π : ΠR-base-back → TotΠ (λ i → TotΠ (λ j → A i j))
  ΠR-base-back→Π = snd

  ΠR-base : Type _
  ΠR-base = Pushout {A = ΠR-base-back}
                    {B = Σ[ e ∈ J ⊎ (fst I ≃ J) ] ((i : fst I) → A i (eval e i))}
                    {C = TotΠ (λ i → TotΠ (λ j → A i j))}
                    ΠR-base-back→Σ
                    ΠR-base-back→Π


  left-push : Type _
  left-push = Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)

  left-push↑ₗ : fst I → Type _
  left-push↑ₗ i =  Σ[ e ∈ J ⊎ (fst I ≃ J) ] A i (eval e i) × ((j : J) → A (notI i) j)

  left-push↑ᵣ : fst I → Type _
  left-push↑ᵣ i = J × ((i : fst I) (j : J) → A i j)

  fat : Type _
  fat = (J ⊎ (fst I ≃ J)) × (((i : fst I) (j : J) → A i j))

  fat→ₗ : (i : fst I) → fat → left-push↑ₗ i
  fat→ₗ i (f , g) = f , ((g i (eval f i)) , (g (notI i)))

  fat→ᵣ : (i : fst I) → fat → left-push↑ᵣ i
  fat→ᵣ i (f , g) = eval f i , g

  PushTop : Type _
  PushTop = Σ[ i ∈ fst I ] (Pushout (fat→ₗ i) (fat→ᵣ i))

  PushTop→left-push' : (i : fst I)
    → (Pushout (fat→ₗ i) (fat→ᵣ i))
    → (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)
  PushTop→left-push' i (inl (f , g)) = (eval f i , g .fst) , g .snd
  PushTop→left-push' i (inr (f , g)) = (f , g i f) , (g (notI i))
  PushTop→left-push' i (push (f , g) k) = ((eval f i) , (g i (eval f i))) , g (notI i)

  PushTop→left-push : PushTop → left-push
  PushTop→left-push (i , x) = (i , PushTop→left-push' i x)

  inrΠR : _ → ΠR-base
  inrΠR = inr

  elimIηPushTop : (i : fst I) (x : J ⊎ (fst I ≃ J)) (g : (i₂ : fst I) (j₁ : J) → A i₂ j₁)
    → _ ≡ _
  elimIηPushTop i x g = elimIη {B = λ i → A i (eval x i)} (λ i' → g i' (eval x i')) i

  PushTop→ΠR-base : PushTop → ΠR-base
  PushTop→ΠR-base (i , inl (f , g)) = inl (f , elimI i (fst g) (snd g _))
  PushTop→ΠR-base (i , inr (f , g)) = inr g -- inr g
  PushTop→ΠR-base (i , push (x , g) i₁) =
      ((λ j → inl (x , elimIηPushTop i x g j))
    ∙ push (x , g)) i₁

  ΠR-extend : Type _
  ΠR-extend = Pushout PushTop→left-push PushTop→ΠR-base


  ΠR-extend→Πₗ : left-push → TotΠ (λ i → joinR-gen J (A i))
  ΠR-extend→Πₗ (i , p , r) = elimI i (inlR p) (inrR r)

  ΠR-base→ : ΠR-base → TotΠ (λ i → joinR-gen J (A i))
  ΠR-base→ (inl (f , p)) i = inlR ((eval f i) , (p i))
  ΠR-base→ (inr x) i = inrR (x i)
  ΠR-base→ (push a i') i = push* (eval (fst a) i , snd a i _) (snd a i) refl i'


  pre-eqvl-diag : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) i'
     ≡ ΠR-base→ (PushTop→ΠR-base (i' , p)) i'
  pre-eqvl-diag i' (inl (f , g)) = elimIβ i' (inlR (eval f i' , g .fst)) (inrR (g .snd)) .fst
                                 ∙ cong inlR (ΣPathP (refl , sym (elimIβ i' (g .fst) (g .snd _) .fst)))
  pre-eqvl-diag i' (inr (f , g)) =
    elimIβ {B = λ x → joinR-gen J (A x) } i' (inlR (f , g i' f)) (inrR (g (notI i'))) .fst  ∙ push* (f , g i' f) (g i') refl
  pre-eqvl-diag i' (push (f , g) i) j =
    hcomp (λ k → λ {(i = i0) → (elimIβ {B = λ i → joinR-gen J (A i)} i'
                                   (inlR (eval f i' , g i' (eval f i')))
                                   (inrR (g (notI i'))) .fst
                                 ∙ cong inlR (ΣPathP (refl , sym (elimIη-id (λ i' → g i' (eval f i')) i' .fst k)))) j
                   ; (i = i1) → compPath-filler
                                   (elimIβ {B = λ i → joinR-gen J (A i)} i'
                                     (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .fst)
                                   (push*  (eval f i' , g i' (eval f i'))
                                           (g i')
                                           refl) k j
                   ; (j = i0) → ΠR-extend→Πₗ (PushTop→left-push (i' , push (f , g) i)) i'
                   ; (j = i1) → ΠR-base→ ((compPath-filler (λ j → inl (f , elimIη (λ i' → g i' (eval f i')) i' j)) (push (f , g)) k i)) i'})
      (hcomp (λ k → λ {(i = i0) → compPath-filler
                                      (elimIβ {B = λ i → joinR-gen J (A i)} i'
                                       (inlR (eval f i' , g i' (eval f i')))
                                       (inrR (g (notI i'))) .fst)
                                    (cong inlR (ΣPathP (refl , sym (funExt⁻ (elimIη (λ i'' → g i'' (eval f i'')) i') i')))) k j
                   ; (i = i1) → elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .fst j
                   ; (j = i0) → ΠR-extend→Πₗ (PushTop→left-push (i' , push (f , g) i)) i'
                   ; (j = i1) → inlR ((eval f i') , elimIη (λ i'' → g i'' (eval f i'')) i' (i ∨ ~ k) i')
                   })
                   (elimIβ {B = λ i → joinR-gen J (A i)} i' (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .fst j))


  pre-eqvl-not : (i' : fst I) (p : Pushout (fat→ₗ i') (fat→ᵣ i'))
    → ΠR-extend→Πₗ (PushTop→left-push (i' , p)) (notI i') ≡
      ΠR-base→ (PushTop→ΠR-base (i' , p)) (notI i')
  pre-eqvl-not i' (inl (f , g)) =
      elimIβ i' (inlR (eval f i' , g .fst)) (inrR (g .snd)) .snd
    ∙ sym (push* (eval f (notI i') , _) (g .snd) (sym (elimIβ i' (fst g)  (snd g (eval f (notI i'))) .snd)))
  pre-eqvl-not i' (inr (f , g)) = elimIβ {B = λ x → joinR-gen J (A x)} i' (inlR (f , g i' f)) (inrR (g (notI i'))) .snd
  pre-eqvl-not i' (push (f , g) i) j =
    hcomp (λ r → λ {(i = i0) → (elimIβ {B = λ x → joinR-gen J (A x)} i' (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .snd
                               ∙ sym (push* (eval f (notI i') , elimI {B = (λ z → A z (eval f z))} i' (g i' (eval f i')) (g (notI i') (eval f (notI i'))) (notI i'))
                                          (g (notI i'))
                                          ((sym ((elimIη-id (λ x → g x (eval f x)) i') .snd r))))) j
                   ; (i = i1) → elimIβ {B = λ x → joinR-gen J (A x)} i'
                                  (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .snd j
                   ; (j = i0) → elimI {B = λ x → joinR-gen J (A x)} i'
                                  (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) (notI i')
                   ; (j = i1) → ΠR-base→ (compPath-filler'
                                            (λ i → inl (f , elimIη (λ x → g x (eval f x)) i' i))
                                            (push (f , g)) i1 i) (notI i')
                   })
      (hcomp (λ r → λ {(i = i0) → (elimIβ {B = λ x → joinR-gen J (A x)} i' (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .snd
                                  ∙ sym (push* (eval f (notI i') , elimIη (λ x → g x (eval f x)) i' (~ r) (notI i'))
                                           (g (notI i'))
                                           λ i → elimIη (λ x → g x (eval f x)) i' (~ r ∨ ~ i) (notI i'))) j
                   ; (i = i1) → elimIβ {B = λ x → joinR-gen J (A x)} i'
                                  (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .snd j
                   ; (j = i0) → elimI {B = λ x → joinR-gen J (A x)} i'
                                  (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) (notI i')
                   ; (j = i1) → ΠR-base→ (compPath-filler'
                                            (λ i → inl (f , elimIη (λ x → g x (eval f x)) i' i))
                                            (push (f , g)) r i) (notI i') })
                   (compPath-filler (elimIβ {B = λ x → joinR-gen J (A x)} i' (inlR (eval f i' , g i' (eval f i'))) (inrR (g (notI i'))) .snd)
                                    (sym (push* (eval f (notI i') , g (notI i') (eval f _)) (g (notI i')) refl))
                                    (~ i) j))

  eqvl : (a : PushTop) (i : fst I)
    → ΠR-extend→Πₗ (PushTop→left-push a) i
     ≡ ΠR-base→ (PushTop→ΠR-base a) i
  eqvl (i' , p) =
    elimI i' (pre-eqvl-diag i' p)
             (pre-eqvl-not i' p)

  ΠR-extend→Π : ΠR-extend → TotΠ (λ i → joinR-gen J (A i))
  ΠR-extend→Π (inl t) = ΠR-extend→Πₗ t
  ΠR-extend→Π (inr x) = ΠR-base→ x
  ΠR-extend→Π (push a i) i' = eqvl a i' i

  left-push→double : left-push → joinR-gen J λ j → joinR-gen (fst I) (λ i → A i j)
  left-push→double (i , (c , r)) = inlR ((c .fst) , (inrR (elimI i (c .snd) (r (c .fst)))))



{- gens -}
  ΠR-base-back* = J × ((i : fst I) (j : J) → A i j)
  left-push↑ₗ* : fst I → Type _
  left-push↑ₗ* i =  Σ[ e ∈ J ] A i e × ((j : J) → A (notI i) j)
  fat* : Type _
  fat* = J × ((i : fst I) (j : J) → A i j)

  fat→ₗ* : (i : fst I) → fat* → left-push↑ₗ* i
  fat→ₗ* i (f , g) = f , (g i f) , (g (notI i))

  fat→ᵣ* : (i : fst I) → fat* → left-push↑ᵣ i
  fat→ᵣ* i (f , g) = f , g

  ΠR-base* : Type _
  ΠR-base* = Pushout {A = ΠR-base-back*}
                    {B = Σ[ e ∈ J ] ((i : fst I) → A i e)}
                    {C = TotΠ (λ i → TotΠ (λ j → A i j))}
                    (λ x → (fst x) , (λ i → snd x i (fst x)))
                    snd

  PushTop* : Type _
  PushTop* = Σ[ i ∈ fst I ] (Pushout (fat→ₗ* i) (fat→ᵣ* i))

  elimIηPushTop* : (i : fst I) (x : J) (g : (i₂ : fst I) (j₁ : J) → A i₂ j₁)
    → _ ≡ _
  elimIηPushTop* i x g = elimIηPushTop i (inl x) g --  -- elimIη (λ i' → g i' x) i

  PushTop→ΠR-base* : PushTop* → ΠR-base*
  PushTop→ΠR-base* (i , inl (f , g)) = inl (f , elimI i (fst g) (snd g f))
  PushTop→ΠR-base* (i , inr (f , g)) = inr g
  PushTop→ΠR-base* (i , push (x , g) i₁) =
      ((λ j → inl (x , elimIηPushTop* i x g j))
    ∙ push (x , g)) i₁

  PushTop→left-push'* : (i : fst I)
    → (Pushout (fat→ₗ* i) (fat→ᵣ* i))
    → (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)
  PushTop→left-push'* i (inl (f , g)) = (f , g .fst) , g .snd
  PushTop→left-push'* i (inr (f , g)) = (f , g i f) , (g (notI i))
  PushTop→left-push'* i (push (f , g) k) = (f , (g i f)) , g (notI i)

  PushTop→left-push* : PushTop* → Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)
  PushTop→left-push* (i , x) = (i , PushTop→left-push'* i x)

  ΠR-extend* : Type _
  ΠR-extend* = Pushout PushTop→left-push* PushTop→ΠR-base*

  data ΠR-extend** : Type ℓ where
    inl : (Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)) → ΠR-extend**
    inr : ΠR-base* → ΠR-extend**
    pashₗ : (i : fst I) (e : left-push↑ₗ* i)
      → inl (i , ((e .fst , e .snd .fst) , (e .snd .snd)))
       ≡ inr (inl ((e .fst) , (elimI i (e .snd .fst) (e .snd .snd (e .fst)))))
    pashᵣ : (i : fst I) (e : left-push↑ᵣ i)
      → inl (i , ((e .fst , snd e i (e .fst)) , e .snd (notI i))) ≡ inr (inr (snd e))
    pashₗᵣ : (i : fst I) (e : fat*)
      → Square {A = ΠR-extend**}
               (λ j → inr (inl (fst e , elimIηPushTop* i (fst e) (snd e) j)))
               (pashᵣ i e)
               (sym (pashₗ i (fst e , (snd e i (fst e)) , (snd e (notI i)))))
               λ i → inr (push e i)

  data ΠR-extend**↑ : Type ℓ where
    inl : (Σ[ i ∈ fst I ] (Σ[ j ∈ J ] (A i j)) × ((j : J) → A (notI i) j)) → ΠR-extend**↑
    inr : ΠR-base* → ΠR-extend**↑
    pashₗ : (i : fst I) (e : left-push↑ₗ* i)
      → inl (i , ((e .fst , e .snd .fst) , (e .snd .snd)))
       ≡ inr (inl ((e .fst) , (elimI i (e .snd .fst) (e .snd .snd (e .fst)))))

  module _ {ℓ : Level} {A : ΠR-extend** → Type ℓ}
       (inl* : (x : _) → A (inl x))
       (inr* : (x : _) → A (inr x))
       (pashₗ* : (i : fst I) (e : left-push↑ₗ* i)
              → PathP (λ j → A (pashₗ i e j))
                       (inl* (i , (fst e , snd e .fst) , (snd e .snd)))
                       (inr* (inl (fst e , elimI i (e .snd .fst) (e .snd .snd (fst e))))))
    where
    private
      filler : (i : fst I) (e : left-push↑ᵣ i) (j k : Cubical.Foundations.Prelude.I)
        → A (pashₗᵣ i e k j)
      filler i e j k =
        fill (λ k → A (pashₗᵣ i e k j))
             (λ k → λ {(j = i0) → pashₗ* i (fst e , snd e i (fst e) , snd e (notI i)) (~ k)
                      ; (j = i1) → inr* (push e k)})
             (inS (inr* (inl ((fst e) , (elimIηPushTop* i (fst e) (snd e) j)))))
             k

    ΠR-extend**-elim : (x : _) → A x
    ΠR-extend**-elim (inl x) = inl* x
    ΠR-extend**-elim (inr x) = inr* x
    ΠR-extend**-elim (pashₗ i e i₁) = pashₗ* i e i₁
    ΠR-extend**-elim (pashᵣ i e i₁) = filler i e i₁ i1
    ΠR-extend**-elim (pashₗᵣ i e j k) = filler i e k j


  data asPushoutBack (e : fst I ≃ J) : Type ℓ where
    ppl : (f : (i₁ : fst I) (j : J) → A i₁ j) → asPushoutBack e
    ppr : (i : fst I) (a : A i (fst e i)) (b : ((j : J) → A (notI i) j)) → asPushoutBack e
    pplr : (i : fst I) (f : (i₁ : fst I) (j : J) → A i₁ j)
      → ppl f ≡ ppr i (f i (fst e i)) (f (notI i))

  asPushoutBack→ₗ : Σ[ e ∈ (fst I ≃ J) ] (asPushoutBack e) → ΠR-extend**
  asPushoutBack→ₗ (e , ppl f) = inr (inr f)
  asPushoutBack→ₗ (e , ppr i a b) = inl (i , (fst e i , a) , b)
  asPushoutBack→ₗ (e , pplr i f i₁) = (pashᵣ i ((fst e i) , f)) (~ i₁)

  asPushoutBack→ₗ↑ : Σ[ e ∈ (fst I ≃ J) ] (asPushoutBack e) → ΠR-extend**↑
  asPushoutBack→ₗ↑ (e , ppl f) = inr (inr f)
  asPushoutBack→ₗ↑ (e , ppr i a b) = inl (i , (fst e i , a) , b)
  asPushoutBack→ₗ↑ (e , pplr i f i₁) =
    ((λ k → inr (push ((fst e i) , f) (~ k)))
    ∙∙ (λ i₁ → inr (inl (fst e i
             , elimIη (λ j → f j (fst e i)) i (~ i₁))))
    ∙∙ sym (pashₗ i ((fst e i) , ((f i (fst e i)) , (f (notI i)))))) i₁

  asPushoutBack→ᵣ-pre : (e : fst I ≃ J) → asPushoutBack e → (i : fst I) → A i (fst e i)
  asPushoutBack→ᵣ-pre e (ppl f) i = f i (fst e i)
  asPushoutBack→ᵣ-pre e (ppr i₁ a b) = elimI i₁ a (b (fst e (notI i₁)))
  asPushoutBack→ᵣ-pre e (pplr i₁ f i₂) =
    elimIη {B = λ i → A i (fst e i)} (λ i → f i (fst e i)) i₁ (~ i₂)

  asPushoutBack→ᵣ : Σ[ e ∈ (fst I ≃ J) ] (asPushoutBack e) → Σ[ e ∈ (fst I ≃ J) ] ((i : fst I) → A i (fst e i))
  asPushoutBack→ᵣ (e , t) = e , asPushoutBack→ᵣ-pre e t

  asPushout : Type ℓ
  asPushout = Pushout asPushoutBack→ₗ asPushoutBack→ᵣ

  asPushout' : Type ℓ
  asPushout' = Pushout asPushoutBack→ₗ↑ asPushoutBack→ᵣ

  ΠR-extend**Iso : Iso ΠR-extend**↑ ΠR-extend**
  Iso.fun ΠR-extend**Iso (inl x) = inl x
  Iso.fun ΠR-extend**Iso (inr x) = inr x
  Iso.fun ΠR-extend**Iso (pashₗ i e i₁) = pashₗ i e i₁
  Iso.inv ΠR-extend**Iso = ΠR-extend**-elim inl inr pashₗ
  Iso.rightInv ΠR-extend**Iso = ΠR-extend**-elim (λ _ → refl) (λ _ → refl) λ _ _ _ → refl
  Iso.leftInv ΠR-extend**Iso (inl x) = refl
  Iso.leftInv ΠR-extend**Iso (inr x) = refl
  Iso.leftInv ΠR-extend**Iso (pashₗ i e i₁) = refl

  as** : Iso asPushout' asPushout
  as** = pushoutIso _ _ _ _
    (idEquiv _)
    (isoToEquiv ΠR-extend**Iso)
    (idEquiv _)
    (funExt
    (λ { (e , ppl f) → refl
       ; (e , ppr i a b) → refl
       ; (e , pplr i f i₁) j
       → hcomp (λ k → λ {(j = i0) → ΠR-extend**Iso .Iso.fun
         (doubleCompPath-filler (λ k → inr (push ((fst e i) , f) (~ k)))
            (λ i₁ → inr (inl (fst e i
                        , elimIη (λ j → f j (fst e i)) i (~ i₁))))
            (sym (pashₗ i ((fst e i) , ((f i (fst e i)) , (f (notI i))))))
            k i₁)
                         ; (j = i1) → pashₗᵣ i (fst e i , f) k (~ i₁)
                         ; (i₁ = i0) → inr (push (fst e i , f) k)
                         ; (i₁ = i1) → pashₗ i (fst e i , f i (fst e i)
                                              , f (notI i)) (~ k)})
                (inr (inl (fst e i , elimIη (λ j₁ → f j₁ (fst e i)) i (~ i₁))))}))
       refl

  ΠR-base→asPushout : ΠR-base → asPushout
  ΠR-base→asPushout (inl (inl x , b)) = inl (inr (inl (x , b)))
  ΠR-base→asPushout (inl (inr x , b)) = inr (x , b)
  ΠR-base→asPushout (inr x) = inl (inr (inr x))
  ΠR-base→asPushout (push (inl x , b) i) = inl (inr (push (x , b) i))
  ΠR-base→asPushout (push (inr x , b) i) = push (x , (ppl b)) (~ i)

  Paths→asPushoutₗ-fill : (e : fst I) (x : J)
    (b : (i₂ : fst I) (j : J) → A i₂ j)
    (i₁ i k : Cubical.Foundations.Prelude.I)
    → asPushout
  Paths→asPushoutₗ-fill e x b i₁ i k =
    hfill (λ k → λ {(i = i0) → inl (pashₗ e (x , b e x , b (notI e)) (~ k))
                   ; (i = i1) → ΠR-base→asPushout (compPath-filler (λ i₁ → (inl (inl x , elimIηPushTop e (inl x) b i₁)))
                                                    (push (inl x , b)) k i₁)
                   ; (i₁ = i0) → inl (pashₗ e (x , b e x , b (notI e)) (i ∨ ~ k))
                   ; (i₁ = i1) → inl (pashₗᵣ e (x , b) k i)})
          (inS (inl ((inr (inl (x , elimIηPushTop e (inl x) b (i₁ ∧ i)))))))
          k

  Paths→asPushoutᵣ-fill : (e : fst I) (x : fst I ≃ J) (b : (i₂ : fst I) (j : J) → A i₂ j)
    (i₁ i k : Cubical.Foundations.Prelude.I)
    → asPushout
  Paths→asPushoutᵣ-fill e x b i₁ i k =
    hfill (λ k → λ {(i = i0) → inl (pashᵣ e (fst x e , b) (~ k))
                   ; (i = i1) → ΠR-base→asPushout
                                  (compPath-filler' (λ i₁ → inl (inr x , elimIηPushTop e (inr x) b i₁))
                                    (push (inr x , b)) k i₁)
                   ; (i₁ = i0) → push (x , pplr {e = x} e b k) i
                   ; (i₁ = i1) → inl (pashᵣ e (fst x e , b) (i ∨ ~ k))})
          (inS (push (x , ppl b) (i ∧ ~ i₁)))
          k

  Paths→asPushout : (e : fst I) (b : Pushout (fat→ₗ e) (fat→ᵣ e))
    → inl (inl (e , PushTop→left-push' e b))
     ≡ ΠR-base→asPushout (PushTop→ΠR-base (e , b))
  Paths→asPushout e (inl (inl x , b)) i = inl (pashₗ e (x , b) i)
  Paths→asPushout e (inl (inr x , b)) i = push (x , (ppr e (fst b) (snd b))) i
  Paths→asPushout e (inr x) i = inl (pashᵣ e x i)
  Paths→asPushout e (push (inl x , b) i₁) i = Paths→asPushoutₗ-fill e x b i₁ i i1
  Paths→asPushout e (push (inr x , b) i₁) i = Paths→asPushoutᵣ-fill e x b i₁ i i1

  ΠR-extend→asPushout : ΠR-extend → asPushout
  ΠR-extend→asPushout (inl x) = inl (inl x)
  ΠR-extend→asPushout (inr x) = ΠR-base→asPushout x
  ΠR-extend→asPushout (push (e , b) i) = Paths→asPushout e b i

  asPushout→ΠR-extendₗ-fill : (i : fst I) (e : fat*)
    (i₁ i₂ k : Cubical.Foundations.Prelude.I)
    → ΠR-extend
  asPushout→ΠR-extendₗ-fill i e i₁ i₂ k =
    hfill (λ k → λ {(i₁ = i0) → inr (inl (inl (fst e) , elimIηPushTop* i (fst e) (snd e) (i₂ ∧ k)))
                   ; (i₁ = i1) → push (i , push ((inl (fst e)) , (snd e)) k) i₂
                   ; (i₂ = i0) → push (i , inl (inl (fst e) , snd e i (fst e) , snd e (notI i))) (~ i₁)
                   ; (i₂ = i1) → inr (compPath-filler
                                       (λ j → inl (inl (fst e) , elimIηPushTop i (inl (fst e)) (snd e) j))
                                       (push (inl (fst e) , snd e)) i₁ k)})
          (inS (push (i , inl (inl (fst e) , snd e i (fst e) , snd e (notI i))) (~ i₁ ∨ i₂)))
          k

  asPushout→ΠR-extendᵣ-fill : (e : fst I ≃ J) (f : (i₃ : fst I) (j : J) → A i₃ j)
    (i₁ : fst I)
    (i i₂ k : Cubical.Foundations.Prelude.I)
    → ΠR-extend
  asPushout→ΠR-extendᵣ-fill e f i₁ i i₂ k =
    hfill (λ r → λ {(i = i0) → push (i₁ , push ((inr e) , f) r) (~ i₂)
                   ; (i = i1) → inr (inl ((inr e) , (elimIηPushTop i₁ (inr e) f (~ i₂ ∧ r))))
                   ; (i₂ = i0) → inr (compPath-filler (λ j → inl (inr e , elimIηPushTop i₁ (inr e) f j))
                                      (push (inr e , f)) (~ i) r)
                   ; (i₂ = i1) →  push (i₁ , inl (inr e , f i₁ (fst e i₁) , f (notI i₁))) i})
          (inS (push (i₁ , inl (inr e , f i₁ (fst e i₁) , f (notI i₁))) (i ∨ ~ i₂)))
          k

  ΠR-base*→ΠR-base : ΠR-base* → ΠR-base
  ΠR-base*→ΠR-base (inl x) = inl ((inl (fst x)) , (snd x))
  ΠR-base*→ΠR-base (inr x) = inr x
  ΠR-base*→ΠR-base (push a i) = push (inl (fst a) , snd a) i

  ΠR-base*→ΠR-extend : ΠR-base* → ΠR-extend
  ΠR-base*→ΠR-extend x = inr (ΠR-base*→ΠR-base x)

  ΠR-extend**↑→ΠR-extend** : ΠR-extend**↑ → ΠR-extend
  ΠR-extend**↑→ΠR-extend** (inl x) = inl x
  ΠR-extend**↑→ΠR-extend** (inr x) = ΠR-base*→ΠR-extend x
  ΠR-extend**↑→ΠR-extend** (pashₗ i e i₁) =
    push (i , (inl ((inl (fst e)) , (snd e)))) i₁

  asPushout→ΠR-extend : asPushout → ΠR-extend
  asPushout→ΠR-extend (inl (inl x)) = inl x
  asPushout→ΠR-extend (inl (inr (inl x))) = inr (inl ((inl (fst x)) , (snd x)))
  asPushout→ΠR-extend (inl (inr (inr x))) = inr (inr x)
  asPushout→ΠR-extend (inl (inr (push (x , b) i))) = inr (push ((inl x) , b) i)
  asPushout→ΠR-extend (inl (pashₗ i e i₁)) = push (i , (inl ((inl (fst e)) , (snd e)))) i₁
  asPushout→ΠR-extend (inl (pashᵣ i e i₁)) = push (i , (inr ((fst e) , (snd e)))) i₁
  asPushout→ΠR-extend (inl (pashₗᵣ i e i₁ i₂)) = asPushout→ΠR-extendₗ-fill i e i₁ i₂ i1
  asPushout→ΠR-extend (inr (e , f)) = inr (inl ((inr e) , f))
  asPushout→ΠR-extend (push (e , ppl f) i) = inr (push ((inr e) , f) (~ i))
  asPushout→ΠR-extend (push (e , ppr i₁ a b) i) = push (i₁ , (inl ((inr e) , (a , b)))) i
  asPushout→ΠR-extend (push (e , pplr i₁ f i₂) i) = asPushout→ΠR-extendᵣ-fill e f i₁ i i₂ i1

  ΠR-extend→asPushout→ΠR-extend : (x : ΠR-extend)
    → asPushout→ΠR-extend (ΠR-extend→asPushout x) ≡ x
  ΠR-extend→asPushout→ΠR-extend =
    elimPushout
      (λ _ → refl)
      lefter
      (uncurry
        λ e →
          elimPushout
            (cohₗ e)
            (λ c i j → push (e , inr c) i)
            (uncurry λ { (inl x) → midₗ e x
                        ; (inr x) → midᵣ e x}))
    where
    lefter : (b : ΠR-base) → asPushout→ΠR-extend (ΠR-base→asPushout b)  ≡ (inr b)
    lefter (inl (inl x , snd₁)) = refl
    lefter (inl (inr x , snd₁)) = refl
    lefter (inr x) = refl
    lefter (push (inl x , snd₁) i) = refl
    lefter (push (inr x , snd₁) i) = refl

    cohₗ : (e : fst I) (b : left-push↑ₗ e)
      → PathP (λ i → asPushout→ΠR-extend (Paths→asPushout e (inl b) i) ≡ push (e , inl b) i)
               refl
               (lefter (inl (fst b , elimI e (snd b .fst) (snd b .snd (eval (fst b) (notI e))))))
    cohₗ e (inl x , snd₁) i j = push (e , inl (inl x , snd₁)) i
    cohₗ e (inr x , snd₁) i j = push (e , inl (inr x , snd₁)) i

    midᵣ : (e : fst I) (x : fst I ≃ J) (t : (i₁ : fst I) (j₁ : J) → A i₁ j₁)
      → Cube {A = ΠR-extend}
           (cohₗ e (fat→ₗ e (inr x , t)))
           (λ j k → push (e , inr (fat→ᵣ e (inr x , t))) j)
           (λ r k → inl (PushTop→left-push (e , push (inr x , t) r)))
           (λ r k → lefter (PushTop→ΠR-base (e , push (inr x , t) r)) k)
           (λ r i → asPushout→ΠR-extend
                      (ΠR-extend→asPushout
                       (push (e , push (inr x , t) r) i)))
           λ r i → push (e , push (inr x , t) r) i
    midᵣ e x t r j k =
      hcomp (λ i → λ {(r = i0) → asPushout→ΠR-extendᵣ-fill x t e j i (~ k)
                     ; (r = i1) → push (e , inr (fst x e , t)) (j ∨ ~ i)
                     ; (j = i0) → push (e , push (inr x , t) (r ∨ ~ k)) (~ i)
                     ; (j = i1) → lefter (compPath-filler'
                                            (λ r → inl (inr x , elimIηPushTop e (inr x) t r))
                                            (push (inr x , t)) (k ∨ i) r) k
                     ; (k = i0) → asPushout→ΠR-extend
                                   (Paths→asPushoutᵣ-fill e x t r j i)
                     ; (k = i1) → push (e , push (inr x , t) r) (j ∨ ~ i)})
      (hcomp (λ i → λ {(r = i0) → inr (compPath-filler
                                         (λ j₁ → inl (inr x , elimIηPushTop e (inr x) t j₁))
                                         (push (inr x , t)) (~ j) (~ k ∨ ~ i))
                      ; (r = i1) → inr (inr t)
                      ; (j = i0) → inr (((λ j₁ → inl (inr x , elimIηPushTop e (inr x) t j₁))
                                         ∙ push (inr x , t)) (~ k ∨ (~ i ∨ r)))
                      ; (j = i1) → lefter (compPath-filler'
                                            (λ r → inl (inr x , elimIηPushTop e (inr x) t r))
                                            (push (inr x , t)) (k ∧ i) r) k
                      ; (k = i0) → inr (push (inr x , t) (r ∨ ~ j))
                      ; (k = i1) → inr (bitch-help _
                                         (λ j₂ → inl (inr x , elimIηPushTop e (inr x) t j₂))
                                         _ (push (inr x , t)) i r j)})
              (inr (push (inr x , t) (r ∨ ~ j))))

    midₗ : (e : fst I) (x : J) (t : (i₁ : fst I) (j₁ : J) → A i₁ j₁)
      → Cube {A = ΠR-extend}
          (λ j k → push (e , inl (inl x , t e (eval (inl x) e) , t (notI e))) j)
          (λ j k → push (e , inr (fat→ᵣ e (inl x , t))) j)
          (λ i k → inl (PushTop→left-push (e , push (inl x , t) i)))
          (λ i k → lefter (PushTop→ΠR-base (e , push (inl x , t) i)) k)
          (λ i j → asPushout→ΠR-extend (ΠR-extend→asPushout (push (e , push (inl x , t) i) j)))
          λ i j → push (e , push (inl x , t) i) j
    midₗ e x t i j k =
      hcomp (λ r → λ {(i = i0) → push (e , inl (inl x , t e x , t (notI e))) (j ∨ (~ r ∧ ~ k))
                   ; (i = i1) → asPushout→ΠR-extendₗ-fill e (x , t) (r ∨ k) j i1
                   ; (j = i0) → push (e , inl (inl x , t e x , t (snd I .fst .fst e))) (~ r ∧ ~ k)
                   ; (j = i1) → lefter (compPath-filler (λ j₁ → inl (inl x , elimIηPushTop e (inl x) t j₁))
                                        (push (inl x , t)) (r ∨ k) i) k
                   ; (k = i0) → asPushout→ΠR-extend (Paths→asPushoutₗ-fill e x t i j r)
                   ; (k = i1) → push (e , push (inl x , t) i) j})
        (hcomp (λ r → λ {(i = i0) → push (e , inl (inl x , t e x , t (notI e))) (j ∨ ~ k)
                   ; (i = i1) → asPushout→ΠR-extendₗ-fill e (x , t) k j r
                   ; (j = i0) → push (e , inl (inl x , t e x , t (snd I .fst .fst e))) (~ k)
                   ; (j = i1) → help r i k
                   ; (k = i0) → inr (inl (inl x , elimIηPushTop e (inl x) t (i ∧ (j ∧ r))))
                   ; (k = i1) → push (e , push (inl x , t) (i ∧ r)) j })
              (push (e , inl (inl x , t e x , t (notI e))) (j ∨ ~ k)))
      where
      help : Cube {A = ΠR-extend}
        (λ i k → inr (inl ((inl x) , (elimI e (t e x) (t (notI e) x)))))
        (λ i k → lefter (compPath-filler (λ j₁ → inl (inl x , elimIηPushTop e (inl x) t j₁)) (push (inl x , t)) k i) k)
        (λ r k → inr (inl ((inl x) , (elimI e (t e x) (t (notI e) x)))))
        (λ r k → inr (compPath-filler (λ j₁ → inl (inl x , elimIηPushTop e (inl x) t j₁))
                      (push ((inl x) , t)) k r))
        (λ r i → inr (inl (inl x , elimIηPushTop e (inl x) t (i ∧ r))))
        λ r i → inr (((λ j₁ → inl (inl x , elimIηPushTop e (inl x) t j₁)) ∙ push (inl x , t)) (i ∧ r))
      help r i k =
        hcomp (λ j → λ {(i = i0) → inr (inl ((inl x) , (elimI e (t e x) (t (notI e) x))))
                   ; (i = i1) → inr (compPath-filler (λ j₁ → inl (inl x , elimIηPushTop e (inl x) t j₁)) (push ((inl x) , t)) (k ∧ j) r)
                   ; (r = i0) → inr (inl (inl x , elimI e (t e x) (t (notI e) x)))
                   ; (r = i1) → lefter (compPath-filler (λ j₁ → inl (inl x , elimIηPushTop e (inl x) t j₁)) (push (inl x , t)) (k ∧ j) i) k
                   ; (k = i0) → inr (inl (inl x , elimIηPushTop e (inl x) t (i ∧ r)))
                   ; (k = i1) → inr (compPath-filler (λ j₁ → inl (inl x , elimIηPushTop e (inl x) t j₁)) (push (inl x , t)) j (i ∧ r))})
               ((inr (inl (inl x , elimIηPushTop e (inl x) t (i ∧ r)))))
  
  asPushout→ΠR-extend→asPushout : (x : asPushout) → ΠR-extend→asPushout (asPushout→ΠR-extend x) ≡ x
  asPushout→ΠR-extend→asPushout =
    elimPushout
      lefter
      (λ _ → refl)
      (uncurry pathpp)
    where
    ΠR-baser* : (x : ΠR-base*)
      → ΠR-extend→asPushout (asPushout→ΠR-extend (inl (inr x))) ≡ inl (inr x)
    ΠR-baser* = elimPushout (λ _ → refl) (λ _ → refl) λ a i j → inl (inr (push (fst a , snd a) i))

    lefter : (b : _) → ΠR-extend→asPushout (asPushout→ΠR-extend (inl b)) ≡ inl b
    lefter (inl x) = refl
    lefter (inr x) = ΠR-baser* x
    lefter (pashₗ i e i₁) = refl
    lefter (pashᵣ i e i₁) = refl
    lefter (pashₗᵣ i e j k) r =
      hcomp (λ i' → λ {(r = i0) → ΠR-extend→asPushout
                                    (asPushout→ΠR-extendₗ-fill i e j k i')
                     ; (r = i1) → inl (pashₗᵣ i e j k)
                     ; (k = i0) → inl (pashₗ i (fst e , snd e i (fst e) , snd e (snd I .fst .fst i)) (~ j))
                     ; (k = i1) →  ΠR-extend→asPushout
                                   (inr ((compPath-filler
                                           (λ j₁ → inl (inl (fst e) , elimIηPushTop i (inl (fst e)) (snd e) j₁))
                                           (push (inl (fst e) , (snd e))) j (i' ∨ r))))
                     ; (j = i0) → inl  (inr (inl (fst e , elimIηPushTop* i (fst e) (snd e) (k ∧ (i' ∨ r)))))
                     ; (j = i1) → Paths→asPushoutₗ-fill i (fst e) (snd e) (i' ∨ r) k i1})
            (hcomp (λ i' → λ {(r = i0) → inl (pashₗ i (fst e , snd e i (fst e) , snd e (notI i)) ((~ j ∨ ~ i') ∨ k))
                             ; (r = i1) → inl (pashₗᵣ i e (j ∧ i') k)
                             ; (k = i0) → Paths→asPushoutₗ-fill i (fst e) (snd e) r i0 (i' ∧ j)
                             ; (k = i1) → ΠR-extend→asPushout
                                   (inr ((compPath-filler
                                           (λ j₁ → inl (inl (fst e) , elimIηPushTop i (inl (fst e)) (snd e) j₁))
                                           (push (inl (fst e) , (snd e))) (j ∧ i') r)))
                             ; (j = i0) → inl (inr (inl (fst e , elimIηPushTop* i (fst e) (snd e) (k ∧ r))))
                             ; (j = i1) → Paths→asPushoutₗ-fill i (fst e) (snd e) r k i'})
                           (inl (inr (inl (fst e , elimIηPushTop i (inl (fst e)) (snd e) (r ∧ k))))))


    pathpp : (a : _) (y : asPushoutBack a) →
      PathP
      (λ i →
         ΠR-extend→asPushout (asPushout→ΠR-extend (push (a , y) i)) ≡
         push (a , y) i)
      (lefter (asPushoutBack→ₗ (a , y)))
      (λ _ → inr (asPushoutBack→ᵣ (a , y)))
    pathpp a (ppl f) i j = push (a , ppl f) i
    pathpp a (ppr i a₁ b) j k = push (a , ppr i a₁ b) j
    pathpp a (pplr i f i₁) j k =
      hcomp (λ i' → λ {(k = i0) → ΠR-extend→asPushout (asPushout→ΠR-extendᵣ-fill a f i j i₁ i')
                     ; (k = i1) → help i' j i₁
                     ; (j = i0) → Paths→asPushoutᵣ-fill i a f i' (~ i₁) i1 -- 
                     ; (j = i1) → inr (a , elimIηPushTop i (inr a) f (~ i₁ ∧ i'))
                     ; (i₁ = i0) → ΠR-extend→asPushout (inr
                                     (compPath-filler
                                       (λ j₁ → inl (inr a , elimIηPushTop i (inr a) f j₁))
                                       (push (inr a , f)) (~ j) i'))
                     ; (i₁ = i1) → push (a , ppr i (f i (fst a i)) (f (notI i))) j})
             (push (a , ppr i (f i (fst a i)) (f (snd I .fst .fst i))) (j ∨ ~ i₁))
      where
      help : Cube {A = asPushout}
               (λ j i₁ → push (a , ppr i (f i (fst a i)) (f (snd I .fst .fst i))) (j ∨ ~ i₁))
               (λ j i₁ → push (a , pplr i f i₁) j)
               (λ i' i₁ → Paths→asPushoutᵣ-fill i a f i' (~ i₁) i1)
               (λ i' i₁ → inr (a , elimIηPushTop i (inr a) f (~ i₁ ∧ i')))
               (λ i' j → ΠR-extend→asPushout (inr (compPath-filler
                            (λ j₁ → inl (inr a , elimIηPushTop i (inr a) f j₁))
                            (push (inr a , (λ v v₁ → f v v₁))) (~ j) i')))
               (λ i' j → push (a , ppr i (f i (fst a i)) (f (notI i))) j)
      help i' j i₁ =
        hcomp (λ r → λ {(i' = i0) → push (a , pplr i f r) (j ∨ ~ i₁)
                     ; (i' = i1) → push (a , pplr i f (i₁ ∧ r)) j
                     ; (j = i0) → Paths→asPushoutᵣ-fill i a f i' (~ i₁) r
                     ; (j = i1) → inr (a , elimIηPushTop i (inr a) f (~ r ∨ (i' ∧ ~ i₁)))
                     ; (i₁ = i0) → ΠR-extend→asPushout
                                     (inr (bitch-help' {A = ΠR-base}
                                             _ (λ j₁ → inl (inr a , elimIηPushTop i (inr a) f j₁))
                                             _ (push (inr a , f)) r i' j))
                     ; (i₁ = i1) → push (a , pplr i f r) j})
               (push (a , ppl f) (j ∨ (~ i' ∧ ~ i₁)))

  asPushout→ΠR-extend-Iso : Iso asPushout ΠR-extend
  Iso.fun asPushout→ΠR-extend-Iso = asPushout→ΠR-extend
  Iso.inv asPushout→ΠR-extend-Iso = ΠR-extend→asPushout
  Iso.rightInv asPushout→ΠR-extend-Iso = ΠR-extend→asPushout→ΠR-extend
  Iso.leftInv asPushout→ΠR-extend-Iso = asPushout→ΠR-extend→asPushout
