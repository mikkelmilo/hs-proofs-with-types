{-# LANGUAGE 
    TypeOperators, 
    GADTs, 
    ScopedTypeVariables, 
    MultiParamTypeClasses,
    FunctionalDependencies,
    FlexibleInstances,
    UndecidableInstances,
    EmptyCase,
    DataKinds,
    PolyKinds,
    TypeFamilies,
    AllowAmbiguousTypes
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}


module PeanoNumbers where

    import PropTypes
    -- inspired by https://typesandkinds.wordpress.com/2012/12/01/decidable-propositional-equality-in-haskell/
    type DecidableEquality a b = Or (Equal a b) (Not (Equal a b))
    
    data Nat = Z | S Nat

    -- addition on type-level. Note that DataKind and TypeFamilies are necessary for this.
    infixl 6 :+
    type family   (n :: Nat) :+ (m :: Nat) :: Nat
    type instance Z     :+ m = m
    type instance (S n) :+ m = S (n :+ m)
    data SNat :: Nat -> * where
        SZero :: SNat Z
        SSucc :: SNat n -> SNat (S n)
    
    decNatEq :: SNat a -> SNat b -> DecidableEquality a b
    decNatEq SZero SZero = OrL Refl
    decNatEq (SSucc x') (SSucc y') = case decNatEq x' y' of
        OrL Refl -> OrL Refl
        OrR contra -> OrR (\y -> case y of Refl -> contra Refl)
    decNatEq SZero (SSucc _) = OrR (\y -> case y of {}) -- impossible case
    decNatEq (SSucc _) SZero = OrR (\y -> case y of {}) -- impossible case

    one = SSucc SZero
    two = SSucc one
    three = SSucc two
    
    eq3 :: DecidableEquality three three
    eq3 = OrL Refl
    
    succCong :: (Equal n m) -> Equal (SSucc n) (SSucc m)
    succCong Refl = Refl

    predCong :: Equal (SSucc n) (SSucc m) -> Equal n m
    predCong Refl = Refl 

    plusCong :: (Equal n m) -> (Equal p q) -> Equal (n :+ p) (m :+ q)
    plusCong Refl Refl = Refl

    plusAssoc :: SNat a -> SNat b -> SNat c -> Equal (a :+ (b :+ c)) ((a :+ b) :+ c)
    plusAssoc SZero b c = Refl 
    plusAssoc (SSucc a) b c = gcastWith (plusAssoc a b c) Refl 

    --plus_fact1 :: Equal (one :+ two) three
    --plus_fact1 = Refl

    --twoNotEqThree :: (Equal Two Three) -> Void
    --twoNotEqThree contra = Refl   
