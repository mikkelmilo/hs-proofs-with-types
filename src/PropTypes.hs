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
    TypeFamilies
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module PropTypes where

    -- Representation of the false proposition. 
    -- Since this type has no constructor, no data inhabits this type (=there is no way to prove it)
    data Void -- = forall a . a, which is isomorphic to the data type with no constructor
    
    data Equal a b where
        Refl :: Equal a a

    -- Logical connectives --

    type Not a = a -> Void 

    type And a b = (a,b) 

    type Iff a b = And (a -> b) (b -> a)

    data Or a b = OrL a | OrR b

    -- ex falso quodlibet
    absurd :: Void -> a
    absurd contra = case contra of {}

    andI :: a -> b -> And a b
    andI a b = (a,b)

    andER :: And a b -> a
    andER (a,b) = a

    andEL :: And a b -> b
    andEL (a,b) = b

    orIL :: a -> Or a b
    orIL a = OrL a

    orIR :: b -> Or a b
    orIR b = OrR b

    orE :: (Or a b) -> (a -> q) -> (b -> q) -> q
    orE (OrL a) f _ = f a
    orE (OrR b) _ g = g b
     
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

    two = SSucc (SSucc SZero)
    three = SSucc two
    
    eq3 :: DecidableEquality three (SSucc two)
    eq3 = OrL Refl
    
    -- plus_fact1 :: (Sum One Two (S Two))
    -- plus_fact1 = Refl

    -- twoNotEqThree :: (Equal Two Three) -> Void
    -- twoNotEqThree contra =   

    impliesTrans :: (a -> b) -> (b -> c) -> a -> c
    impliesTrans f g = g . f -- equivalent to impliesTrans f g x = g (f x)
