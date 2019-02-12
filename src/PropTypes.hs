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
     
    impliesTrans :: (a -> b) -> (b -> c) -> a -> c
    impliesTrans f g = g . f -- equivalent to impliesTrans f g x = g (f x)
