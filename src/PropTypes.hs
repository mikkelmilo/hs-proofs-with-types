{-# LANGUAGE 
    TypeOperators, 
    GADTs, 
    ScopedTypeVariables, 
    MultiParamTypeClasses,
    FunctionalDependencies,
    FlexibleInstances,
    UndecidableInstances
#-}

module PropTypes () where

-- Representation of the false proposition. 
-- Since this type has no constructor, no data inhabits this type (=there is no way to prove it)
data FalseP

data Equal a b where
    Refl :: Equal a a

-- Logical connectives --

type NotP a = a -> FalseP 

type AndP a b = (a,b) 

data OrP a b = OrL a | OrR b

exfalso :: forall a. FalseP -> a
exfalso contra = a

andI :: a -> b -> AndP a b
andI a b = (a,b)

andER :: AndP a b -> a
andER (a,b) = a

andEL :: AndP a b -> b
andEL (a,b) = b

orIL :: a -> OrP a b
orIL a = OrL a

orIR :: b -> OrP a b
orIR b = OrR b

orE :: (OrP a b) -> (a -> q) -> (b -> q) -> q
orE (OrL a) f _ = f a
orE (OrR b) _ g = g b

data Z 
data S a

class Add a b ab | a b -> ab
instance Add Z b b
instance (Add a b ab) => Add (S a) b (S ab)
-- redundant?
instance (Add a b ab) => (Add b a ab)

type One = S Z 
type Two = S One 
type Three = S Two

eq3 :: Equal Three Three
eq3 = Refl

absurdium :: FalseP -> a
absurdium = FalseP

twoNotEqThree :: NotP (Equal Two Three)
twoNotEqThree = (\x Refl -> FalseP)

impliesTrans :: (a -> b) -> (b -> c) -> a -> c
impliesTrans f g = g . f -- equivalent to impliesTrans f g x = g (f x)
