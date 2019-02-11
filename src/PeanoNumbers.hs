{-# LANGUAGE 
    TypeOperators, 
    GADTs, 
    ScopedTypeVariables, 
    MultiParamTypeClasses,
    FunctionalDependencies,
    FlexibleInstances,
    UndecidableInstances,
    EmptyCase
#-}

module PeanoNumbers where
    -- Peano Numbers
    -- heavily inspiered by article.gmane.org/gmane.comp.lang.haskell.general/13223 
    data Z
    data S a
    __ = __

    class Sum2 a b c | a b -> c, a c -> b
    instance Sum2 Z a a
    instance Sum2 a b c => Sum2 (S a) b (S c)

    class Sum a b c | a b -> c, a c -> b, b c -> a
    instance (Sum2 a b c, Sum2 b a c) => Sum a b c


    add :: Sum a b c => a -> b -> c
    add = __ -- implementation doesn't matter

    type One = S Z
    type Two = S One
    type Three = S Two

    zero = __ :: Z
    one = __ :: One
    two = __ :: Two
    three = __ :: Three
    three' = add one two

    add3 = \x -> (add two x  `asTypeOf` three)
    
    --add1 :: (Sum2 One One Two) => a
    --add1 = __


    class Number a where
        numValue :: a -> Int
    
    numPred :: S a -> a
    numPred = const undefined

    instance Number Z where
        numValue = const 0
    instance Number x => Number (S x) where
        numValue x = numValue (numPred x) + 1