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
    RankNTypes
#-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module PropTypes where

    -- Representation of the false proposition. 
    -- Since this type has no constructor, no data inhabits this type (=there is no way to prove it)
    data Void -- = forall a . a, which is isomorphic to the data type with no constructor
    
    data Equal a b where
        Refl :: Equal a a

    -- requires RankNTypes
    -- takes two values and cast their type to the second, or something...
    -- "casts" between two equal types because (a ~ b) is assumed for r
    gcastWith :: Equal a b -> ((a ~ b) => r) -> r
    gcastWith Refl x = x

    -- Logical connectives --

    type Not a = a -> Void 

    type And a b = (a,b) 

    type Iff a b = And (a -> b) (b -> a)

    data Or a b = OrL a | OrR b

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
     

    -- Various (fairly trivial) theorems/tautologies of propositional logic.
    -- Inspired by the theorems from https://www.cs.princeton.edu/courses/archive/fall07/cos595/stdlib/html/Coq.Init.Logic.html

    -- ex falso quodlibet
    absurd :: Void -> a
    absurd contra = case contra of {}

    not_False :: Not Void
    not_False = \contra -> case contra of {}

    double_neg :: a -> Not (Not a) -- same as a -> (a -> Void) -> Void 
    double_neg x contra = contra x -- same as \x -> \contra -> contra x

    contrapositive :: (a -> b) -> (Not b -> Not a)
    contrapositive ab = \notb -> notb . ab -- pretty neat

    not_both_true_false :: Not (And a (Not a))
    not_both_true_false (a, not_a) = not_a a

    contra_implies_anything :: And a (Not a) -> b
    contra_implies_anything (a, not_a) = absurd (not_a a)

    impliesTrans :: (a -> b) -> (b -> c) -> a -> c
    impliesTrans f g = g . f -- equivalent to impliesTrans f g x = g (f x)

    iff_refl :: Iff a a
    iff_refl = andI (\x -> x) (\x -> x)

    iff_trans :: (Iff a b) -> (Iff b c) -> (Iff a c)
    iff_trans (ab, ba) (bc, cb) = andI (bc . ab) (ba . cb) -- equivalent to andI (\x -> bc (ab x)) (\x -> ba (cb x))

    iff_sym :: (Iff a b) -> (Iff b a)
    iff_sym (ab, ba) = andI ba ab

    and_comm :: (And a b) -> (And b a)
    and_comm (a, b) = andI b a

    and_assoc :: (And a (And b c)) -> (And (And a b) c)
    and_assoc (a, (b, c)) = andI (andI a b) c 

    and_symm :: Iff (And a b) (And b a) 
    and_symm = andI and_comm and_comm -- pretty neat and concise, right?

    or_comm :: (Or a b) -> (Or b a)
    or_comm or_ab = case or_ab of
        OrL a -> orIR a
        OrR b -> orIL b
    
    or_assoc :: Iff (Or a (Or b c)) (Or (Or a b) c)
    or_assoc = andI -- maybe this can be made shorter?
        (\or_a_bc -> case or_a_bc of
            OrL a -> orIL (orIL a)
            OrR or_bc -> case or_bc of
                OrL b -> orIL (orIR b)
                OrR c -> orIR c    
        )
        (\or_ab_c -> case or_ab_c of
            OrL or_ab -> case or_ab of 
                OrL a -> orIL a
                OrR b -> orIR (orIL b)
            OrR c -> orIR (orIR c)
        )

    eq_sym :: Equal a b -> Equal b a
    eq_sym Refl = Refl

    eq_trans :: Equal a b -> Equal b c -> Equal a c
    eq_trans Refl Refl = Refl
