> {-# LANGUAGE GADTs, DeriveFunctor, RankNTypes #-}
> module Algebraic where
> import Data.Functor.Foldable


=== Solution with recursion schemes

First, the types. We define a base expression functor and its corresponding catamorphism

> data ExprF a
>   = Const a
>   | Add   a a
>   | Sub   a a
>   | Mul   a a
>   | Div   a a
>   deriving (Functor)

An expresison tree is the fixpoint of the functor

> type Expr = Fix ExprF

-- Lift a catamorphism of a functor to a catamorphism of its fixpoint

-- > cata :: Functor f => (f a -> a) -> (Fix f a -> a)
-- > cata f = f . fmap (cata f) . out

The evaluator simply takes the deep embedding to the shallow embedding

> eval :: Expr -> Int
> eval = cata evalF
>   where
>     evalF :: ExprF Int -> Int
>     evalF (Const i) = i
>     evalF (Add x y) = x + y
>     evalF (Sub x y) = x - y
>     evalF (Mul x y) = x * y
>     evalF (Div x y) = x `div` y

'values' extracts all the constants of an expression

> values :: Expr -> [Int]
> values = cata valuesF
>   where
>     valuesF :: ExprF [Int] -> [Int]
>     valuesF (Const i) = i
>     valuesF (Add x y) = x ++ y
>     valuesF (Sub x y) = x ++ y
>     valuesF (Mul x y) = x ++ y
>     valuesF (Div x y) = x ++ y

The predicate 'valid' takes an expression (of type `Expr Int`) and checks
whether it evaluates to an integer greater than zero.

> valid :: Expr -> Bool
> valid = cata validF

> validF :: ExprF Int -> Bool
> validF (Add _ _) = True
> validF (Sub x y) = x > y
> validF (Mul _ _) = True
> validF (Div x y) = x `mod` y == 0

Finally we fuse the validity check and the evaluation step, such that only valid
expressions are evaluated:
