> module Countdown where
> import Control.Monad ((>=>))
> import Data.List
> import Data.Bifunctor


==  The countdown problem

Given a set of numbers `xs` and a target number `n`, find the number of
expressions built using grammar `G` that evaluate to `n`.

Grammar:

\begin{verbatim}
G := int
   | G + G
   | G - G
   | G * G
   | G / G
   | ( G )
\end{verbatim}

Design an *efficient* program to solve countdown:

< solutions :: [Int] -> Int -> Int

You may find it easier to implement this function instead:

< solutions :: [Int] -> Int -> [Expr]

The following solution is transcribed from the paper, but it can also be solved
with dynamic programming.

=== Part 1: Formal specification

- conditions: no duplicates. intermediate results and final result are all nats

Candidate should:
- define an Expr type
- define the 'solution' predicate

We specify the problem with a type of operands and expressions

> data Op = Add | Sub | Mul | Div
> data Expr = Val Int | App Op Expr Expr

A predicate for valid expressions, that is, an expression with two natural
operands that evaluates to a natural.

> valid :: Op -> Int -> Int -> Bool
> valid Add _ _ = True
> valid Sub x y = x > y
> valid Mul _ _ = True
> valid Div x y = x `mod` y == 0

The semantics of expressions, using the list monad to encode failure.

> apply :: Op -> Int -> Int -> Int
> apply Add x y = x + y
> apply Sub x y = x - y
> apply Mul x y = x * y
> apply Div x y = x `div` y

> eval :: Expr -> [Int]
> eval (Val n) = [n]
> eval (App o l r) = [apply o x y | x <- eval l, y <- eval r, valid o x y]

The formal specification of the problem. An expression `e` is a valid solution
for the instance defined by `(n, xs)` if `e` evaluates to `n` and the set of
constants of `e` is a subset of `xs`.

> values :: Expr -> [Int]
> values (Val n) = [n]
> values (App _ l r) = values l ++ values r

> subbags :: [a] -> [[a]]
> subbags = tails >=> permutations

> solution :: Expr -> Int -> [Int] -> Bool
> solution e n xs = eval e == [n] && values e `elem` subbags xs

=== Part 2: Brute force implementation

Candidate should:
- describe the brute force algorithm, in pseudocode or Haskell
- can discuss lazy evaluation, memoization, etc

We will generate all expressions and filter out the solutions by evaluation.

> {-@ splits :: {xs : [a]} -> { [(ys : [a], zs : [a])] | ys ++ zs == xs } @-}
> splits        :: [a] -> [([a], [a])]
> splits []     = [([],[])]
> splits (x:xs) = ([], x:xs) : map (first (x:)) (splits xs)

> nesplits :: [a] -> [([a], [a])]
> nesplits = filter ne . splits
>   where
>     ne (x,y) = not (null x || null y)

> exprs :: [Int] -> [Expr]
> exprs []  = []
> exprs [n] = [Val n]
> exprs ns  = [  e
>             | (ls, rs) <- nesplits ns
>             , l        <- exprs ls
>             , r        <- exprs rs
>             , e        <- combine l r
>             ]

Build all expressions with operands 'l' and 'r'

> combine :: Expr -> Expr -> [Expr]
> combine l r = [App o l r | o <- ops]

> ops :: [Op]
> ops =  [Add, Sub, Mul, Div]

All solutions are found thusly: we take all permutations of all subsequences of 'xs',
generate all expressions for each permutation, then filter.

> solutions :: [Int] -> Int -> [Expr]
> solutions ns n = [e | ns' <- subbags ns, e <- exprs ns', eval e == [n]]

Of course, this is hopelessly inefficient, as there are $\sum^n_i=1 i!$ subbags!

Questions:
1. prove the correctness of this algorithm by calculation


=== Part 3: Fusing Generation and Evaluation

> type Result = (Expr, Int)

We want an optimized function 'results' that is the same as 'resultsSpec'

> resultsSpec :: [Int] -> [Result]
> resultsSpec ns = [(e,n) | e <- exprs ns, n <- eval e]

> combine' :: Result -> Result -> [Result]
> combine' (l,x) (r,y) = [ (App o l r, apply o x y) | o <- ops, valid o x y]

Calculate 'results'.

> results :: [Int] -> [Result]
> results []  = []           -- defn of expr

> results [n] = [(Val n, n)] -- defn of expr and eval

< results ns = resultsSpec
<            -- induction hypothesis
<            = [(e,n) | e <- exprs ns, n <- eval e]
<
<            -- inline exprs
<            = [(App o l r,n)
<              | (ls, rs) <- nesplits ns
<              , l        <- exprs ls
<              , r        <- exprs rs
<              , o        <- ops
<              , n        <- eval (App o l r)
<              ]
<
<            -- inline eval
<            = [(App o l r, apply o x y)
<              | (ls, rs) <- nesplits ns
<              , l        <- exprs ls
<              , r        <- exprs rs
<              , o        <- ops
<              , x        <- eval l
<              , y        <- eval r
<              , valid o x y
<              ]
<
<            -- commutativity of independent subcomputations
<            = [(App o l r, apply o x y)
<              | (ls, rs) <- nesplits ns
<              , l        <- exprs ls
<              , x        <- eval l
<              , r        <- exprs rs
<              , y        <- eval r
<              , o        <- ops
<              , valid o x y
<              ]
<
<            -- induction hypothesis
<            = [(App o l r, apply o x y)
<              | (ls, rs) <- nesplits ns
<              , (l,x)    <- results ls
<              , (r,x)    <- results rs
<              , o        <- ops
<              , valid o x y
<              ]
<
<            -- defn of combine'
> results ns = [ e
>              | (ls, rs) <- nesplits ns
>              , lx       <- results ls
>              , rx       <- results rs
>              , e        <- combine lx rx
>              ]

Now the optimized solution is simply:

> solution' :: [Int] -> Int -> [Expr]
> solution' ns n = [e | ns' <- subbags ns, (e,m) <- results ns', m == n]

This is quite efficient, with a divide-and-conquer flavour.

=== Credit

This problem is transcribed from Graham Hutton's beautiful paper *The Countdown Problem* [1]

[1] http://www.cs.nott.ac.uk/~pszgmh/countdown.pdf
