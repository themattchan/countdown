> {-# LANGUAGE GADTs, DeriveFunctor #-}
> module Countdown where

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

< solve :: [Int] -> Int -> Int

First, the types. We define a base expression functor and its corresponding catamorphism

> data ExprF a
>   = Const a
>   | Add   a a
>   | Sub   a a
>   | Mul   a a
>   | Div   a a
>   deriving (Functor)

> data Fix f a = In { out :: f (Fix f a) }
> type Expr = Fix ExprF

> cata :: Functor f => (f a -> a) -> (Fix f a -> a)
> cata f = f . fmap (cata f) . out

> evalF :: ExprF Int -> Int
> evalF (Const i) = i
> evalF (Add x y) = x + y
> evalF (Sub x y) = x - y
> evalF (Mul x y) = x * y
> evalF (Div x y) = x `div` y

> eval :: Expr Int -> Int
> eval = cata evalF



Credit: this is adapted from Graham Hutton's beautiful paper *The Countdown
Problem* [1]

[1] http://www.cs.nott.ac.uk/~pszgmh/countdown.pdf
