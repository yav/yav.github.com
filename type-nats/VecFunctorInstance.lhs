The Problem
===========

The problem you are encountering is because in GHC type-families may not
appear in the head of a class instance, and (+) is just a type family.

In general, this make sense because such instances do not always make sense.
Consider, for example, the following code:

    class C a where
      f :: a -> String

    type family F a
    type instance F Int  = Char
    type instance F Bool = Char

    -- bad instance
    instance C (F a)

Now, if GHC encounters a constraint `C Char`, there is no way to know if
`a` should be `Int` or `Bool`.  One could make the case that such instances
should be allowed as long as `F` is injective, but no one has implemented
that yet.

One possible work-around is to change:

    instance C (F a)

into

    instance (F a ~ b) => C b

This is a valid instance, but one has to be careful, as GHC
consults only the instance "head" (i.e., the predicate on the RHS of
the fat arrow) when selecting instances, and the context is ignored.
Since in this case the instance "head" is just a variable,
we have end up with a very general instance.

Extensions an Imports
---------------------

The rest of the file has two solutions.  The first one, which is more natural,
requires the use of a type-checker plugin, which can be enabled with
the following flag (if installed):

    {-# OPTIONS_GHC -fplugin=TypeNatSolver #-} -- use plugin

> {-# LANGUAGE GADTs #-}
> -- To define the type `Vec`

> {-# LANGUAGE DataKinds, KindSignatures, TypeOperators #-}
> -- For working with type level literals

> {-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
> -- For defining "exotic" instances

> module VecFuntorInstance where
>
> import GHC.TypeLits
> import Data.Proxy


The Type of Vectors with a Fixed Length
---------------------------------------

We start by defining the type of vectors of a fixed length.

> data Vec (n::Nat) a where
>   Nil  :: Vec 0 a
>   Cons :: a -> Vec n a -> Vec (n+1) a
>
> -- | Convert a vector to a list; useful for debugging.
> toList :: Vec n a -> [a]
> toList vec =
>   case vec of
>     Nil       -> []
>     Cons x xs -> x : toList xs
>
> instance Show a => Show (Vec n a) where
>   showsPrec p = showsPrec p . toList

The Basic Idea
--------------

We illustrate the basic idea by defining an overloaded function that
generates a constant vector of a given length, by consulting the type
of the vector.

> class ConstVec n where
>   constVec :: a -> Vec n a


The base case instance is nothing special:

> instance ConstVec 0 where
>   constVec _ = Nil

The interesting case arises when we define the inductive step:

> instance {-# OVERLAPS #-}
>   (ConstVec prev, (prev + 1) ~ n) => ConstVec n
>   where
>   constVec a = Cons a (constVec a)

Note that, as discussed before, We moved the type-function to the instance's
context and, also, we added the `OVERLAPS` pragma.
This pragma tells GHC that we are defining an instance that overlaps another
one, and so before committing to the more general one,
it should make sure that the more specific one is guaranteed to not work.

Here is an example of this at work:

> make5 :: Char -> Vec 5 Char
> make5 = constVec

    *Test> make5 'b'
    "bbbbb"


If we look at the generated Core for `make5` after compiling with
optimizations, we see that GHC has fully unrolled all the loops:

    make5
    make5 = ($sconstVec2) `cast` ...

    $sconstVec2
    $sconstVec2 =
      \ @ a_X2et a1_X1Vj ->
        Cons
          @~ <4 + 1>_N
          a1_X1Vj
          ((Cons
              @~ <3 + 1>_N
              a1_X1Vj
              ((Cons
                  @~ <2 + 1>_N
                  a1_X1Vj
                  ((Cons
                      @~ <1 + 1>_N
                      a1_X1Vj
                      ((Cons @~ <0 + 1>_N a1_X1Vj ($WNil)) `cast` ...))
                   `cast` ...))
               `cast` ...))
           `cast` ...)


Defining a Functor instance
---------------------------

To define an instance of the `Functor` class we use the same pattern:

> class MapVec (n :: Nat) where
>   mapVec :: proxy n -> (a -> b) -> Vec n a -> Vec n b
>
> instance MapVec 0 where
>   mapVec _ _ _ = Nil


    -- Only works with plugin
    instance {-# OVERLAPS #-} (MapVec prev, (prev + 1) ~ n) => MapVec n where
      mapVec p f (Cons x xs) = Cons (f x) (mapVec (prev p) f xs)
        where prev :: proxy (a + 1) -> Proxy a
              prev _ = Proxy


> instance MapVec n => Functor (Vec n) where
>   fmap = mapVec Proxy



Unfortunately the inductive instance is rejected by vanilla GHC 7.10
because it has very little knowledge about how numbers work---the only
thing GHC knows is how to evaluate functions on numbers (e.g., it
knows that 7 + 3 is 10).  However, for this instance to be accepted
we need to know about cancellation, in particular that
if `(x + 1) ~ (y + 1)`, then it must be the case that `x ~ y`.

This, and other facts about numbers, are implemented as a separate
GHC plug-in, available from:

    https://github.com/yav/type-nat-solver

To use the plugin one needs to invoke GHC with the `-fplugin=TypeNatSolver`
(or add it as an `OPTION` pragma at the top of the file).  The plug-in
uses the `z3` (or another) SMT-solver to solve many of the linear
numeric constraints arising from type-checking numbers.


A Version Without Using a Plugin
--------------------------------

The simple solver built into GHC works only in simple cases
(generally, if one uses GADTs, it is very likely that the advanced
solver would be needed).   However, in this case we can get a working
implementation by reformulating the definition of the GADT as follows:

> data Vec' (n::Nat) a where
>   Nil'  :: Vec' 0 a
>   Cons' :: a -> Vec' (n - 1) a -> Vec' n a
>
> -- | Convert a vector to a list; useful for debugging.
> toList' :: Vec' n a -> [a]
> toList' vec =
>   case vec of
>     Nil'       -> []
>     Cons' x xs -> x : toList' xs
>
> instance Show a => Show (Vec' n a) where
>   showsPrec p = showsPrec p . toList'


> class ConstVec' n where
>   constVec' :: a -> Vec' n a
>
> instance ConstVec' 0 where
>   constVec' _ = Nil'
>
> instance {-# OVERLAPS #-} (ConstVec' (n-1)) => ConstVec' n where
>   constVec' a = Cons' a (constVec' a)

> make5' :: a -> Vec' 5 a
> make5' = constVec'



> class MapVec' (n :: Nat) where
>   mapVec' :: proxy n -> (a -> b) -> Vec' n a -> Vec' n b
>
> instance MapVec' 0 where
>   mapVec' _ _ _ = Nil'

> instance {-# OVERLAPS #-} (MapVec' (n-1)) => MapVec' n where
>   mapVec' p f (Cons' x xs) = Cons' (f x) (mapVec' (prev p) f xs)
>     where prev :: proxy a -> Proxy (a - 1)
>           prev _ = Proxy


> instance MapVec' n => Functor (Vec' n) where
>   fmap = mapVec' Proxy









