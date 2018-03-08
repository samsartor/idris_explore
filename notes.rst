Idris Notes
###########

- Idris is a "general purpose programming language with dependent types".

- Idris can be compiled or interpreted.
- Idris is modelled after Haskell and its syntax is highly Haskellian
- The name Idris goes back to the character of the singing dragon in the 1970s
  UK children's television program *Ivor the Engine*.

Dependent Types
===============

Type can be dependent on the value. For example natural numbers are defined as
follows::

    data Nat = Z | S Nat

If you were at the Lambda Calculus talk, this may look familiar to you. The
``S`` function returns the *successor* to a natural number.

::

    isSingleton : Bool -> Type
    isSingleton True = Nat
    isSingleton False = List Nat

    mysum : (single : Bool) -> isSingleton single -> Nat
    mysum True x = x
    mysum False [] = 0
    mysum False (x :: xs) = x + mysum False xs

Then use like this::

    > mysum False [0..10]
    55 : Nat

Type errors are great::

    (++) : Vect n a -> Vect m a -> Vect (n + m) a
    (++) Nil       ys = ys
    (++) (x :: xs) ys = x :: xs ++ xs -- BROKEN

Which gives the error::

    When checking right hand side of Vect.++ with expected type
            Vect (S k + m) a

    When checking an application of constructor Vect.:::
            Type mismatch between
                    Vect (k + k) a (Type of xs ++ xs)
            and
                    Vect (plus k m) a (Expected type)

            Specifically:
                    Type mismatch between
                            plus k k
                    and
                            plus k m

Encoding Out of Bounds Exception in the Type System
---------------------------------------------------

The fin data type is defined as follows::

    data Fin : Nat -> Type where
       FZ : Fin (S k)
       FS : Fin k -> Fin (S k)

The following function looks up an element in an ``n`` sized vector::

    index : Fin n -> Vect n a -> a
    index FZ     (x :: xs) = x
    index (FS k) (x :: xs) = index k xs

Functions in Idris
==================

- Idris requires type declarations for all functions (this is unlike Haskell
  where this is optional)
- Like Haskell, functions are implemented by pattern matching
- If you know Haskell, you will note that the syntax is very similar, but note
  the single colon rather than Haskell's double colon.

Example of an addition function in Idris::

    plus : Nat -> Nat -> Nat
    plus Z     y = y
    plus (S k) y = S (plus k y)

Where Clauses
-------------

::

    even : Nat -> Bool
    even Z = True
    even (S k) = odd k where
      odd Z = False
      odd (S k) = even k

Holes
=====

::

    even : Nat -> Bool
    even Z = True
    even (S k) = ?even_rhs
