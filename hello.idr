module Main
import Data.Fin
import Data.Vect

main : IO ()
main = putStrLn ?greeting

test : List Nat
test = [c (S 1), c Z, d (S Z)]
  where c x = 42 + x
        d y = c (y + 1 + z y)
              where z w = y + w

even : Nat -> Bool
even Z = True
even (S k) = ?even_rhs

isSingleton : Bool -> Type
isSingleton True = Nat
isSingleton False = List Nat

mysum : (single : Bool) -> isSingleton single -> Nat
mysum True x = x
mysum False [] = 0
mysum False (x :: xs) = x + mysum False xs

myindex : Fin n -> Vect n a -> a
myindex (FS k) (x :: xs) = myindex k xs
myindex FZ     (x :: xs) = x
