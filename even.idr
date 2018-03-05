-- Returns whether or not the number is even.
--    Note that natural numbers are defined recursively, much like in Lambda
--      Calculus.
--      (See http://docs.idris-lang.org/en/latest/tutorial/typesfuns.html#data-types)
--    Z is the zero type for natural numbers
--    S is a function which returns the successor to a natural number
even : Nat -> Bool
even Z = True
even (S k) = odd k where
  odd Z = False
  odd (S k) = even k

-- Proves that k + k is even where k is a natural number.
--    Refl is the reflexive identity: x = x
--    "rewrite" takes a proof that x = y and substitutes that into the
--      expression on the other side of the "in".
evenAddSelf : (k:Nat) -> even (k + k) = True
evenAddSelf Z = Refl
evenAddSelf (S Z) = Refl
evenAddSelf (S (S k)) = rewrite (plusCommutative k (2 + k)) in evenAddSelf k

-- Proves that 2 * k is even where k is a natural number.
evenMulTwo : (k:Nat) -> even (2 * k) = True
evenMulTwo k = rewrite (plusCommutative k 0) in evenAddSelf k