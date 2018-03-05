-- A function that returns whether or not something is even.
even : Nat -> Bool
even Z = True
even (S k) = odd k where
  odd Z = False
  odd (S k) = even k

-- Proves that k + k is even where k is a natural number.
evenAddSelf : (k:Nat) -> even (k + k) = True
evenAddSelf Z = Refl
evenAddSelf (S Z) = Refl
evenAddSelf (S (S k)) = rewrite (plusCommutative k (2 + k)) in evenAddSelf k

-- Proves that 2 * k is even where k is a natural number.
evenMulTwo : (k:Nat) -> even (2 * k) = True
evenMulTwo k = rewrite (plusCommutative k 0) in evenAddSelf k
