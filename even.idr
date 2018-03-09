odd : Nat -> Maybe Nat
even : Nat -> Maybe Nat
even Z = Just 0
even (S n) = map S (odd n)

odd Z = Nothing
odd (S n) = even n

unjust : (Just a = Just b) -> a = b
evenDownOne : (even (S n) = Just (S k)) -> odd n = Just k

evenDownTwo : (even (S $ S n) = Just (S k)) -> even n = Just k
evenDownTwo eut = evenDownOne eut

evenIsDoubleAdd : (even n = Just k) -> (n = k + k)
evenIsDoubleAdd {n=Z} pk = rewrite sym $ unjust pk in Refl
evenIsDoubleAdd {n=S Z} pk = ?impos
evenIsDoubleAdd {n=S $ S n} {k=S k} pk = 
  rewrite sym $ plusSuccRightSucc k k in 
    plusConstantLeft n (plus k k) 2 (evenIsDoubleAdd {n=n} {k=k} (evenDownTwo pk))
