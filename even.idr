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

evenPlusSelf : (n:Nat) -> (even (n + n) = Just n)
evenPlusSelf Z = Refl
evenPlusSelf (S n) = 
  rewrite plusCommutative n (1 + n) in
  rewrite evenPlusSelf n in Refl

evenPlusEven : (even n = Just k) -> (even m = Just j) -> (even (m + n) = Just (j + k))
evenPlusEven {n=n} {k=k} {m=m} {j=j} pk pj =
  rewrite evenIsDoubleAdd {n=n} {k=k} pk in
  rewrite evenIsDoubleAdd {n=m} {k=j} pj in
  rewrite sym $ plusAssociative j j (k+k) in
  rewrite plusAssociative j k k in
  rewrite plusCommutative (plus j k) k in
  rewrite plusAssociative j k (j+k) in
    evenPlusSelf (plus j k)
