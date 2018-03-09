odd : Nat -> Maybe Nat
even : Nat -> Maybe Nat
even Z = Just 0
even (S n) = map S $ odd n

odd Z = Nothing
odd (S n) = even n

mapSuccSym : (a:Maybe Nat) -> (b:Maybe Nat) -> (map S a = map S b) -> a = b
mapSuccSym (Just a) (Just b) = cong {f=Just} . plusLeftCancel 1 a b . justInjective {x=S a} {y=S b}

evenLessOneOdd : (even $ S n = Just $ S k) -> odd n = Just k
evenLessOneOdd {n=n} {k=k} = mapSuccSym (odd n) (Just $ k)

evenLessTwoEven : (even $ S $ S n = Just $ S k) -> even n = Just k
evenLessTwoEven eut = evenLessOneOdd eut

evenIsPlusSelf : (even n = Just k) -> (n = k + k)
evenIsPlusSelf {n=Z} pk = rewrite sym $ justInjective pk in Refl
evenIsPlusSelf {n=S Z} pk = absurd $ nothingNotJust pk
evenIsPlusSelf {n=S $ S n} {k=S k} pk = 
  rewrite sym $ plusSuccRightSucc k k in 
    plusConstantLeft n (plus k k) 2 (evenIsPlusSelf {n=n} {k=k} (evenLessTwoEven pk))

evenIsTimesTwo : (even n = Just k) -> (n = 2 * k)
evenIsTimesTwo {k=k} pk =
  rewrite plusZeroRightNeutral k in
    evenIsPlusSelf pk

plusSelfEven : (n:Nat) -> (even (n + n) = Just n)
plusSelfEven Z = Refl
plusSelfEven (S n) = 
  rewrite plusCommutative n (1 + n) in
  rewrite plusSelfEven n in Refl

timesTwoEven : (n:Nat) -> (even (2 * n) = Just n)
timesTwoEven n =
  rewrite plusZeroRightNeutral n in
    plusSelfEven n

plusEvenEven : (even n = Just k) -> (even m = Just j) -> even (m + n) = Just (j + k)
plusEvenEven {n=n} {k=k} {m=m} {j=j} pk pj =
  rewrite evenIsPlusSelf {n=n} {k=k} pk in
  rewrite evenIsPlusSelf {n=m} {k=j} pj in
  rewrite sym $ plusAssociative j j (k+k) in
  rewrite plusAssociative j k k in
  rewrite plusCommutative (plus j k) k in
  rewrite plusAssociative j k (j+k) in
    plusSelfEven (plus j k)
