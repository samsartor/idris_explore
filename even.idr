odd : Nat -> Maybe Nat
even : Nat -> Maybe Nat
even Z = Just 0
even (S n) = map S $ odd n

odd Z = Nothing
odd (S n) = even n


evenLessOneOdd : (even (S n) = Just (S k)) -> odd n = Just k

evenlessTwoEven : (even (S $ S n) = Just (S k)) -> even n = Just k
evenlessTwoEven eut = evenLessOneOdd eut

evenIsPlusSelf : (even n = Just k) -> (n = k + k)
evenIsPlusSelf {n=Z} pk = rewrite sym $ justInjective pk in Refl
evenIsPlusSelf {n=S Z} pk = absurd $ trueNotFalse $ sym $ cong {f=isJust} pk
evenIsPlusSelf {n=S $ S n} {k=S k} pk = 
  rewrite sym $ plusSuccRightSucc k k in 
    plusConstantLeft n (plus k k) 2 (evenIsPlusSelf {n=n} {k=k} (evenlessTwoEven pk))

evenIsTimesTwo : (even n = Just k) -> (n = 2 * k)
evenIsTimesTwo {k=k} pk =
  rewrite plusCommutative k 0 in
    evenIsPlusSelf pk

plusSelfEven : (n:Nat) -> (even (n + n) = Just n)
plusSelfEven Z = Refl
plusSelfEven (S n) = 
  rewrite plusCommutative n (1 + n) in
  rewrite plusSelfEven n in Refl

timesTwoEven : (n:Nat) -> (even (2 * n) = Just n)
timesTwoEven n =
  rewrite plusCommutative n 0 in
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
