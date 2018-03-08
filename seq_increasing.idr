-- Theorem: Let n be a natural number. Let S be the sequence {a_0, a_1, ...}.
--          Where a_0 = 5, a_1 = 13, and a_{n+2} = 5a_{n+1} - 6a_n.
--          Prove that the sequence is increasing.

-- Define the sequence
-- seq : Nat -> Nat
-- seq Z = 5
-- seq (S Z) = 13
-- seq (S (S n)) = (+) (5 * (seq (S n))) (6 * (seq n))

seq : Nat -> Nat
seq n = plus (pow 2 n) (pow 3 n)

seqInc : (n:Nat) -> LTE (seq n) (seq (S n))
seqInc Z = lteAddRight 2
seqInc n = rewrite (plusCommutative (pow 3 n) 0) in
           rewrite (plusCommutative (pow 2 n) 0) in
           rewrite (plusAssociative (plus (pow 2 n) (pow 2 n)) (pow 3 n) (plus (pow 3 n) (pow 3 n))) in
           rewrite (plusCommutative (plus (pow 2 n) (pow 2 n)) (pow 3 n)) in
           rewrite (plusAssociative (pow 3 n) (pow 2 n) (pow 2 n)) in
           rewrite (plusCommutative (pow 3 n) (pow 2 n)) in
           -- rewrite (plusAssociative (plus (plus (pow 2 n) (pow 3 n)) (pow 2 n)) (pow 3 n) (pow 3 n)) in
                   -- lteAddRight (plus (pow 3 n) (pow 2 n))
                   ?a

-- seq (S (S n)) = (-) (5 * (seq (S n))) (6 * (seq n)) {smaller=monotonic n} where
--   l : (n:Nat) -> (m:Nat) -> LTE (6 * n) (5 * m)
--   l Z _ = LTEZero
--   l (S n) (S m) = l n m

--   monotonic : (n:Nat) -> LTE (6 * (seq n)) (5 * (seq (S n)))
--   monotonic Z = ?b
--   monotonic n = ?c


--          For each natural number n, with
--          a_{n+2} = 5a_{n+1} - 6a_n, a_n = 2^{n+1} + 3^{n+1}.

-- thmProof : (n:Nat) -> seq n = (pow 2 (S (S n))) + (pow 3 (S (S n)))
-- thmProof n = ?ohea
