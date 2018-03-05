-- Theorem: Let a_0 = 5, a_1 = 13. For each natural number n, with
--          a_{n+2} = 5a_{n+1} - 6a_n, a_n = 2^{n+1} + 3^{n+1}.

-- Define the sequence
seq : (n:Nat) -> Int
seq Z = 5
seq (S Z) = 13
seq (S (S n)) = (5 * (seq (S n))) - (6 * (seq n))

thmProof : (n:Nat) -> seq n = (pow 2 (S (S n))) + (pow 3 (S (S n)))
thmProof n = rewrite (multAssociative 2 2 (pow 2 n)) in ?ohea
