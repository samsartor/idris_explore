import Data.Vect

ZeroEquals : a -> Type
ZeroEquals = (=) 0

TwoOf : Type -> Type
TwoOf = Vect 2

bar : case False of
    True => List Char
    False => String
bar = "Hello, World!"
