module Bla


type list 'a = 
    | Nil : list 'a
    | Cons : 'a -> list 'a -> list 'a