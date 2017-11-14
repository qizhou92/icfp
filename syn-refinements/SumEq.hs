{-@ LIQUID "--higherorder"                         @-}
{-@ LIQUID "--automatic-instances=liquidinstances" @-}

module SumEq where

-- | Recursive implementation -----------------------------------------

{-@ reflect sumTo @-}
{-@ sumTo :: Nat -> Nat @-}
sumTo :: Int -> Int
sumTo n
  | n == 0    = 0
  | otherwise = n + sumTo (n - 1)

-- | Tail-Recursive implementation ------------------------------------

{-@ reflect loop              @-}
{-@ loop :: Nat -> Nat -> Nat @-}
loop :: Int -> Int -> Int
loop n acc
  | n == 0    = acc
  | otherwise = loop (n - 1) (acc + n)

{-@ reflect sumToTR       @-}
{-@ sumToTR :: Nat -> Nat @-}
sumToTR n = loop n 0

-- | Invariant relating the two implementations --------------------

{-@ inv :: n:Nat -> acc:Nat -> { loop n acc == acc + sumTo n } @-}
inv :: Int -> Int -> ()
inv n acc
  | n == 0    = ()
  | otherwise = inv (n - 1) (acc + n)

-- | Equivalence of two implementations ----------------------------

{-@ equiv :: n:Nat -> {sumTo n = sumToTR n} @-}
equiv :: Int -> ()
equiv n = inv n 0
