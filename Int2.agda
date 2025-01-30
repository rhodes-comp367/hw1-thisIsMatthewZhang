module Int2 where

-- import `plus` & `times` on Nats;
-- use these functions where appropriate below.
open import Nat

data Int : Set where
  -- (+ n) represents positive n.
  + : Nat → Int
  -- (- n) represents negative n.
  - : Nat → Int
  -- 0 can be represented as (+ zero) or (- zero).

-- given i, return i + 1.
isuc : Int → Int
isuc (+ n) = + (suc n)
isuc (- zero) = + (suc zero)
isuc (- (suc n)) = - n

-- given i, return i - 1.
ipred : Int → Int
ipred (+ zero) = - (suc zero) -- pred of zero is -1 regardless if it's + zero or - zero
ipred (- zero) = - (suc zero)
ipred (+ (suc n)) = + n -- pred of + (n + 1) is simply just + n
ipred (- (suc n)) = - (suc (suc n)) -- pred of - (n + 1) is - (n + 2)

-- given i, return -i.
ineg : Int → Int
ineg (+ n) = - n -- negative form is just the opposite sign
ineg (- n) = + n

-- given i & j, return i + j.
iplus : Int → Int → Int 
iplus (- zero) n = n -- had to define base cases with both - zero and + zero
iplus (+ zero) n = n
iplus (+ (suc n)) (- zero) = + (suc n) 
iplus (+ m) (+ n) = + (plus m n)
iplus (+ (suc m)) (- (suc n)) = iplus (+ m) (- n)
iplus (- (suc m)) (+ n) = ipred (iplus (- m) (+ n))
iplus (- (suc m)) (- n) = - (plus m (suc n))


-- given i & j, return i - j.
iminus : Int → Int → Int
iminus (- zero) (+ n) = - n -- I'm not sure why Agda didn't make me explicitly define 'iminus (- zero) (- n)' or the lines with '(+ zero)' like in iplus
iminus (+ m) (+ n) = iplus (- n) (+ m)
iminus (- (suc m)) (+ n) = iplus (- n) (- (suc m))
iminus m (- n) = iplus m (+ n)

-- given i & j, return i * j.
itimes : Int → Int → Int
itimes (- zero) n = (- zero) -- same thing here
itimes (+ m) (- n) = - (times m n)
itimes (+ m) (+ n) = + (times m n)
itimes (- (suc m)) (+ n) = - (times (suc m) n)
itimes (- (suc m)) (- n) = + (times (suc m) n)

