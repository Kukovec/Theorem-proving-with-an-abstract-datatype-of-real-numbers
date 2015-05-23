
module Evaluation where

type I = [Int]
minusOne, one :: I
minusOne = repeat (-1)
one = repeat 1
type J = [Int]
divideBy :: Int -> J -> I
divideBy n (a : b : x) = let d = 2*a +b in
						 if d < -n then -1 : divideBy n (d+2*n : x)
						 else if d > n then 1 : divideBy n (d - 2*n : x)
						 else 0 : divideBy n (d:x)
mid :: I -> I -> I
mid x y = divideBy 2 $ zipWith (+) x y

zero :: I
zero = repeat 0

bigMid :: [ I ] -> I
bigMid = (divideBy 4) . bigMid' where
		bigMid' ((a : b : x) : (c : y) : zs) = 2*a+b+c : bigMid' (mid x y : zs)
		
h :: I -> I -> Int -> I
h a b 0 = mid a b
h a b 1 = b
h a b (-1) = a

affine :: I -> I -> I -> I
affine a b x = bigMid [h a b d | d <- x]

partialSum :: I -> Int -> Double
partialSum x n = ps 0 $ take n x where
		ps m (y : ys) = fromIntegral y /(2^(m+1)) + if m<n then ps ( m + 1 ) ys else (fromIntegral 0)
		ps m [] = 0

neg = affine one minusOne

times :: I -> I -> I
times x y = affine (neg x) x y

pow :: I -> Int -> I
pow x 0 = one
pow x n = times x $ pow x $ n-1

divide :: Int -> Int -> (I,Int)
divide m n = if (2 * m >= n) then (one, 2*m - n) else (zero, 2*m)

offset = 3

fullDivision :: Int -> Int -> (Int -> (I, Int))
fullDivision k r 0 = divide k r
fullDivision k r n = divide (snd $ fullDivision k r (n-1)) r

divList :: Int -> Int -> [ I ]
divList k r = divAux 0 where 
			divAux n = fst (fullDivision k r n) : divAux (n+1)

fractionI :: Int -> Int -> I
fractionI k r = bigMid $ divList k r

factorial :: Int -> Int
factorial 0 = 1
factorial n = n * (factorial $ n-1)

divByPow :: I -> Int -> I
divByPow x 0 = x
divByPow x n = mid (divByPow x (n-1)) zero


series :: I -> (Int -> I)
series x i = times (pow x i) z where
			z = if (i+1 <= offset) 
			then divByPow (fractionI 1 (factorial i)) (offset - i -1)
			else bigMid $ divList (2^(i + 1 -offset)) (factorial i)
			
seriesList :: (Int -> I) -> [I]
seriesList f = auxSL 0 where auxSL m = f m : auxSL (m+1)

expI :: I -> I
expI x = bigMid $ seriesList $ series x

expNum :: I -> Double
expNum x = 2^offset * partialSum (expI x) 15

half = 1 : zero

e = expNum one