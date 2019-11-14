%default total

||| The ordinary list data type, carrying around an extra PHOAS parameter
public export
data PHOASList : (v : Type -> Type) -> (a : Type) -> Type where
  Nil  : PHOASList v a 
  (::) : a -> PHOASList v a -> PHOASList v a 

||| Append on PHOASLists
public export
(++) : PHOASList v a -> PHOASList v a -> PHOASList v a 
(++) Nil xs = xs
(++) (x :: xs) ys = x :: xs ++ ys

||| A proof that a given index is a valid index into a PHOASList
public export
data InPList : (k : Nat) -> (xs : PHOASList v a) -> Type where
  InNow : InPList Z (x :: xs)
  InAfter : InPList k xs -> InPList (S k) (x :: xs)

||| An index function into a PHOASList
public export
index : (n : Nat) -> (xs : PHOASList v a) -> {auto prf: InPList n xs} -> a
index Z (x :: xs) = x
index (S k) (x :: xs) {prf = InAfter p} = index k xs

||| Length defined for PHOASList
public export
length : PHOASList v a -> Nat
length [] = Z
length (x :: xs) = S (length xs)

||| A non-empty proof for PHOASLists
public export
data NonEmptyPL : (xs : PHOASList v a) -> Type where
  IsNonEmptyPL : NonEmptyPL (x :: xs)

||| A proof that an empty non-empty proof is uninhabited for PHOASLists
public export
implementation Uninhabited (NonEmptyPL []) where
  uninhabited IsNonEmptyPL impossible

||| A Show implementation for PHOASLists
public export
implementation Show a => Show (PHOASList v a) where
  show Nil = "[]"
  show (x :: xs) = "[" ++ show x ++ showl xs
    where
    showl : Show a => PHOASList v a -> String
    showl Nil = "]"
    showl (y :: ys) = "," ++ show y ++ showl ys

||| Semigroup implementation for PHOASLists
public export 
implementation Semigroup (PHOASList v a) where
  (<+>) = (++)

||| Monoid implementation for PHOASLists
public export
implementation Monoid (PHOASList v a) where
  neutral = []

||| Foldable implementation for PHOASLists
public export
implementation Foldable (PHOASList v) where
  foldr f acc [] = acc
  foldr f acc (x :: xs) = f x (foldr f acc xs)

  foldl f acc [] = acc
  foldl f acc (x :: xs) = f (foldl f acc xs) x

||| Functor implementation for PHOASLists
public export
implementation Functor (PHOASList v) where
  map f [] = []
  map f (x :: xs) = f x :: map f xs

||| Applicative implementation for PHOASLists
public export
implementation Applicative (PHOASList v) where
 pure x = [x]
 fs <*> xs = concatMap (\f => map f xs) fs

||| Monad implementation for PHOASLists
public export
implementation Monad (PHOASList v) where
  xs >>= f = concatMap f xs


