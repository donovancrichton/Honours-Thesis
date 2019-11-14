import PHOASList.PHOASList
import Mod.Mod
import Typeable.Typeable
import Expr.Expr
import Zipper.Zipper
import Proofs.Proofs

%default total
-- A list to sample from to get basic keyboard characters.
charStr : String
charStr = "abcdefghijklmnopqrstuvwxyz1234567890!@#$%^&*()`~-=_+,.<>/?;':\"" ++
          "[]{}"
          
-- A proof that the length of the list of characters is 66.
charStrLen66 : Strings.length Main.charStr = 66
charStrLen66 = Refl

public export
FetchTy : (k : Nat) -> (xs : List Nat) -> Type
FetchTy Z xs = Bool
FetchTy (S Z) xs = Nat
FetchTy (S (S Z)) xs = Integer
FetchTy (S (S (S Z))) xs = String
FetchTy (S (S (S (S Z)))) [] = Bool
FetchTy (S (S (S (S Z)))) (x :: []) = 
  assert_total (FetchTy (modfin x 4) [])
FetchTy (S (S (S (S Z)))) (x :: (y :: xs)) = 
  assert_total ((FetchTy x xs) -> (FetchTy y (reverse xs)))
FetchTy (S (S (S (S (S Z))))) [] = Nat
FetchTy (S (S (S (S (S Z))))) (x :: []) =
  assert_total (FetchTy (modfin x 4) [])
FetchTy (S (S (S (S (S Z))))) (x :: (y :: xs)) = 
  assert_total (FetchTy x xs,FetchTy y (reverse xs))
FetchTy (S (S (S (S (S (S Z)))))) [] = Integer
FetchTy (S (S (S (S (S (S Z)))))) (x :: []) = 
  assert_total (FetchTy (modfin x 4) [])
FetchTy (S (S (S (S (S (S Z)))))) (x :: (y :: xs)) = 
  assert_total (Either (FetchTy x xs) (FetchTy y (reverse xs)))
FetchTy k@(S (S (S (S (S (S (S k))))))) xs = 
  assert_total (FetchTy (modfin k 7) xs)

public export
fetchTy : (k : Nat) -> (xs : List Nat) -> TypeRep (FetchTy k xs)
fetchTy Z xs = TBool
fetchTy (S Z) xs = TNat
fetchTy (S (S Z)) xs = TInteger
fetchTy (S (S (S Z))) xs = TString
fetchTy (S (S (S (S Z)))) [] = TBool
fetchTy (S (S (S (S Z)))) (x :: []) = 
  let p1 = modfNlteN x (S (S (S (S Z))))
      p2 = assert_smaller (S (S (S (S Z)))) (fetchTy (modfin x 4) [])
  in p2
fetchTy (S (S (S (S Z)))) (x :: (y :: xs)) = 
  assert_total $ TFunc (fetchTy x xs) (fetchTy y (reverse xs))
fetchTy (S (S (S (S (S Z))))) [] = TNat
fetchTy (S (S (S (S (S Z))))) (x :: []) =
  let p1 = modfNlteN x (S (S (S (S (S Z)))))
      p2 = assert_smaller (S (S (S (S (S Z))))) (fetchTy (modfin x 4) [])
  in p2
fetchTy (S (S (S (S (S Z))))) (x :: (y :: xs)) = 
  assert_total $ TPair (fetchTy x xs) (fetchTy y (reverse xs))
fetchTy (S (S (S (S (S (S Z)))))) [] = TInteger
fetchTy (S (S (S (S (S (S Z)))))) (x :: []) = 
  let p1 = modfNlteN x (S (S (S (S (S (S Z))))))
      p2 = assert_smaller (S (S (S (S (S (S Z)))))) (fetchTy (modfin x 4) [])
  in p2
fetchTy (S (S (S (S (S (S Z)))))) (x :: (y :: xs)) = 
  assert_total $ TSum (fetchTy x xs) (fetchTy y (reverse xs))
fetchTy k@(S (S (S (S (S (S (S j))))))) xs = 
  assert_total $ fetchTy (modfin k 7) xs

public export
genBoolLit : Nat -> Expr v Bool
genBoolLit n =
  case (modfin n 2) of
    Z => Lit {t1=TBool} True
    (S k) => Lit {t1=TBool} False

public export
genExp : Nat -> List Nat -> TypeRep a -> Expr v a
genExp n [] TBool = genBoolLit n
genExp n (x :: xs) TBool = 
  case (modfin n 3) of
    Z => genBoolLit n
    (S Z) =>
      let ty = fetchTy n (x :: xs)
          e1 = assert_total (genExp x xs TBool)
          e2 = assert_total (genExp n (reverse xs) ty)
      in Cnst {t1=TBool} e1 {t2=ty} e2
    (S (S k)) => 
      let ty = fetchTy n (x :: xs)
          e1 = assert_total (genExp x xs (TFunc ty TBool))
          e2 = assert_total (genExp x (reverse xs) ty)
      in App {t1=ty} e1 {t2=TBool} e2
genExp n [] TNat = Lit {t1=TNat} n
genExp n (x :: xs) TNat = 
  case (modfin n 4) of
    Z => 
      let p1 = modfNlteN n (length (x :: xs))
          p2 = lenXsAlwaysBounded (modfin n (length (x :: xs))) (x :: xs) p1
          m = modfin n (length (x :: xs))
      in Lit {t1=TNat} $ index m (x :: xs)
    (S Z) => 
      let ty = fetchTy n (x :: xs)
          e1 = assert_total (genExp x xs TNat)
          e2 = assert_total (genExp x (reverse xs) ty)
      in Cnst {t1=TNat} e1 {t2=ty} e2
    (S (S Z)) => 
      let e1 = assert_total (genExp x xs TNat)
          e2 = assert_total (genExp x (reverse xs) TNat)
      in Add {t1=TNat} e1 e2
    (S (S (S k))) =>
      let ty = fetchTy n (x :: xs)
          e1 = assert_total (genExp x xs (TFunc ty TNat))
          e2 = assert_total (genExp x (reverse xs) ty)
      in App {t1=ty} e1 {t2=TNat} e2
genExp n [] TInteger = Lit {t1=TInteger} (cast n {to=Integer})
genExp n (x :: xs) TInteger =
  case (modfin n 4) of
    Z => 
      let p1 = modfNlteN n (length (x :: xs))
          p2 = lenXsAlwaysBounded (modfin n (length (x :: xs))) (x :: xs) p1
          m = modfin n (length (x :: xs))
      in Lit {t1=TInteger} $ cast (index m (x :: xs)) {to=Integer}
    (S Z) => 
      let ty = fetchTy n (x :: xs)
          e1 = assert_total (genExp x xs TInteger)
          e2 = assert_total (genExp x (reverse xs) ty)
      in Cnst {t1=TInteger} e1 {t2=ty} e2
    (S (S Z)) => 
      let e1 = assert_total (genExp x xs TInteger)
          e2 = assert_total (genExp x (reverse xs) TInteger)
      in Add {t1=TInteger} e1 e2
    (S (S (S k))) =>
      let ty = fetchTy n (x :: xs)
          e1 = assert_total (genExp x xs (TFunc ty TInteger))
          e2 = assert_total (genExp x (reverse xs) ty)
      in App {t1=ty} e1 {t2=TInteger} e2
genExp n [] TString = Lit {t1=TString} (show n)
genExp n (x :: xs) TString =
  case (modfin n 3) of
    Z => Lit {t1=TString} (show n)
    (S Z) =>
      let ty = fetchTy n (x :: xs)
          e1 = assert_total (genExp x xs TString)
          e2 = assert_total (genExp x (reverse xs) ty)
      in Cnst {t1=TString} e1 {t2=ty} e2
    (S (S k)) => 
      let ty = fetchTy n (x :: xs)
          e1 = assert_total (genExp x xs (TFunc ty TString))
          e2 = assert_total (genExp x (reverse xs) ty)
      in App {t1=ty} e1 {t2=TString} e2
genExp n [] (TFunc a b) = 
  let e1 = genExp n [] a {v}
      e2 = genExp n [] b {v}
  in lam {t1=a} {t2=b} (Cnst {t1=b} e2 {t2=a})
genExp n (x :: xs) (TFunc TNat (TFunc TNat TNat)) = 
  case (modfin n 2) of
    Z => lam {t1=TNat}{t2=TFunc TNat TNat} (\x => 
          lam {t1=TNat}{t2=TNat} (\y => (Add {t1=TNat} x y)))
    (S k) => ?test --lam (\x => lam (\y => (Cnst x y)))
genExp n (x :: xs) (TFunc TInteger (TFunc TInteger TInteger)) = ?t5
genExp n (x :: xs) (TFunc a (TFunc b c)) = ?t6
genExp n (x :: xs) (TFunc a (TPair b c)) = ?t7
genExp n (x :: xs) (TFunc a (TSum b c)) = ?t8
genExp n (x :: xs) (TFunc a b) = ?t1
genExp n xs (TPair a b) = 
  let e1 = genExp n xs a
      e2 = genExp n (reverse xs) b
  in EPair {t1=a} e1 {t2=b} e2
genExp n xs (TSum a b) =
  let e1 = genExp n xs a {v}
      e2 = genExp n (reverse xs) b {v}
  in case (modfin n 2) of
       Z => ELeft {t1=a} {t2=b} e1
       (S k) => ERight {t1=a} {t2=b} e2


ex1 : Expr v (Nat -> Nat -> Nat)
ex1 = lam {t1=TNat} {t2=TFunc TNat TNat} (\x => 
        lam {t1=TNat} {t2=TNat} (\y => Add {t1=TNat} x y))
