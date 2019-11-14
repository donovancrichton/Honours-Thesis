import Typeable.Typeable
import Mod.Mod
import Expr.Expr
import PHOASList.PHOASList
import Proofs.Proofs
import Zipper.Zipper
import Crossover.Crossover

import System

%default total

ex1 : Expr v Nat
ex1 = Add {t1=TNat} (Lit {t1=TNat} 2) 
       (Cnst {t1=TNat} {t2=TString}
          (Lit {t1 = TNat} 3) (Lit {t1 = TString} "Test"))

ex2 : Expr v Nat
ex2 = Add {t1=TNat} (Lit {t1=TNat} 2) 
       (Cnst {t1=TNat} {t2=TString}
          (Lit {t1 = TNat} 3) (Lit {t1 = TString} "Hello"))

zipExp1 : Zipper v Nat
zipExp1 = Zip {z1=TNat} ex1 Root

zipExp2 : Zipper v Nat
zipExp2 = Zip {z1=TNat} ex2 Root

||| The cartesian product of possible focus pairs between zipExp1 and zipExp2
cartProdZipExp : PHOASList v ((x : Type ** (TypeRep x, Zipper v x)),
                              (y : Type ** (TypeRep y, Zipper v y)))
cartProdZipExp = (\a, b => (a, b)) <$> (flatten zipExp1) <*> (flatten zipExp2)


||| A control function that selects a crossover point and does not
||| perform crossover
noOver : Nat -> ((a : Type ** Zipper v a), (b : Type ** Zipper v b))
noOver n = (top x, top y)
  where 
    xys : (a : Type ** (Zipper v a, Zipper v a))
    xys = selectNode n (typeRepEq cartProdZipExp)
    
    x : (a : Type ** Zipper v a)
    x = (DPair.fst xys ** (Basics.fst (DPair.snd xys)))

    y : (a : Type ** Zipper v a)
    y = (DPair.fst xys ** (Basics.snd (DPair.snd xys)))

||| A function that selects the same point as 'noover' and performs the
||| crossover operation
testOver : Nat -> ((a : Type ** Zipper v a), (b : Type ** Zipper v b))
testOver n =
  let xys = xover $ selectNode n (typeRepEq cartProdZipExp)
      x = (_ ** Basics.fst xys)
      y = (_ ** Basics.snd xys)
in (top x, top y)

||| A convenience function to read bytes from /dev/urandom.
getChars : File -> List (IO (Either FileError Char)) -> Nat ->
           List (IO (Either FileError Char))
getChars f xs Z = fgetc f :: xs
getChars f xs (S k) = fgetc f :: getChars f xs k

main : IO ()
main = do
  let path = "/dev/urandom"

  Right (FHandle ptr) <- openFile path Read | Left err => do
    putStrLn (show err)
  cs <- sequence $ getChars (FHandle ptr) [] 4

  Right str <- pure (sequence cs) | Left err => do
    putStrLn (show err)
  
  closeFile (FHandle ptr)
  let ints = (\x => cast x {to=Int}) <$> str
  (x :: xs) <- pure ints | [] => putStrLn "Error somehow we have an empty List"
  
  let i = x
  let n = cast i {to=Nat}
  let xs' = (\x => cast x {to=Nat}) <$> ints
  let s = show i
  let control = noOver n {v=\x => x}
  let xo = testOver n {v = \x => x}
  let list = typeRepEq cartProdZipExp {v= (\x => String)}
  let xolen = length list
  let xomod = modfin n xolen
  let printctrl = noOver n {v = \_ => String}
  let printxo = testOver n {v = \_ => String}
  let c1 = extract $ DPair.snd $ Basics.fst control
  let p1 = extract $ DPair.snd $ Basics.fst printctrl
  let c2 = extract $ DPair.snd $ Basics.snd control
  let p2 = extract $ DPair.snd $ Basics.snd printctrl
  let x1 = extract $ DPair.snd $ Basics.fst printxo
  let x2 = extract $ DPair.snd $ Basics.snd printxo
  
  putStrLn "-------------------GENERATING RANDOM NUMBER----------------"
  putStrLn ("Random number is: " ++ s)
  putStrLn ("List of numbers: " ++ show (x :: xs))
  putStrLn "----------PRINTING CONTROL EXPRESSIONS (No Crossover!)------"
  putStrLn (prettyE 0 p1)
  putStrLn (prettyE 0 p2)
  putStrLn "-----------NUMBER OF VALID POSITIONS FOR CROSSOVER----------"
  putStrLn (show xolen)
  putStrLn "------------POSITION CHOSEN FROM VALID POSITIONS------------"
  putStrLn (show xomod)
  putStrLn "-------------PRINTING CROSSED OVER EXPRESSIION VALUES---------"
  putStrLn (prettyE 0 x1)
  putStrLn (prettyE 0 x2)
  putStrLn "---------------------------END PROGRAM-----------------------"

