import Data.Fin

import Mod.Mod
import Typeable.Typeable
import Expr.Expr
import PHOASList.PHOASList
import Zipper.Zipper
import Proofs.Proofs

%default total

||| Given a list of Sigma types of a pair of Zippers,
|||   and some (presumably random) natural number:
|||   select that index.
public export
selectNode : (n : Nat) -> (xs : 
             PHOASList v (a : Type ** (Zipper v a, Zipper v a))) ->
             {auto prf : NonEmptyPL xs} -> 
             (a : Type ** (Zipper v a, Zipper v a))
selectNode n xs {prf} =
  let p1 = nonEmptyImpliesGTZ xs prf
      p2 = modfNlteN n (length xs) {prf = p1}
      p3 = ltLenAlwaysBound (modfin n (length xs)) xs p2
  in index (modfin n (length xs)) xs {prf=p3}

||| typeRepEq takes a PHOASList of the cartesian product of all possible
||| crossover pairs, and builds a PHOASList of only those pairs where crossover
||| is possible.
public export
typeRepEq : (xs : PHOASList v 
            ((x : Type ** (TypeRep x, Zipper v x)),
            (y : Type ** (TypeRep y, Zipper v y)))) ->
            PHOASList v (a : Type ** (Zipper v a, Zipper v a))
typeRepEq xs = foldr f [] xs
  where
    f : {v : Type -> Type} -> 
        (xy : ((x : Type ** (TypeRep x, Zipper v x)),
              (y : Type ** (TypeRep y, Zipper v y)))) ->
        PHOASList v (a : Type ** (Zipper v a, Zipper v a)) ->
        PHOASList v (a : Type ** (Zipper v a, Zipper v a))
    f ((t1 ** (r1, z1)),(t2 ** (r2, z2))) xs with (beqType r1 r2) proof p
      f ((t1 ** (r1, z1)),(t2 ** (r2, z2))) xs | True =
        let p1 = beqTypeReflectsEq r1 r2 (sym p)
            z3 = replace (sym p1) z2
        in (_ ** (z1, z3)) :: xs
      f ((t1 ** (r1, z1)),(t2 ** (r2, z2))) xs | False = xs

||| A type preserving crossover function that is correct by construction
public export
xover : (zs : (a : Type ** (Zipper v a, Zipper v a))) ->
        (Zipper v (fst zs), Zipper v (fst zs))
xover (t ** (Zip {z1} e1 c1, Zip e2 c2)) = (Zip {z1} e2 c1, Zip {z1} e1 c2)
