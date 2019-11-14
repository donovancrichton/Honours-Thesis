import PHOASList.PHOASList
import Typeable.Typeable
import Expr.Expr
import Zipper.Zipper
import Generators.Generators

ex1 : Expr v Integer
ex1 = Add {t1=TInteger} (Lit {t1=TInteger} 2) (Lit {t1=TInteger} 3)

zip1 : Zipper v Integer
zip1 = Zip ex1 Root

positions : PHOASList v (x : Type ** (TypeRep x, Zipper v x))
positions = flatten zip1

focus : Zipper v Integer
focus = snd $ snd $ index 2 positions

replace : Nat -> Zipper v a -> Zipper v a
replace n (Zip {z1} e c) = 
  let e' = genExp n z1
  in Zip {z1} e' c



