import Expr.Expr
import Typeable.Typeable

%default total

||| The indexed family calculating the type when walking left on an Expr.
public export
GoLeft : Expr v a -> Maybe Type
GoLeft (Lit x) = Nothing
GoLeft (Var x) = Nothing
GoLeft (Lam f) = Nothing
GoLeft (EPair {a} x y) = Just a
GoLeft (ELeft x) = Nothing
GoLeft (ERight x) = Nothing
GoLeft (App {a}{b} f x) = Just (a -> b)
GoLeft (Add {a} x y) = Just a
GoLeft (Cnst {a} x y) = Just a

||| The indexed family calculating the type when walking right on an Expr.
public export
GoRight : Expr v a -> Maybe Type
GoRight (Lit x) = Nothing
GoRight (Var x) = Nothing
GoRight (Lam f) = Nothing
GoRight (EPair {b} x y) = Just b
GoRight (ELeft x) = Nothing
GoRight (ERight x) = Nothing
GoRight (App f {a} x) = Just a
GoRight (Add x {a} y) = Just a
GoRight (Cnst x {b} y) = Just b

||| The indexed family calculating the type when walking down on an Expr.
public export
GoDown : Expr v a -> Maybe Type
GoDown (Lit x) = Nothing
GoDown (Var x) = Nothing
GoDown (Lam {a}{b} f) = Nothing
GoDown (App f x) = Nothing
GoDown (Add x y) = Nothing
GoDown (Cnst x y) = Nothing
GoDown (EPair x y) = Nothing
GoDown (ELeft {a}{b} x) = Just a
GoDown (ERight {b}{a} x) = Just b

||| An ordinary Cons list but indexed by the PHOAS parameter so I don't
||| need to carry it around inside Sigma types everwhere.
public export
data PHOASList : (v : Type -> Type) -> (a : Type) -> Type where
  Nil  : PHOASList v a
  (::) : a -> PHOASList v a -> PHOASList v a

||| Append for PHOASList.
public export
(++) : PHOASList v a -> PHOASList v a -> PHOASList v a
(++) Nil xs = xs
(++) (x :: xs) ys = x :: xs ++ ys

||| InBounds for PHOASLists
public export
data InPList : (k : Nat) -> (xs : PHOASList v a) -> Type where
  InNow : InPList Z (x :: xs)
  InAfter : InPList k xs -> InPList (S k) (x :: xs)

||| Index for PHOASLists
public export
index : (n : Nat) -> (xs : PHOASList v a) -> {auto prf: InPList n xs} -> a
index Z (x :: xs) = x
index (S k) (x :: xs) {prf = InAfter p} = index k xs

||| The context contains all information necessary to rebuild the expression
||| tree.
public export
data Context : (Type -> Type) -> Maybe Type -> Type where
  Root : Context v (Just a)
  L : (x : Expr v a) -> Context v (Just a) -> Context v (GoLeft x)
  R : (x : Expr v a) -> Context v (Just a) -> Context v (GoRight x)
  D : (x : Expr v a) -> Context v (Just a) -> Context v (GoDown x)

||| A modified Hamana-Fiore style dependent-zipper.
public export
data Zipper : (Type -> Type) -> Type -> Type where
  Zip : {z1 : TypeRep a} -> Expr v a -> Context v (Just a) -> Zipper v a

||| extract the focus from a Zipper.
public export
extract : Zipper v a -> Expr v a
extract (Zip e c) = e

||| A convenience function to wrap a zipper up in a Sigma type.
public export
wrap : Zipper v a -> (v : (Type -> Type) ** a : Type ** Zipper v a)
wrap {v} {a} z = (v ** a ** z)

||| Rebuild a tree.
public export
up : (a : Type ** Zipper v a) -> (b : Type ** Zipper v b)
up (t ** pf) = 
  case pf of
    (Zip {z1} e {a} Root) => (a ** Zip e {z1} Root)
    (Zip e (L (Lit x) c)) impossible
    (Zip e (L (Lam f) c)) impossible
    (Zip e (L (App {t1}{t2} f x) c)) => (_ ** (Zip {z1=t2} (App {t1}{t2} e x) c))
    (Zip e (L (Add {t1} x y) c)) => (_ ** (Zip {z1=t1} (Add {t1} e y) c))
    (Zip e (L (Cnst {t1}{t2}  x y) c)) => (_ ** (Zip {z1=t1} (Cnst {t1}{t2} e y) c))
    (Zip e (L (EPair {t1}{t2} {a}{b} x y) c)) => 
      ((a,b) ** (Zip {z1=TPair t1 t2} (EPair {t1}{t2} e y) c))
    (Zip e (L (ELeft x) c)) impossible
    (Zip e (L (ERight x) c)) impossible
    (Zip e (R (Lit x) c)) impossible
    (Zip e (R (Lam f) c)) impossible
    (Zip e (R (App {t1}{t2}{b} f x) c)) => (b ** (Zip {z1=t2} (App {t1}{t2} f e) c))
    (Zip e (R (Add {t1} {a} x y) c)) => (a ** (Zip {z1=t1} (Add {t1} x e) c))
    (Zip e (R (Cnst {t1}{t2}{a} x y) c)) => 
      (a ** (Zip {z1=t1} (Cnst {t1}{t2} x e) c))
    (Zip e (R (EPair {t1}{t2} {a}{b} x y) c)) => 
      ((a,b) ** (Zip {z1=TPair t1 t2} (EPair {t1}{t2} x e) c))
    (Zip e (R (ELeft x) c)) impossible
    (Zip e (R (ERight x) c)) impossible
    (Zip e (D (Lit x) c)) impossible
    (Zip e (D (Lam f) c)) impossible
    (Zip e (D (App f x) c)) impossible
    (Zip e (D (Add x y) c)) impossible
    (Zip e (D (Cnst x y) c)) impossible
    (Zip e (D (EPair x y) c)) impossible
    (Zip e (D (ELeft {t1}{t2} {a} {b} x) c)) => 
      (Either a b ** (Zip {z1=TSum t1 t2} (ELeft {t1}{t2} e) c))
    (Zip e (D (ERight {t1}{t2} {a} {b} x) c)) => 
      (Either a b ** (Zip {z1=TSum t1 t2} (ERight {t1} {t2} e) c))

||| A convenience function to move the focus all the way to the root
public export
top : (a ** Zipper v a) -> (b ** Zipper v b)
top (a ** (Zip {z1} e Root)) = (a ** (Zip {z1} e Root))
top (a ** (Zip {z1} e c)) = 
  let s = assert_smaller (a ** (Zip e {z1} c)) (up (a ** (Zip {z1} e c)))
  in top s

||| Flatten a zipper into a list of all possible foci
public export
flatten : Zipper v a -> 
          PHOASList v (x : Type ** (TypeRep x, Zipper v x))
flatten (Zip {z1} e@(Lit {t1} {a} x) c) = [(a ** (z1, (Zip {z1} e c)))]
flatten (Zip {z1} e@(Var {t1} {a} x) c) = [(a ** (z1, (Zip {z1} e c)))]
flatten (Zip {z1} e@(Lam {t1}{t2}{a}{b} f) c) = [(a -> b ** (z1, (Zip {z1} e c)))]
flatten (Zip {z1} e@(App {t1}{t2} {a}{b} f x) c) =
  let zl = assert_total $ flatten (Zip {z1 = TFunc t1 t2} f (L e c))
      zr = assert_total $ flatten (Zip {z1=t1} x (R e c))
  in zl ++ zr ++ [(b ** (z1, (Zip {z1} e c)))]
flatten (Zip {z1} e@(Add {t1}{a} x y) c) =
  let zl = assert_total $ flatten (Zip {z1=t1} x (L e c))
      zr = assert_total $ flatten (Zip {z1=t1} y (R e c))
  in zl ++ zr ++ [(a ** (z1, (Zip {z1} e c)))]
flatten (Zip {z1} e@(Cnst {t1}{t2} x y) c) =
  let zl = assert_total $ flatten (Zip {z1=t1} x (L e c))
      zr = assert_total $ flatten (Zip {z1=t2} y (R e c))
  in zl ++ zr ++ [(a ** (z1, (Zip {z1} e c)))]
flatten (Zip {z1} e@(EPair {t1}{t2}{a}{b} x y) c) =
  let zl = assert_total $ flatten (Zip {z1=t1} x (L e c))
      zr = assert_total $ flatten (Zip {z1=t2} y (R e c))
  in zl ++ zr ++ [((a, b) ** (z1, (Zip {z1} e c)))]
flatten (Zip {z1} e@(ELeft {t1}{t2} {a}{b} x) c) =
  let zd = assert_total $ flatten (Zip {z1=t1} x (D e c))
  in zd ++ [(Either a b ** (z1, (Zip {z1} e c)))]
flatten (Zip {z1} e@(ERight {t1}{t2}{a}{b} x) c) =
  let zd = assert_total $ flatten (Zip {z1=t2} x (D e c))
  in zd ++ [(Either a b ** (z1, (Zip {z1} e c)))]

||| substitute in a new focus expression into a zipper
public export
subst : (x : (v : (Type -> Type) ** a : Type ** Zipper v a)) ->
        Expr (fst x) (fst (snd x)) -> Zipper (fst x) (fst (snd x))
subst (v ** x ** (Zip {z1} e' c)) e = Zip {z1} e c

||| Pretty printer for contexts
public export
prettyC : Context (\_ => String) a -> String
prettyC Root = " Root"
prettyC (L e c) = "(L " ++ prettyE 0 e ++ prettyC c ++ ")"
prettyC (R e c) = "(R " ++ prettyE 0 e ++ prettyC c ++ ")"
prettyC (D e c) = "(D " ++ prettyE 0 e ++ prettyC c ++ ")"

||| pretty printer for zippers
public export
prettyZ : Zipper (\_ => String) a -> String
prettyZ (Zip e c) = "Zip " ++ prettyE 0 e ++ " [C: " ++ prettyC c ++ "]"
