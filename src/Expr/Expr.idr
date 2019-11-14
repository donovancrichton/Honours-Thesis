import Typeable.Typeable

%default total

||| PHOAS Expression Langauge
||| see 'Typeable' for TypeRep explaination.
public export
data Expr : (v : Type -> Type) -> (a : Type) -> Type where
  Lit : Show a => {t1 : TypeRep a} -> a -> Expr v a 
  Var : {t1 : TypeRep a} -> v a -> Expr v a
  Lam : {t1 : TypeRep a} -> {t2 : TypeRep b} -> 
        (v a -> Expr v b) -> Expr v (a -> b)
  App : {t1 : TypeRep a} -> {t2 : TypeRep b} -> Expr v (a -> b) -> 
        Expr v a -> Expr v b
  Add : Num a => Expr v a -> {t1 : TypeRep a} -> Expr v a -> Expr v a
  Cnst : {t1 : TypeRep a} -> {t2 : TypeRep b} -> Expr v a -> Expr v b -> 
         Expr v a
  EPair : {t1 : TypeRep a} -> {t2 : TypeRep b} -> Expr v a -> Expr v b -> 
          Expr v (a, b)
  ELeft : {t1 : TypeRep a} -> {t2 : TypeRep b} -> Expr v a -> 
          Expr v (Either a b)
  ERight : {t1 : TypeRep a} -> {t2 : TypeRep b} -> Expr v b -> 
           Expr v (Either a b)

||| Weaken a non-positive function into a strictly positive one.
public export
weaken : {t1 : TypeRep a} -> (Expr v a -> Expr v b) -> 
         (v a -> Expr v b)
weaken {t1} f = \x => f (Var {t1} x)

||| Smart constructor for the 'Lam' case so weaken doesn't need to be 
||| explicitly called.
public export
lam : {t1 : TypeRep a} -> {t2 : TypeRep b} -> (Expr v a -> Expr v b) -> 
      Expr v (a -> b)
lam {t1}{t2} f = Lam {t1} {t2} (weaken {t1} f)

||| Polymorphic evaluator.
public export
eval : Expr (\x => x) a -> a
eval (Lit x) = x
eval (Var x) = x
eval (Lam f) = \x => eval (f x)
eval (App f x) = (eval f) (eval x)
eval (Add x y) = (eval x) + (eval y)
eval (Cnst x y) = const (eval x) (eval y)
eval (EPair x y) = (eval x, eval y)
eval (ELeft {b} x) = Left (eval x)
eval (ERight {a} x) = Right (eval x)

||| A HOAS encoding of `Expr a -> String` is too polymorphic
||| to reach under the lambda binding to access the body.
||| So here we pretty print with PHOAS.
||| (Needed to identify expressions/typereps in the IO monad)
public export
prettyE : Nat -> Expr (\_ => String) a -> String
prettyE k (Lit x) = show x
prettyE k (Var x) = "(Var " ++ x ++ ")"
prettyE k (Lam f) = 
  let x = "x" ++ (show k)
  in "(Lam " ++ x ++ " => " ++ prettyE (succ k) (f x) ++ ")"
prettyE k (App f x) = "(App " ++ prettyE k f ++ " " ++ prettyE k x ++ ")"
prettyE k (Add x y) = "(" ++ prettyE k x ++ " + " ++ prettyE k y ++ ")"
prettyE k (Cnst x y) = "(Const " ++ prettyE k x ++ " " ++ prettyE k y ++ ")"
prettyE k (EPair x y) = "(Pair " ++ prettyE k x ++ " " ++ prettyE k y ++ ")"
prettyE k (ELeft x) = "(Left " ++ prettyE k x ++ ")"
prettyE k (ERight x) = "(Right " ++ prettyE k x ++ ")"
