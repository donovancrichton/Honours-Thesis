%default total

||| A run-time representation for a type.
public export
data TypeRep : Type -> Type where
  TBool : TypeRep Bool
  TNat : TypeRep Nat
  TInteger : TypeRep Integer
  TString : TypeRep String
  TFunc : TypeRep a -> TypeRep b -> TypeRep (a -> b)
  TPair : TypeRep a -> TypeRep b -> TypeRep (a, b)
  TSum : TypeRep a -> TypeRep b -> TypeRep (Either a b)

||| A Pi Type to extract the underlying type of the run-time representation.
||| TODO: Is this used anywhere?
public export
ExtractTy : (TypeRep a) -> Type
ExtractTy {a} t = a

||| Boolean equality between type representations
||| Unfortunately Idris is not smart enough to correctly match
||| all the false cases by default.
public export
beqType : TypeRep a -> TypeRep b -> Bool
beqType TBool TBool = True
beqType TBool TNat = False
beqType TBool TInteger = False
beqType TBool TString = False
beqType TBool (TFunc x y) = False
beqType TBool (TPair x y) = False
beqType TBool (TSum x y) = False
beqType TNat TBool = False
beqType TNat TNat = True
beqType TNat TInteger = False
beqType TNat TString = False
beqType TNat (TFunc x y) = False
beqType TNat (TPair x y) = False
beqType TNat (TSum x y) = False
beqType TInteger TBool = False
beqType TInteger TNat = False
beqType TInteger TInteger = True
beqType TInteger TString = False
beqType TInteger (TFunc x y) = False
beqType TInteger (TPair x y) = False
beqType TInteger (TSum x y) = False
beqType TString TBool = False
beqType TString TNat = False
beqType TString TInteger = False
beqType TString TString = True
beqType TString (TFunc x y) = False
beqType TString (TPair x y) = False
beqType TString (TSum x y) = False
beqType (TFunc x y) TNat = False
beqType (TFunc x y) TBool = False
beqType (TFunc x y) TInteger = False
beqType (TFunc x y) TString = False
beqType (TFunc x y) (TFunc a b) = beqType x a && beqType y b
beqType (TFunc x y) (TPair a b) = False
beqType (TFunc x y) (TSum a b) = False
beqType (TPair x y) TNat = False
beqType (TPair x y) TBool = False
beqType (TPair x y) TInteger = False
beqType (TPair x y) TString = False
beqType (TPair x y) (TFunc a b) = False
beqType (TPair x y) (TPair a b) = beqType x a && beqType y b
beqType (TPair x y) (TSum a b) = False
beqType (TSum x y) TNat = False
beqType (TSum x y) TBool = False
beqType (TSum x y) TInteger = False
beqType (TSum x y) TString = False
beqType (TSum x y) (TFunc a b) = False
beqType (TSum x y) (TPair a b) = False
beqType (TSum x y) (TSum a b) = beqType x a && beqType y b

||| Pretty printing for runtime representations of Types.
public export
prettyTy : TypeRep a -> String
prettyTy TBool = "Bool"
prettyTy TNat = "Nat"
prettyTy TInteger = "Integer"
prettyTy TString = "String"
prettyTy (TFunc x y) = "(" ++ prettyTy x ++ " -> " ++ prettyTy y ++ ")"
prettyTy (TPair x y) = "(" ++ prettyTy x ++ ", " ++ prettyTy y ++ ")"
prettyTy (TSum x y) = "(Either " ++ prettyTy x ++ " " ++ prettyTy y ++ ")"
