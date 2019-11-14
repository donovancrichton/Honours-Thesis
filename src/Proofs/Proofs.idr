import Data.Fin

import Mod.Mod
import Typeable.Typeable
import PHOASList.PHOASList

%default total

||| A proof that if the run-time representation of two types are equal
||| Then those types are constructively equal.
public export
typeRepInj : (prf : TypeRep a = TypeRep b) -> (a = b)
typeRepInj Refl = Refl

||| Congruence on two equality proofs.
public export
cong2 : {f : Type -> Type -> Type} -> (a = c) -> (b = d) -> (f a b = f c d)
cong2 Refl Refl = Refl

||| Specific two equality congruence proof for product types.
public export
cong2p : (a = c) -> (b = d) -> (a, b) = (c, d)
cong2p Refl Refl = Refl

||| An equality of products implies a product of equalities.
public export
p2cong : (prf : (a, b) = (c, d)) -> (a = c, b = d)
p2cong Refl = (Refl, Refl)

||| Specific two equality congruence proof for function types.
public export
cong2f : (a = c) -> (b = d) -> (a -> b) = (c -> d)
cong2f Refl Refl = Refl

||| Proof of the injectivity of a boolean AND when True on pair.
public export
bandIsInjective : (x, y : Bool) -> (prf: (x && y) = True) -> (x = True, y = True)
bandIsInjective False False prf = absurd prf
bandIsInjective False True prf = absurd prf
bandIsInjective True False prf = absurd prf
bandIsInjective True True prf = (Refl, Refl)

||| Proof that boolean equality between run-time type representations
||| implies constructive equality between types.
public export
beqTypeReflectsEq : {a, b : Type} -> (x: TypeRep a) -> (y: TypeRep b) ->
                    (prf : beqType x y = True) -> (a = b)
beqTypeReflectsEq TBool TBool prf = Refl
beqTypeReflectsEq TBool TNat prf = absurd prf
beqTypeReflectsEq TBool TInteger prf = absurd prf
beqTypeReflectsEq TBool TString prf = absurd prf
beqTypeReflectsEq TBool (TFunc x y) prf = absurd prf
beqTypeReflectsEq TBool (TPair x y) prf = absurd prf
beqTypeReflectsEq TBool (TSum x y) prf = absurd prf
beqTypeReflectsEq TNat TBool prf = absurd prf
beqTypeReflectsEq TNat TNat prf = Refl
beqTypeReflectsEq TNat TInteger prf = absurd prf
beqTypeReflectsEq TNat TString prf = absurd prf
beqTypeReflectsEq TNat (TFunc x y) prf = absurd prf
beqTypeReflectsEq TNat (TPair x y) prf = absurd prf
beqTypeReflectsEq TNat (TSum x y) prf = absurd prf
beqTypeReflectsEq TInteger TBool prf = absurd prf
beqTypeReflectsEq TInteger TNat prf = absurd prf
beqTypeReflectsEq TInteger TInteger prf = Refl
beqTypeReflectsEq TInteger TString prf = absurd prf
beqTypeReflectsEq TInteger (TFunc x y) prf = absurd prf
beqTypeReflectsEq TInteger (TPair x y) prf = absurd prf
beqTypeReflectsEq TInteger (TSum x y) prf = absurd prf
beqTypeReflectsEq TString TBool prf = absurd prf
beqTypeReflectsEq TString TNat prf = absurd prf
beqTypeReflectsEq TString TInteger prf = absurd prf
beqTypeReflectsEq TString TString prf = Refl
beqTypeReflectsEq TString (TFunc x y) prf = absurd prf
beqTypeReflectsEq TString (TPair x y) prf = absurd prf
beqTypeReflectsEq TString (TSum x y) prf = absurd prf
beqTypeReflectsEq (TFunc x y) TBool prf = absurd prf
beqTypeReflectsEq (TFunc x y) TNat prf = absurd prf
beqTypeReflectsEq (TFunc x y) TInteger prf = absurd prf
beqTypeReflectsEq (TFunc x y) TString prf = absurd prf
beqTypeReflectsEq (TFunc x y) (TFunc z w) prf =
  let p1 = bandIsInjective (beqType x z) (beqType y w) prf
      rec1 = beqTypeReflectsEq x z (fst p1)
      rec2 = beqTypeReflectsEq y w (snd p1)
  in cong2f rec1 rec2
beqTypeReflectsEq (TFunc x y) (TPair z w) prf = absurd prf
beqTypeReflectsEq (TFunc x y) (TSum z w) prf = absurd prf
beqTypeReflectsEq (TPair x y) TBool prf = absurd prf
beqTypeReflectsEq (TPair x y) TNat prf = absurd prf
beqTypeReflectsEq (TPair x y) TInteger prf = absurd prf
beqTypeReflectsEq (TPair x y) TString prf = absurd prf
beqTypeReflectsEq (TPair x y) (TFunc z w) prf = absurd prf
beqTypeReflectsEq (TPair x y) (TPair z w) prf =
  let p1 = bandIsInjective (beqType x z) (beqType y w) prf
      rec1 = beqTypeReflectsEq x z (fst p1)
      rec2 = beqTypeReflectsEq y w (snd p1)
  in cong2 rec1 rec2
beqTypeReflectsEq (TPair x y) (TSum z w) prf = absurd prf
beqTypeReflectsEq (TSum x y) TBool prf = absurd prf
beqTypeReflectsEq (TSum x y) TNat prf = absurd prf
beqTypeReflectsEq (TSum x y) TInteger prf = absurd prf
beqTypeReflectsEq (TSum x y) TString prf = absurd prf
beqTypeReflectsEq (TSum x y) (TFunc z w) prf = absurd prf
beqTypeReflectsEq (TSum x y) (TPair z w) prf = absurd prf
beqTypeReflectsEq (TSum x y) (TSum z w) prf =
  let p1 = bandIsInjective (beqType x z) (beqType y w) prf
      rec1 = beqTypeReflectsEq x z (fst p1)
      rec2 = beqTypeReflectsEq y w (snd p1)
in cong2 rec1 rec2

||| Proof that x != 0 implies that x >= 0 forall natural numbers.
public export
notZimpliesGTZ : (x : Nat) -> (prf : Not (x = 0)) -> GT x Z
notZimpliesGTZ Z prf = void (prf Refl)
notZimpliesGTZ (S k) prf = LTESucc LTEZero

||| Proof that x > 0 implies that x != 0 forall natural numbers.
public export
gTZimpliesZ : (x : Nat) -> (prf : GT x Z) -> Not (x = 0)
gTZimpliesZ Z prf = absurd prf
gTZimpliesZ (S k) prf = SIsNotZ

||| Proof that for a given non-empty PHOASList, that the length
||| of such a list must be greater than zero.
public export
nonEmptyImpliesGTZ : (xs : PHOASList v a) -> (prf : NonEmptyPL xs) ->
                      GT (length xs) Z
nonEmptyImpliesGTZ [] prf = absurd prf
nonEmptyImpliesGTZ (x :: xs) prf = LTESucc LTEZero


||| Proof that for a given element and given PHOASList, the length of the list
||| built from prepending the elemnt to the original list must be
||| greater than zero.
consGTZ : (x : a) -> (xs : PHOASList v a) -> GT (length (x :: xs)) Z
consGTZ x [] = lteRefl
consGTZ x (y :: ys) = LTESucc LTEZero

||| Proof that forall Natural numbers: 'y', given a list of length y: 'xs'
||| and a proof that y is not zero. Then xs must not be empty.
lenGTZimpliesNonEmpty : (y : Nat) -> (xs : PHOASList v a) -> (prf : y = length xs) ->
                        (prf2 : GT y Z) -> NonEmptyPL xs
lenGTZimpliesNonEmpty Z xs prf prf2 = absurd prf2
lenGTZimpliesNonEmpty (S k) [] prf prf2 = absurd prf
lenGTZimpliesNonEmpty (S k) (x :: xs) prf prf2 = IsNonEmptyPL

||| Proof that for all elements of a finite set 'f' with a supremum 'n'
||| Any (successful) increments to the index of 'f' must be <= n.
public export
finLTBound : (f : Fin n) -> LTE (S (finToNat f)) n
finLTBound FZ = LTESucc LTEZero
finLTBound (FS x) =
  let rec = finLTBound x
  in LTESucc rec

||| Proof that for all natural numbers: n given a PHOASList: xs
||| and a proof that n < length xs then element at index n is
||| guaranteed to be in the PHOASList.
public export
ltLenAlwaysBound : (n : Nat) -> (xs : PHOASList v a) -> 
                   (prf : LTE (S n) (length xs)) -> InPList n xs
ltLenAlwaysBound Z [] prf = absurd prf
ltLenAlwaysBound Z (x :: xs) prf = InNow
ltLenAlwaysBound (S k) (x :: xs) prf =
  let rec = ltLenAlwaysBound k xs
  in InAfter (rec (fromLteSucc prf))

||| proof that natural numbers x and y, given a proof that y > 0 
||| then mod x y + 1 <= y
public export
modfNlteN : (x, y : Nat) -> {auto prf : GT y Z} -> LTE (S (modfin x y)) y
modfNlteN x y = finLTBound (modf x y)

