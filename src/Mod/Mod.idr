import Data.Fin
%default total

||| helper function on finite sets rather than natural numbers
public export
modf : (x, y : Nat) -> {auto prf : GT y Z} -> Fin y
modf Z (S k) = FZ
modf (S k) (S j) with (strengthen (modf k (S j)))
  modf (S k) (S j) | Left bounds = FZ
  modf (S k) (S j) | Right rem = FS rem

||| mod on natural numbers using finite sets
public export
modfin : (x, y : Nat) -> {auto prf : GT y Z} -> Nat
modfin x y = finToNat (modf x y)

