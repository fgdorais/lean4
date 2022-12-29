/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian, Sebastian Ullrich
-/

prelude
import Init.Data.Int
import Init.Data.String

inductive Ordering where
  | lt | eq | gt
deriving Inhabited, BEq

class Ord (α : Type u) extends BEq α, LT α, LE α, Min α, Max α where
  compare : α → α → Ordering
  beq x y := compare x y == .eq
  lt x y := compare x y == .lt
  le x y := compare x y != .gt
  min x y := if compare x y != .gt then x else y
  max x y := if compare x y != .gt then y else x

export Ord (compare)

@[inline] def compareOfLE [LE α] [DecidableRel (LE.le (α:=α))] (x y : α) : Ordering :=
  if x ≤ y then if x ≥ y then .eq else .lt else .gt

def ordOfLE (α) [LE α] [DecidableRel (LE.le (α:=α))] : Ord α := {compare:=compareOfLE}

@[inline] def compareOfLessAndEq {α} (x y : α) [LT α] [Decidable (x < y)] [DecidableEq α] : Ordering :=
  if x < y then Ordering.lt
  else if x = y then Ordering.eq
  else Ordering.gt

instance : Ord Nat where
  compare x y := compareOfLessAndEq x y

instance : Ord Int where
  compare x y := compareOfLessAndEq x y

instance : Ord Bool where
  compare
  | false, true => Ordering.lt
  | true, false => Ordering.gt
  | _, _ => Ordering.eq

instance : Ord String where
  compare x y := compareOfLessAndEq x y

instance (n : Nat) : Ord (Fin n) where
  compare x y := compare x.val y.val

instance : Ord UInt8 where
  compare x y := compareOfLessAndEq x y

instance : Ord UInt16 where
  compare x y := compareOfLessAndEq x y

instance : Ord UInt32 where
  compare x y := compareOfLessAndEq x y

instance : Ord UInt64 where
  compare x y := compareOfLessAndEq x y

instance : Ord USize where
  compare x y := compareOfLessAndEq x y

instance : Ord Char where
  compare x y := compareOfLessAndEq x y

/-- The lexicographic order on pairs. -/
def lexOrd [Ord α] [Ord β] : Ord (α × β) where
  compare p1 p2 := match compare p1.1 p2.1 with
    | .eq => compare p1.2 p2.2
    | o   => o