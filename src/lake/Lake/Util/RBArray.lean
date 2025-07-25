/-
Copyright (c) 2023 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Std.Data.TreeMap.Basic

namespace Lake

/--
There are two ways to think of this type:
* As an `Array` of values with a `Std.TreeMap` key-value index for the key `α`.
* As a `Std.TreeMap` that preserves insertion order, but is optimized for
iteration-by-values. Thus, it does not store the order of keys.
-/
structure RBArray (α : Type u) (β : Type v) (cmp : α → α → Ordering) where
  toTreeMap : Std.TreeMap α β cmp
  toArray : Array β

namespace RBArray

def empty : RBArray α β cmp :=
  ⟨.empty, .empty⟩

instance : EmptyCollection (RBArray α β cmp) := ⟨empty⟩

def mkEmpty (size : Nat) : RBArray α β cmp :=
  ⟨.empty, .mkEmpty size⟩

@[inline] def find? (self : RBArray α β cmp) (a : α) : Option β :=
  self.toTreeMap.get? a

@[inline] def contains (self : RBArray α β cmp) (a : α) : Bool :=
  self.toTreeMap.contains a

/-- Insert `b` with the key `a`. Does nothing if the key is already present. -/
def insert (self : RBArray α β cmp) (a : α) (b : β) : RBArray α β cmp :=
  if self.toTreeMap.contains a then
    self
  else
    ⟨self.toTreeMap.insert a b, self.toArray.push b⟩

@[inline] def all (f : β → Bool) (self : RBArray α β cmp) : Bool  :=
  self.toArray.all f

@[inline] def any (f : β → Bool) (self : RBArray α β cmp) : Bool  :=
  self.toArray.any f

@[inline] def foldl (f : σ → β → σ) (init : σ) (self : RBArray α β cmp) : σ  :=
  self.toArray.foldl f init

@[inline] def foldlM [Monad m] (f : σ → β → m σ) (init : σ) (self : RBArray α β cmp) : m σ :=
  self.toArray.foldlM f init

@[inline] def foldr (f : β → σ → σ) (init : σ) (self : RBArray α β cmp) : σ :=
  self.toArray.foldr f init

@[inline] def foldrM [Monad m] (f : β → σ → m σ) (init : σ) (self : RBArray α β cmp) : m σ :=
  self.toArray.foldrM f init

@[inline] def forM [Monad m] (f : β → m PUnit) (self : RBArray α β cmp) : m PUnit :=
  self.toArray.forM f

@[inline] protected def forIn [Monad m] (self : RBArray α β cmp) (init : σ) (f : β → σ → m (ForInStep σ)) : m σ :=
  ForIn.forIn self.toArray init f

instance : ForIn m (RBArray α β cmp) β := ⟨RBArray.forIn⟩

end RBArray

@[inline] def mkRBArray  (f : β → α) (vs : Array β) : RBArray α β cmp :=
  vs.foldl (init := RBArray.mkEmpty vs.size) fun m v => m.insert (f v) v
