

universe u v

inductive arrow (α : Type u) (β : Type v)
| mk : (α → β) → arrow α β

inductive foo
| mk : arrow Nat foo → foo

/--
info: inductive foo : Type
number of parameters: 0
constructors:
foo.mk : arrow Nat foo → foo
-/
#guard_msgs in
#print foo

#print foo.rec
set_option pp.all true
#print foo.below

mutual

inductive foo2 : Type
| mk : arrow2 → foo2

inductive arrow2 : Type
| mk : (Nat → foo2) → arrow2

end

#print foo2.brecOn
