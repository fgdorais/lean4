/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Paul Reichert
-/
module

prelude
public import Std.Data.DTreeMap.Internal.Lemmas
public import Std.Data.DTreeMap.Raw.Basic
public import Std.Data.DTreeMap.Raw.AdditionalOperations

@[expose] public section

/-!
# Dependent tree map lemmas

This file contains lemmas about `Std.Data.DTreeMap.Raw.Basic`. Most of the lemmas require
`TransCmp cmp` for the comparison function `cmp` and a proof that the involved maps are well-formed.
These proofs can be obtained from `Std.Data.DTreeMap.Raw.WF`.
-/

set_option linter.missingDocs true
set_option autoImplicit false

open Std.DTreeMap.Internal

universe u v w w'

namespace Std.DTreeMap.Raw

variable {α : Type u} {β : α → Type v} {γ : α → Type w} {cmp : α → α → Ordering} {t : DTreeMap.Raw α β cmp}
local instance : Coe (Type v) (α → Type v) where coe γ := fun _ => γ

private theorem ext {t t' : Raw α β cmp} : t.inner = t'.inner → t = t' := by
  cases t; cases t'; rintro rfl; rfl

@[simp, grind =]
theorem isEmpty_emptyc : (∅ : DTreeMap.Raw α β cmp).isEmpty :=
  Impl.isEmpty_empty

@[simp, grind =]
theorem isEmpty_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).isEmpty = false :=
  Impl.isEmpty_insert! h

theorem mem_iff_contains {k : α} : k ∈ t ↔ t.contains k :=
  Impl.mem_iff_contains

@[simp, grind _=_]
theorem contains_iff_mem {k : α} : t.contains k ↔ k ∈ t :=
  Impl.contains_iff_mem

theorem contains_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) :
    t.contains k = t.contains k' :=
  Impl.contains_congr h hab

theorem mem_congr [TransCmp cmp] (h : t.WF) {k k' : α} (hab : cmp k k' = .eq) : k ∈ t ↔ k' ∈ t :=
  Impl.mem_congr h hab

@[simp, grind =]
theorem contains_emptyc {k : α} : (∅ : Raw α β cmp).contains k = false :=
  Impl.contains_empty

@[simp]
theorem not_mem_emptyc {k : α} : k ∉ (∅ : Raw α β cmp) :=
  Impl.not_mem_empty

theorem contains_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty → t.contains a = false :=
  Impl.contains_of_isEmpty h

theorem not_mem_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty → a ∉ t :=
  Impl.not_mem_of_isEmpty h

theorem isEmpty_eq_false_iff_exists_contains_eq_true [TransCmp cmp] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, t.contains a = true :=
  Impl.isEmpty_eq_false_iff_exists_contains_eq_true h

theorem isEmpty_eq_false_iff_exists_mem [TransCmp cmp] (h : t.WF) :
    t.isEmpty = false ↔ ∃ a, a ∈ t :=
  Impl.isEmpty_eq_false_iff_exists_mem h

theorem isEmpty_eq_false_of_contains [TransCmp cmp] (h : t.WF) {a : α} (hc : t.contains a = true) :
    t.isEmpty = false :=
  Impl.isEmpty_eq_false_of_contains h hc

theorem isEmpty_iff_forall_contains [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, t.contains a = false :=
  Impl.isEmpty_iff_forall_contains h

theorem isEmpty_iff_forall_not_mem [TransCmp cmp] (h : t.WF) :
    t.isEmpty = true ↔ ∀ a, ¬a ∈ t :=
  Impl.isEmpty_iff_forall_not_mem h

@[simp]
theorem insert_eq_insert {p : (a : α) × β a} : Insert.insert p t = t.insert p.1 p.2 :=
  rfl

@[simp]
theorem singleton_eq_insert {p : (a : α) × β a} :
    Singleton.singleton p = (∅ : Raw α β cmp).insert p.1 p.2 :=
  rfl

@[simp, grind =]
theorem contains_insert [h : TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).contains a = (cmp k a == .eq || t.contains a) :=
  Impl.contains_insert! h

@[simp, grind =]
theorem mem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert k v ↔ cmp k a = .eq ∨ a ∈ t :=
  Impl.mem_insert! h

theorem contains_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).contains k :=
  Impl.contains_insert!_self h

theorem mem_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insert k v :=
  Impl.mem_insert!_self h

theorem contains_of_contains_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).contains a → cmp k a ≠ .eq → t.contains a :=
  Impl.contains_of_contains_insert! h

theorem mem_of_mem_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insert k v → cmp k a ≠ .eq → a ∈ t :=
  Impl.mem_of_mem_insert! h

@[simp, grind =]
theorem size_emptyc : (∅ : Raw α β cmp).size = 0 :=
  Impl.size_empty

theorem isEmpty_eq_size_eq_zero (h : t.WF) :
    t.isEmpty = (t.size == 0) :=
  Impl.isEmpty_eq_size_eq_zero h.out

@[grind =] theorem size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).size = if t.contains k then t.size else t.size + 1 :=
  Impl.size_insert! h

theorem size_le_size_insert [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insert k v).size :=
  Impl.size_le_size_insert! h

theorem size_insert_le [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).size ≤ t.size + 1 :=
  Impl.size_insert!_le h

@[simp, grind =]
theorem erase_emptyc {k : α} :
    (∅ : Raw α β cmp).erase k = ∅ :=
  ext <| Impl.erase!_empty (instOrd := ⟨cmp⟩) (k := k)

@[simp, grind =]
theorem isEmpty_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).isEmpty = (t.isEmpty || (t.size == 1 && t.contains k)) :=
  Impl.isEmpty_erase! h

theorem isEmpty_eq_isEmpty_erase_and_not_contains [TransCmp cmp] (h : t.WF) (k : α) :
    t.isEmpty = ((t.erase k).isEmpty && !(t.contains k)) :=
  Impl.isEmpty_eq_isEmpty_erase!_and_not_containsKey h k

theorem isEmpty_eq_false_of_isEmpty_erase_eq_false [TransCmp cmp] (h : t.WF) {k : α}
    (he : (t.erase k).isEmpty = false) :
    t.isEmpty = false :=
  Impl.isEmpty_eq_false_of_isEmpty_erase!_eq_false h he

@[simp, grind =]
theorem contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a = (cmp k a != .eq && t.contains a) :=
  Impl.contains_erase! h

@[simp, grind =]
theorem mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k ↔ cmp k a ≠ .eq ∧ a ∈ t :=
  Impl.mem_erase! h

theorem contains_of_contains_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).contains a → t.contains a :=
  Impl.contains_of_contains_erase! h

theorem mem_of_mem_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    a ∈ t.erase k → a ∈ t :=
  Impl.mem_of_mem_erase! h

@[grind =] theorem size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size = if t.contains k then t.size - 1 else t.size :=
  Impl.size_erase! h

theorem size_erase_le [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).size ≤ t.size :=
  Impl.size_erase!_le h

theorem size_le_size_erase [TransCmp cmp] (h : t.WF) {k : α} :
    t.size ≤ (t.erase k).size + 1 :=
  Impl.size_le_size_erase! h

@[simp, grind =]
theorem containsThenInsert_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v).1 = t.contains k :=
  Impl.containsThenInsert!_fst h

@[simp, grind =]
theorem containsThenInsert_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsert k v).2 = t.insert k v :=
  ext <| Impl.containsThenInsert!_snd h

@[simp, grind =]
theorem containsThenInsertIfNew_fst [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).1 = t.contains k :=
  Impl.containsThenInsertIfNew!_fst h

@[simp, grind =]
theorem containsThenInsertIfNew_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.containsThenInsertIfNew k v).2 = t.insertIfNew k v :=
  ext <| Impl.containsThenInsertIfNew!_snd h

@[simp, grind =]
theorem get?_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} :
    (∅ : DTreeMap α β cmp).get? a = none :=
  Impl.get?_empty

theorem get?_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t.get? a = none :=
  Impl.get?_of_isEmpty h

@[grind =] theorem get?_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a k : α} {v : β k} :
    (t.insert k v).get? a =
      if h : cmp k a = .eq then some (cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h)) v) else t.get? a :=
  Impl.get?_insert! h

@[simp]
theorem get?_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).get? k = some v :=
  Impl.get?_insert!_self h

theorem contains_eq_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (t.get? a).isSome :=
  Impl.contains_eq_isSome_get? h

@[simp, grind =]
theorem isSome_get?_eq_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    (t.get? a).isSome = t.contains a :=
  (contains_eq_isSome_get? h).symm

theorem mem_iff_isSome_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.get? a).isSome :=
  Impl.mem_iff_isSome_get? h

@[simp]
theorem isSome_get?_iff_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    (t.get? a).isSome ↔ a ∈ t :=
  (mem_iff_isSome_get? h).symm

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t.get? a = none :=
  Impl.get?_eq_none_of_contains_eq_false h

theorem get?_eq_none [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.get? a = none :=
  Impl.get?_eq_none h

@[grind =] theorem get?_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).get? a = if cmp k a = .eq then none else t.get? a :=
  Impl.get?_erase! h

@[simp]
theorem get?_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).get? k = none :=
  Impl.get?_erase!_self h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp, grind =]
theorem get?_emptyc [TransCmp cmp] {a : α} :
    get? (∅ : Raw α β cmp) a = none :=
  Impl.Const.get?_empty

theorem get?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → get? t a = none :=
  Impl.Const.get?_of_isEmpty h

@[grind =] theorem get?_insert [TransCmp cmp] (h : t.WF) {a k : α} {v : β} :
    get? (t.insert k v) a =
      if cmp k a = .eq then some v else get? t a :=
  Impl.Const.get?_insert! h

@[simp]
theorem get?_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    get? (t.insert k v) k = some v :=
  Impl.Const.get?_insert!_self h

theorem contains_eq_isSome_get? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (get? t a).isSome :=
  Impl.Const.contains_eq_isSome_get? h

@[simp, grind =]
theorem isSome_get?_eq_contains [TransCmp cmp] (h : t.WF) {a : α} :
    (get? t a).isSome = t.contains a :=
  (contains_eq_isSome_get? h).symm

theorem mem_iff_isSome_get? [TransCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (get? t a).isSome :=
  Impl.Const.mem_iff_isSome_get? h

@[simp]
theorem isSome_get?_iff_mem [TransCmp cmp] (h : t.WF) {a : α} :
    (get? t a).isSome ↔ a ∈ t :=
  (mem_iff_isSome_get? h).symm

theorem get?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → get? t a = none :=
  Impl.Const.get?_eq_none_of_contains_eq_false h

theorem get?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → get? t a = none :=
  Impl.Const.get?_eq_none h

@[grind =] theorem get?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    get? (t.erase k) a = if cmp k a = .eq then none else get? t a :=
  Impl.Const.get?_erase! h

@[simp]
theorem get?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    get? (t.erase k) k = none :=
  Impl.Const.get?_erase!_self h

theorem get?_eq_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} : get? t a = t.get? a :=
  Impl.Const.get?_eq_get? h

theorem get?_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) :
    get? t a = get? t b :=
  Impl.Const.get?_congr h hab

end Const

@[grind =] theorem get_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert k v).get a h₁ =
      if h₂ : cmp k a = .eq then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h₂)) v
      else
        t.get a (mem_of_mem_insert h h₁ h₂) :=
  Impl.get_insert! h

@[simp]
theorem get_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).get k (mem_insert_self h) = v :=
  Impl.get_insert!_self h

@[simp, grind =]
theorem get_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k).get a h' = t.get a (mem_of_mem_erase h h') :=
  Impl.get_erase! h

theorem get?_eq_some_get [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {h'} :
    t.get? a = some (t.get a h') :=
  Impl.get?_eq_some_get h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[grind =] theorem get_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insert k v) a h₁ =
      if h₂ : cmp k a = .eq then v
      else get t a (mem_of_mem_insert h h₁ h₂) :=
  Impl.Const.get_insert! h

@[simp]
theorem get_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    get (t.insert k v) k (mem_insert_self h) = v :=
  Impl.Const.get_insert!_self h

@[simp, grind =]
theorem get_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    get (t.erase k) a h' = get t a (mem_of_mem_erase h h') :=
  Impl.Const.get_erase! h

theorem get?_eq_some_get [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    get? t a = some (get t a h') :=
  Impl.Const.get?_eq_some_get h

theorem get_eq_get [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {h'} :
    get t a h' = t.get a h' :=
  Impl.Const.get_eq_get h

theorem get_congr [TransCmp cmp] (h : t.WF) {a b : α} (hab : cmp a b = .eq) {h'} :
    get t a h' = get t b ((mem_congr h hab).mp h') :=
  Impl.Const.get_congr h hab

end Const

@[simp, grind =]
theorem get!_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} [Inhabited (β a)] :
    get! (∅ : Raw α β cmp) a = default :=
  Impl.get!_empty

theorem get!_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.isEmpty = true → t.get! a = default :=
  Impl.get!_of_isEmpty h

@[grind =] theorem get!_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} [Inhabited (β a)]
    {v : β k} : (t.insert k v).get! a =
      if h : cmp k a = .eq then cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h)) v else t.get! a :=
  Impl.get!_insert! h

@[simp]
theorem get!_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)]
    {b : β a} : (t.insert a b).get! a = b :=
  Impl.get!_insert!_self h

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    [Inhabited (β a)] : t.contains a = false → t.get! a = default :=
  Impl.get!_eq_default_of_contains_eq_false h

theorem get!_eq_default [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    ¬ a ∈ t → t.get! a = default :=
  Impl.get!_eq_default h

@[grind =] theorem get!_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} [Inhabited (β a)] :
    (t.erase k).get! a = if cmp k a = .eq then default else t.get! a :=
  Impl.get!_erase! h

@[simp]
theorem get!_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} [Inhabited (β k)] :
    (t.erase k).get! k = default :=
  Impl.get!_erase!_self h

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    [Inhabited (β a)] : t.contains a = true → t.get? a = some (t.get! a) :=
  Impl.get?_eq_some_get!_of_contains h

theorem get?_eq_some_get! [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    a ∈ t → t.get? a = some (t.get! a) :=
  Impl.get?_eq_some_get! h

theorem get!_eq_get!_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = (t.get? a).get! :=
  Impl.get!_eq_get!_get? h

theorem get_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] {h'} :
    t.get a h' = t.get! a :=
  Impl.get_eq_get! h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp, grind =]
theorem get!_emptyc [TransCmp cmp] [Inhabited β] {a : α} :
    get! (∅ : Raw α β cmp) a = default :=
  Impl.Const.get!_empty

theorem get!_of_isEmpty [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.isEmpty = true → get! t a = default :=
  Impl.Const.get!_of_isEmpty h

@[grind =] theorem get!_insert [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insert k v) a = if cmp k a = .eq then v else get! t a :=
  Impl.Const.get!_insert! h

@[simp]
theorem get!_insert_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α} {v : β} :
    get! (t.insert k v) k = v :=
  Impl.Const.get!_insert!_self h

theorem get!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = false → get! t a = default :=
  Impl.Const.get!_eq_default_of_contains_eq_false h

theorem get!_eq_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    ¬ a ∈ t → get! t a = default :=
  Impl.Const.get!_eq_default h

@[grind =] theorem get!_erase [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} :
    get! (t.erase k) a = if cmp k a = .eq then default else get! t a :=
  Impl.Const.get!_erase! h

@[simp]
theorem get!_erase_self [TransCmp cmp] [Inhabited β] (h : t.WF) {k : α} :
    get! (t.erase k) k = default :=
  Impl.Const.get!_erase!_self h

theorem get?_eq_some_get!_of_contains [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    t.contains a = true → get? t a = some (get! t a) :=
  Impl.Const.get?_eq_some_get! h

theorem get?_eq_some_get! [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    a ∈ t → get? t a = some (get! t a) :=
  Impl.Const.get?_eq_some_get! h

theorem get!_eq_get!_get? [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = (get? t a).get! :=
  Impl.Const.get!_eq_get!_get? h

theorem get_eq_get! [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} {h'} :
    get t a h' = get! t a :=
  Impl.Const.get_eq_get! h

theorem get!_eq_get! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = t.get! a :=
  Impl.Const.get!_eq_get! h

theorem get!_congr [TransCmp cmp] [Inhabited β] (h : t.WF) {a b : α} (hab : cmp a b = .eq) :
    get! t a = get! t b :=
  Impl.Const.get!_congr h hab

end Const

@[simp, grind =]
theorem getD_emptyc [TransCmp cmp] [LawfulEqCmp cmp] {a : α} {fallback : β a} :
    (∅ : DTreeMap α β cmp).getD a fallback = fallback :=
  Impl.getD_empty

theorem getD_of_isEmpty [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.isEmpty = true → t.getD a fallback = fallback :=
  Impl.getD_of_isEmpty h

@[grind =] theorem getD_insert [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insert k v).getD a fallback =
      if h : cmp k a = .eq then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h)) v
      else t.getD a fallback :=
  Impl.getD_insert! h

@[simp]
theorem getD_insert_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback b : β a} :
    (t.insert a b).getD a fallback = b :=
  Impl.getD_insert!_self h

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.contains a = false → t.getD a fallback = fallback :=
  Impl.getD_eq_fallback_of_contains_eq_false h

theorem getD_eq_fallback [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    ¬ a ∈ t → t.getD a fallback = fallback :=
  Impl.getD_eq_fallback h

@[grind =] theorem getD_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {fallback : β a} :
    (t.erase k).getD a fallback = if cmp k a = .eq then fallback else t.getD a fallback :=
  Impl.getD_erase! h

@[simp]
theorem getD_erase_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {fallback : β k} :
    (t.erase k).getD k fallback = fallback :=
  Impl.getD_erase!_self h

theorem get?_eq_some_getD_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α}
    {fallback : β a} : t.contains a = true → t.get? a = some (t.getD a fallback) :=
  Impl.get?_eq_some_getD_of_contains h

theorem get?_eq_some_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    a ∈ t → t.get? a = some (t.getD a fallback) :=
  Impl.get?_eq_some_getD h

theorem getD_eq_getD_get? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} :
    t.getD a fallback = (t.get? a).getD fallback :=
  Impl.getD_eq_getD_get? h

theorem get_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β a} {h'} :
    t.get a h' = t.getD a fallback :=
  Impl.get_eq_getD h

theorem get!_eq_getD_default [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} [Inhabited (β a)] :
    t.get! a = t.getD a default :=
  Impl.get!_eq_getD_default h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp, grind =]
theorem getD_emptyc [TransCmp cmp] {a : α} {fallback : β} :
    getD (∅ : Raw α β cmp) a fallback = fallback :=
  Impl.Const.getD_empty

theorem getD_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.isEmpty = true → getD t a fallback = fallback :=
  Impl.Const.getD_of_isEmpty h

@[grind =] theorem getD_insert [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insert k v) a fallback = if cmp k a = .eq then v else getD t a fallback :=
  Impl.Const.getD_insert! h

@[simp]
theorem getD_insert_self [TransCmp cmp] (h : t.WF) {k : α} {fallback v : β} :
    getD (t.insert k v) k fallback = v :=
  Impl.Const.getD_insert!_self h

theorem getD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = false → getD t a fallback = fallback :=
  Impl.Const.getD_eq_fallback_of_contains_eq_false h

theorem getD_eq_fallback [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    ¬ a ∈ t → getD t a fallback = fallback :=
  Impl.Const.getD_eq_fallback h

@[grind =] theorem getD_erase [TransCmp cmp] (h : t.WF) {k a : α} {fallback : β} :
    getD (t.erase k) a fallback = if cmp k a = .eq then
      fallback
    else
      getD t a fallback :=
  Impl.Const.getD_erase! h

@[simp]
theorem getD_erase_self [TransCmp cmp] (h : t.WF) {k : α} {fallback : β} :
    getD (t.erase k) k fallback = fallback :=
  Impl.Const.getD_erase!_self h

theorem get?_eq_some_getD_of_contains [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    t.contains a = true → get? t a = some (getD t a fallback) :=
  Impl.Const.get?_eq_some_getD_of_contains h

theorem get?_eq_some_getD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    a ∈ t → get? t a = some (getD t a fallback) :=
  Impl.Const.get?_eq_some_getD h

theorem getD_eq_getD_get? [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = (get? t a).getD fallback :=
  Impl.Const.getD_eq_getD_get? h

theorem get_eq_getD [TransCmp cmp] (h : t.WF) {a : α} {fallback : β} {h'} :
    get t a h' = getD t a fallback :=
  Impl.Const.get_eq_getD h

theorem get!_eq_getD_default [TransCmp cmp] [Inhabited β] (h : t.WF) {a : α} :
    get! t a = getD t a default :=
  Impl.Const.get!_eq_getD_default h

theorem getD_eq_getD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {a : α} {fallback : β} :
    getD t a fallback = t.getD a fallback :=
  Impl.Const.getD_eq_getD h

theorem getD_congr [TransCmp cmp] (h : t.WF) {a b : α} {fallback : β} (hab : cmp a b = .eq) :
    getD t a fallback = getD t b fallback :=
  Impl.Const.getD_congr h hab

end Const

@[simp, grind =]
theorem getKey?_emptyc {a : α} : (∅ : DTreeMap α β cmp).getKey? a = none :=
  Impl.getKey?_empty

theorem getKey?_of_isEmpty [TransCmp cmp] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey? a = none :=
  Impl.getKey?_of_isEmpty h

@[grind =] theorem getKey?_insert [TransCmp cmp] (h : t.WF) {a k : α} {v : β k} :
    (t.insert k v).getKey? a = if cmp k a = .eq then some k else t.getKey? a :=
  Impl.getKey?_insert! h

@[simp]
theorem getKey?_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).getKey? k = some k :=
  Impl.getKey?_insert!_self h

theorem contains_eq_isSome_getKey? [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = (t.getKey? a).isSome :=
  Impl.contains_eq_isSome_getKey? h

@[simp, grind =]
theorem isSome_getKey?_eq_contains [TransCmp cmp] (h : t.WF) {a : α} :
    (t.getKey? a).isSome = t.contains a :=
  (contains_eq_isSome_getKey? h).symm

theorem mem_iff_isSome_getKey? [TransCmp cmp] (h : t.WF) {a : α} :
    a ∈ t ↔ (t.getKey? a).isSome :=
  Impl.mem_iff_isSome_getKey? h

@[simp]
theorem isSome_getKey?_iff_mem [TransCmp cmp] (h : t.WF) {a : α} :
    (t.getKey? a).isSome ↔ a ∈ t :=
  (mem_iff_isSome_getKey? h).symm

theorem getKey?_eq_none_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey? a = none :=
  Impl.getKey?_eq_none_of_contains_eq_false h

theorem getKey?_eq_none [TransCmp cmp] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey? a = none :=
  Impl.getKey?_eq_none h

@[grind =] theorem getKey?_erase [TransCmp cmp] (h : t.WF) {k a : α} :
    (t.erase k).getKey? a = if cmp k a = .eq then none else t.getKey? a :=
  Impl.getKey?_erase! h

@[simp]
theorem getKey?_erase_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.erase k).getKey? k = none :=
  Impl.getKey?_erase!_self h

theorem compare_getKey?_self [TransCmp cmp] (h : t.WF) {k : α} :
    (t.getKey? k).all (cmp · k = .eq) :=
  Impl.compare_getKey?_self h

theorem getKey?_congr [TransCmp cmp] (h : t.WF) {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey? k = t.getKey? k' :=
  Impl.getKey?_congr h h'

theorem getKey?_eq_some_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    (h' : t.contains k) :
    t.getKey? k = some k :=
  Impl.getKey?_eq_some_of_contains h h'

theorem getKey?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} (h' : k ∈ t) :
    t.getKey? k = some k :=
  Impl.getKey?_eq_some_of_contains h h'

@[grind =] theorem getKey_insert [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insert k v).getKey a h₁ =
      if h₂ : cmp k a = .eq then
        k
      else
        t.getKey a (mem_of_mem_insert h h₁ h₂) :=
  Impl.getKey_insert! h

@[simp]
theorem getKey_insert_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insert k v).getKey k (mem_insert_self h) = k :=
  Impl.getKey_insert!_self h

@[simp, grind =]
theorem getKey_erase [TransCmp cmp] (h : t.WF) {k a : α} {h'} :
    (t.erase k).getKey a h' = t.getKey a (mem_of_mem_erase h h') :=
  Impl.getKey_erase! h

theorem getKey?_eq_some_getKey [TransCmp cmp] (h : t.WF) {a : α} {h'} :
    t.getKey? a = some (t.getKey a h') :=
  Impl.getKey?_eq_some_getKey h

theorem compare_getKey_self [TransCmp cmp] (h : t.WF) {k : α} (h' : k ∈ t) :
    cmp (t.getKey k h') k = .eq :=
  Impl.compare_getKey_self h h'

theorem getKey_congr [TransCmp cmp] (h : t.WF) {k₁ k₂ : α} (h' : cmp k₁ k₂ = .eq)
    (h₁ : k₁ ∈ t) : t.getKey k₁ h₁ = t.getKey k₂ ((mem_congr h h').mp h₁) :=
  Impl.getKey_congr h h' h₁

@[simp, grind =]
theorem getKey_eq [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} (h' : k ∈ t) :
    t.getKey k h' = k :=
  Impl.getKey_eq h h'

@[simp, grind =]
theorem getKey!_emptyc {a : α} [Inhabited α] :
    (∅ : DTreeMap α β cmp).getKey! a = default :=
  Impl.getKey!_empty

theorem getKey!_of_isEmpty [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.isEmpty = true → t.getKey! a = default :=
  Impl.getKey!_of_isEmpty h

@[grind =] theorem getKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} {v : β k} :
    (t.insert k v).getKey! a = if cmp k a = .eq then k else t.getKey! a :=
  Impl.getKey!_insert! h

@[simp]
theorem getKey!_insert_self [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} {b : β a} :
    (t.insert a b).getKey! a = a :=
  Impl.getKey!_insert!_self h

theorem getKey!_eq_default_of_contains_eq_false [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = false → t.getKey! a = default :=
  Impl.getKey!_eq_default_of_contains_eq_false h

theorem getKey!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    ¬ a ∈ t → t.getKey! a = default :=
  Impl.getKey!_eq_default h

@[grind =] theorem getKey!_erase [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α} :
    (t.erase k).getKey! a = if cmp k a = .eq then default else t.getKey! a :=
  Impl.getKey!_erase! h

@[simp]
theorem getKey!_erase_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k : α} :
    (t.erase k).getKey! k = default :=
  Impl.getKey!_erase!_self h

theorem getKey?_eq_some_getKey!_of_contains [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.contains a = true → t.getKey? a = some (t.getKey! a) :=
  Impl.getKey?_eq_some_getKey!_of_contains h

theorem getKey?_eq_some_getKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    a ∈ t → t.getKey? a = some (t.getKey! a) :=
  Impl.getKey?_eq_some_getKey! h

theorem getKey!_eq_get!_getKey? [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.getKey! a = (t.getKey? a).get! :=
  Impl.getKey!_eq_get!_getKey? h

theorem getKey_eq_getKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} {h'} :
    t.getKey a h' = t.getKey! a :=
  Impl.getKey_eq_getKey! h

theorem getKey!_congr [TransCmp cmp] [Inhabited α] (h : t.WF) {k k' : α} (h' : cmp k k' = .eq) :
    t.getKey! k = t.getKey! k' :=
  Impl.getKey!_congr h h'

theorem getKey!_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k : α}
    (h' : t.contains k) :
    t.getKey! k = k :=
  Impl.getKey!_eq_of_contains h h'

theorem getKey!_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k : α}
    (h' : k ∈ t) :
    t.getKey! k = k :=
  Impl.getKey!_eq_of_mem h h'

@[simp, grind =]
theorem getKeyD_emptyc {a : α} {fallback : α} :
    (∅ : DTreeMap α β cmp).getKeyD a fallback = fallback :=
  Impl.getKeyD_empty

theorem getKeyD_of_isEmpty [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.isEmpty = true → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_of_isEmpty h

@[grind =] theorem getKeyD_insert [TransCmp cmp] (h : t.WF) {k a fallback : α} {v : β k} :
    (t.insert k v).getKeyD a fallback = if cmp k a = .eq then k else t.getKeyD a fallback :=
  Impl.getKeyD_insert! h

@[simp]
theorem getKeyD_insert_self [TransCmp cmp] (h : t.WF) {a fallback : α} {b : β a} :
    (t.insert a b).getKeyD a fallback = a :=
  Impl.getKeyD_insert!_self h

theorem getKeyD_eq_fallback_of_contains_eq_false [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.contains a = false → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_eq_fallback_of_contains_eq_false h

theorem getKeyD_eq_fallback [TransCmp cmp] (h : t.WF) {a fallback : α} :
    ¬ a ∈ t → t.getKeyD a fallback = fallback :=
  Impl.getKeyD_eq_fallback h

@[grind =] theorem getKeyD_erase [TransCmp cmp] (h : t.WF) {k a fallback : α} :
    (t.erase k).getKeyD a fallback =
      if cmp k a = .eq then fallback else t.getKeyD a fallback :=
  Impl.getKeyD_erase! h

@[simp]
theorem getKeyD_erase_self [TransCmp cmp] (h : t.WF) {k fallback : α} :
    (t.erase k).getKeyD k fallback = fallback :=
  Impl.getKeyD_erase!_self h

theorem getKey?_eq_some_getKeyD_of_contains [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.contains a = true → t.getKey? a = some (t.getKeyD a fallback) :=
  Impl.getKey?_eq_some_getKeyD_of_contains h

theorem getKey?_eq_some_getKeyD [TransCmp cmp] (h : t.WF) {a fallback : α} :
    a ∈ t → t.getKey? a = some (t.getKeyD a fallback) :=
  Impl.getKey?_eq_some_getKeyD h

theorem getKeyD_eq_getD_getKey? [TransCmp cmp] (h : t.WF) {a fallback : α} :
    t.getKeyD a fallback = (t.getKey? a).getD fallback :=
  Impl.getKeyD_eq_getD_getKey? h

theorem getKey_eq_getKeyD [TransCmp cmp] (h : t.WF) {a fallback : α} {h'} :
    t.getKey a h' = t.getKeyD a fallback :=
  Impl.getKey_eq_getKeyD h

theorem getKey!_eq_getKeyD_default [TransCmp cmp] [Inhabited α] (h : t.WF) {a : α} :
    t.getKey! a = t.getKeyD a default :=
  Impl.getKey!_eq_getKeyD_default h

theorem getKeyD_congr [TransCmp cmp] (h : t.WF) {k k' fallback : α} (h' : cmp k k' = .eq) :
    t.getKeyD k fallback = t.getKeyD k' fallback :=
  Impl.getKeyD_congr h h'

theorem getKeyD_eq_of_contains [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k fallback : α}
    (h' : t.contains k) :
    t.getKeyD k fallback = k :=
  Impl.getKeyD_eq_of_contains h h'

theorem getKeyD_eq_of_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k fallback : α}
    (h' : k ∈ t) :
    t.getKeyD k fallback = k :=
  Impl.getKeyD_eq_of_contains h h'

@[simp, grind =]
theorem isEmpty_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).isEmpty = false :=
  Impl.isEmpty_insertIfNew! h

@[simp, grind =]
theorem contains_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a = (cmp k a == .eq || t.contains a) :=
  Impl.contains_insertIfNew! h

@[simp, grind =]
theorem mem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v ↔ cmp k a = .eq ∨ a ∈ t :=
  Impl.mem_insertIfNew! h

theorem contains_insertIfNew_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).contains k :=
  Impl.contains_insertIfNew!_self h

theorem mem_insertIfNew_self [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    k ∈ t.insertIfNew k v :=
  Impl.mem_insertIfNew!_self h

theorem contains_of_contains_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).contains a → cmp k a ≠ .eq → t.contains a :=
  Impl.contains_of_contains_insertIfNew! h

theorem mem_of_mem_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v → cmp k a ≠ .eq → a ∈ t :=
  Impl.contains_of_contains_insertIfNew! h

/-- This is a restatement of `mem_of_mem_insertIfNew` that is written to exactly match the
proof obligation in the statement of `get_insertIfNew`. -/
theorem mem_of_mem_insertIfNew' [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    a ∈ t.insertIfNew k v → ¬ (cmp k a = .eq ∧ ¬ k ∈ t) → a ∈ t :=
  Impl.mem_of_mem_insertIfNew!' h

@[grind =] theorem size_insertIfNew [TransCmp cmp] {k : α} (h : t.WF) {v : β k} :
    (t.insertIfNew k v).size = if k ∈ t then t.size else t.size + 1 :=
  Impl.size_insertIfNew! h

theorem size_le_size_insertIfNew [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    t.size ≤ (t.insertIfNew k v).size :=
  Impl.size_le_size_insertIfNew! h

theorem size_insertIfNew_le [TransCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.insertIfNew k v).size ≤ t.size + 1 :=
  Impl.size_insertIfNew!_le h

@[grind =] theorem get?_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).get? a =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        some (cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h.1)) v)
      else
        t.get? a :=
  Impl.get?_insertIfNew! h

@[grind =] theorem get_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v).get a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h₂.1)) v
      else
        t.get a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  Impl.get_insertIfNew! h

@[grind =] theorem get!_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} [Inhabited (β a)] {v : β k} :
    (t.insertIfNew k v).get! a =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h.1)) v
      else
        t.get! a :=
  Impl.get!_insertIfNew! h

@[grind =] theorem getD_insertIfNew [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k a : α} {fallback : β a} {v : β k} :
    (t.insertIfNew k v).getD a fallback =
      if h : cmp k a = .eq ∧ ¬ k ∈ t then
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp h.1)) v
      else
        t.getD a fallback :=
  Impl.getD_insertIfNew! h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[grind =] theorem get?_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} :
    get? (t.insertIfNew k v) a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some v else get? t a :=
  Impl.Const.get?_insertIfNew! h

@[grind =] theorem get_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β} {h₁} :
    get (t.insertIfNew k v) a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then
        v
      else
        get t a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  Impl.Const.get_insertIfNew! h

@[grind =] theorem get!_insertIfNew [TransCmp cmp] [Inhabited β] (h : t.WF) {k a : α} {v : β} :
    get! (t.insertIfNew k v) a =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else get! t a :=
  Impl.Const.get!_insertIfNew! h

@[grind =] theorem getD_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {fallback v : β} :
    getD (t.insertIfNew k v) a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then v else getD t a fallback :=
  Impl.Const.getD_insertIfNew! h

end Const

@[grind =] theorem getKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} :
    (t.insertIfNew k v).getKey? a =
      if cmp k a = .eq ∧ ¬ k ∈ t then some k else t.getKey? a :=
  Impl.getKey?_insertIfNew! h

@[grind =] theorem getKey_insertIfNew [TransCmp cmp] (h : t.WF) {k a : α} {v : β k} {h₁} :
    (t.insertIfNew k v).getKey a h₁ =
      if h₂ : cmp k a = .eq ∧ ¬ k ∈ t then k
      else t.getKey a (mem_of_mem_insertIfNew' h h₁ h₂) :=
  Impl.getKey_insertIfNew! h

@[grind =] theorem getKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF) {k a : α}
    {v : β k} :
    (t.insertIfNew k v).getKey! a =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKey! a :=
  Impl.getKey!_insertIfNew! h

@[grind =] theorem getKeyD_insertIfNew [TransCmp cmp] (h : t.WF) {k a fallback : α}
    {v : β k} :
    (t.insertIfNew k v).getKeyD a fallback =
      if cmp k a = .eq ∧ ¬ k ∈ t then k else t.getKeyD a fallback :=
  Impl.getKeyD_insertIfNew! h

@[simp, grind =]
theorem getThenInsertIfNew?_fst [TransCmp cmp] [LawfulEqCmp cmp] (_ : t.WF) {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v).1 = t.get? k :=
  Impl.getThenInsertIfNew?!_fst

@[simp, grind =]
theorem getThenInsertIfNew?_snd [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    (t.getThenInsertIfNew? k v).2 = t.insertIfNew k v :=
  ext <| Impl.getThenInsertIfNew?!_snd h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp, grind =]
theorem getThenInsertIfNew?_fst [TransCmp cmp] (_ : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v).1 = get? t k :=
  Impl.Const.getThenInsertIfNew?!_fst

@[simp, grind =]
theorem getThenInsertIfNew?_snd [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (getThenInsertIfNew? t k v).2 = t.insertIfNew k v :=
  ext <| Impl.Const.getThenInsertIfNew?!_snd h

end Const

@[simp, grind =]
theorem length_keys [TransCmp cmp] (h : t.WF) :
    t.keys.length = t.size :=
  Impl.length_keys h.out

@[simp, grind =]
theorem isEmpty_keys :
    t.keys.isEmpty = t.isEmpty :=
  Impl.isEmpty_keys

@[simp, grind =]
theorem contains_keys [BEq α] [LawfulBEqCmp cmp] (h : t.WF) [TransCmp cmp] {k : α} :
    t.keys.contains k = t.contains k :=
  Impl.contains_keys h

@[simp, grind =]
theorem mem_keys [LawfulEqCmp cmp] [TransCmp cmp] (h : t.WF) {k : α} :
    k ∈ t.keys ↔ k ∈ t :=
  Impl.mem_keys h

theorem distinct_keys [TransCmp cmp] (h : t.WF) :
    t.keys.Pairwise (fun a b => ¬ cmp a b = .eq) :=
  Impl.distinct_keys h.out

theorem ordered_keys [TransCmp cmp] (h : t.WF) :
    t.keys.Pairwise (fun a b => cmp a b = .lt) :=
  Impl.ordered_keys h.out

@[simp, grind _=_]
theorem map_fst_toList_eq_keys :
    t.toList.map Sigma.fst = t.keys :=
  Impl.map_fst_toList_eq_keys

@[simp, grind =]
theorem length_toList [TransCmp cmp] (h : t.WF) :
    t.toList.length = t.size :=
  Impl.length_toList h.out

@[simp, grind =]
theorem isEmpty_toList :
    t.toList.isEmpty = t.isEmpty :=
  Impl.isEmpty_toList

@[simp, grind =]
theorem mem_toList_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β k} :
    ⟨k, v⟩ ∈ t.toList ↔ t.get? k = some v :=
  Impl.mem_toList_iff_get?_eq_some h.out

theorem find?_toList_eq_some_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {v : β k} : t.toList.find? (cmp ·.1 k == .eq) = some ⟨k, v⟩ ↔ t.get? k = some v :=
  Impl.find?_toList_eq_some_iff_get?_eq_some h.out

theorem find?_toList_eq_none_iff_contains_eq_false [TransCmp cmp] (h : t.WF) {k : α} :
    t.toList.find? (cmp ·.1 k == .eq) = none ↔ t.contains k = false :=
  Impl.find?_toList_eq_none_iff_contains_eq_false h.out

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransCmp cmp] (h : t.WF) {k : α} :
    t.toList.find? (cmp ·.1 k == .eq) = none ↔ ¬ k ∈ t := by
  simpa only [Bool.not_eq_true, mem_iff_contains] using find?_toList_eq_none_iff_contains_eq_false h

theorem distinct_keys_toList [TransCmp cmp] (h : t.WF) :
    t.toList.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) :=
  Impl.distinct_keys_toList h.out

theorem ordered_keys_toList [TransCmp cmp] (h : t.WF) :
    t.toList.Pairwise (fun a b => cmp a.1 b.1 = .lt) :=
  Impl.ordered_keys_toList h.out

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp, grind _=_]
theorem map_fst_toList_eq_keys :
    (toList t).map Prod.fst = t.keys :=
  Impl.Const.map_fst_toList_eq_keys

@[simp, grind =]
theorem length_toList (h : t.WF) :
    (toList t).length = t.size :=
  Impl.Const.length_toList h.out

@[simp, grind =]
theorem isEmpty_toList :
    (toList t).isEmpty = t.isEmpty :=
  Impl.Const.isEmpty_toList

@[simp, grind =]
theorem mem_toList_iff_get?_eq_some [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {v : β} :
    (k, v) ∈ toList t ↔ get? t k = some v :=
  Impl.Const.mem_toList_iff_get?_eq_some h

@[simp]
theorem mem_toList_iff_getKey?_eq_some_and_get?_eq_some [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    (k, v) ∈ toList t ↔ t.getKey? k = some k ∧ get? t k = some v :=
  Impl.Const.mem_toList_iff_getKey?_eq_some_and_get?_eq_some h

theorem get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList [TransCmp cmp] (h : t.WF) {k : α} {v : β} :
    get? t k = some v ↔ ∃ (k' : α), cmp k k' = .eq ∧ (k', v) ∈ toList t :=
  Impl.Const.get?_eq_some_iff_exists_compare_eq_eq_and_mem_toList h

theorem find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some [TransCmp cmp] (h : t.WF)
    {k k' : α} {v : β} :
    (toList t).find? (fun a => cmp a.1 k = .eq) = some ⟨k', v⟩ ↔
      t.getKey? k = some k' ∧ get? t k = some v :=
  Impl.Const.find?_toList_eq_some_iff_getKey?_eq_some_and_get?_eq_some h.out

theorem find?_toList_eq_none_iff_contains_eq_false [TransCmp cmp] (h : t.WF) {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ t.contains k = false :=
  Impl.Const.find?_toList_eq_none_iff_contains_eq_false h.out

@[simp]
theorem find?_toList_eq_none_iff_not_mem [TransCmp cmp] (h : t.WF) {k : α} :
    (toList t).find? (cmp ·.1 k == .eq) = none ↔ ¬ k ∈ t :=
  Impl.Const.find?_toList_eq_none_iff_not_mem h.out

theorem distinct_keys_toList [TransCmp cmp] (h : t.WF) :
    (toList t).Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq) :=
  Impl.Const.distinct_keys_toList h.out

theorem ordered_keys_toList [TransCmp cmp] (h : t.WF) :
    (toList t).Pairwise (fun a b => cmp a.1 b.1 = .lt) :=
  Impl.Const.ordered_keys_toList h.out

end Const

section monadic

variable {δ : Type w} {m : Type w → Type w'}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m] {f : δ → (a : α) → β a → m δ} {init : δ} :
    t.foldlM f init = t.toList.foldlM (fun a b => f a b.1 b.2) init :=
  Impl.foldlM_eq_foldlM_toList

theorem foldl_eq_foldl_toList {f : δ → (a : α) → β a → δ} {init : δ} :
    t.foldl f init = t.toList.foldl (fun a b => f a b.1 b.2) init :=
  Impl.foldl_eq_foldl_toList

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m] {f : (a : α) → β a → δ → m δ} {init : δ} :
    t.foldrM f init = t.toList.foldrM (fun a b => f a.1 a.2 b) init :=
  Impl.foldrM_eq_foldrM_toList

theorem foldr_eq_foldr_toList {f : (a : α) → β a → δ → δ} {init : δ} :
    t.foldr f init = t.toList.foldr (fun a b => f a.1 a.2 b) init :=
  Impl.foldr_eq_foldr_toList

@[simp, grind =]
theorem forM_eq_forM [Monad m] [LawfulMonad m] {f : (a : α) → β a → m PUnit} :
    t.forM f = ForM.forM t (fun a => f a.1 a.2) := rfl

theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {f : (a : α) × β a → m PUnit} :
    ForM.forM t f = ForM.forM t.toList f :=
  Impl.forM_eq_forM_toList

@[simp, grind =]
theorem forIn_eq_forIn [Monad m] [LawfulMonad m]
    {f : (a : α) → β a → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn t init (fun a b => f a.1 a.2 b) := rfl

theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m]
    {f : (a : α) × β a → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init f = ForIn.forIn t.toList init f :=
  Impl.forIn_eq_forIn_toList (f := f)

theorem foldlM_eq_foldlM_keys [Monad m] [LawfulMonad m] {f : δ → α → m δ} {init : δ} :
    t.foldlM (fun d a _ => f d a) init = t.keys.foldlM f init :=
  Impl.foldlM_eq_foldlM_keys

theorem foldl_eq_foldl_keys {f : δ → α → δ} {init : δ} :
    t.foldl (fun d a _ => f d a) init = t.keys.foldl f init :=
  Impl.foldl_eq_foldl_keys

theorem foldrM_eq_foldrM_keys [Monad m] [LawfulMonad m] {f : α → δ → m δ} {init : δ} :
    t.foldrM (fun a _ d => f a d) init = t.keys.foldrM f init :=
  Impl.foldrM_eq_foldrM_keys

theorem foldr_eq_foldr_keys {f : α → δ → δ} {init : δ} :
    t.foldr (fun a _ d => f a d) init = t.keys.foldr f init :=
  Impl.foldr_eq_foldr_keys

theorem forM_eq_forM_keys [Monad m] [LawfulMonad m] {f : α → m PUnit} :
    ForM.forM t (fun a => f a.1) = t.keys.forM f :=
  Impl.forM_eq_forM_keys

theorem forIn_eq_forIn_keys [Monad m] [LawfulMonad m]
    {f : α → δ → m (ForInStep δ)} {init : δ} :
    ForIn.forIn t init (fun a d => f a.1 d) = ForIn.forIn t.keys init f :=
  Impl.forIn_eq_forIn_keys

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem foldlM_eq_foldlM_toList [Monad m] [LawfulMonad m] {f : δ → α → β → m δ} {init : δ} :
    t.foldlM f init = (Const.toList t).foldlM (fun a b => f a b.1 b.2) init :=
  Impl.Const.foldlM_eq_foldlM_toList

theorem foldl_eq_foldl_toList {f : δ → α → β → δ} {init : δ} :
    t.foldl f init = (Const.toList t).foldl (fun a b => f a b.1 b.2) init :=
  Impl.Const.foldl_eq_foldl_toList

theorem foldrM_eq_foldrM_toList [Monad m] [LawfulMonad m] {f : α → β → δ → m δ} {init : δ} :
    t.foldrM f init = (Const.toList t).foldrM (fun a b => f a.1 a.2 b) init :=
  Impl.Const.foldrM_eq_foldrM_toList

theorem foldr_eq_foldr_toList {f : α → β → δ → δ} {init : δ} :
    t.foldr f init = (Const.toList t).foldr (fun a b => f a.1 a.2 b) init :=
  Impl.Const.foldr_eq_foldr_toList

theorem forM_eq_forMUncurried [Monad m] [LawfulMonad m] {f : α → β → m PUnit} :
    t.forM f = forMUncurried (fun a => f a.1 a.2) t := rfl

theorem forMUncurried_eq_forM_toList [Monad m] [LawfulMonad m] {f : α × β → m PUnit} :
    forMUncurried f t = (Const.toList t).forM f :=
  Impl.Const.forM_eq_forM_toList

/--
Deprecated, use `forMUncurried_eq_forM_toList` together with `forM_eq_forMUncurried` instead.
-/
@[deprecated forMUncurried_eq_forM_toList (since := "2025-03-02")]
theorem forM_eq_forM_toList [Monad m] [LawfulMonad m] {f : α → β → m PUnit} :
    t.forM f = (Const.toList t).forM (fun a => f a.1 a.2) :=
  Impl.Const.forM_eq_forM_toList

theorem forIn_eq_forInUncurried [Monad m] [LawfulMonad m]
    {f : α → β → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = forInUncurried (fun a b => f a.1 a.2 b) init t := rfl

theorem forInUncurried_eq_forIn_toList [Monad m] [LawfulMonad m]
    {f : α × β → δ → m (ForInStep δ)} {init : δ} :
    forInUncurried f init t = ForIn.forIn (Const.toList t) init f :=
  Impl.Const.forIn_eq_forIn_toList

/--
Deprecated, use `forInUncurried_eq_forIn_toList` together with `forIn_eq_forInUncurried` instead.
-/
@[deprecated forInUncurried_eq_forIn_toList (since := "2025-03-02")]
theorem forIn_eq_forIn_toList [Monad m] [LawfulMonad m]
    {f : α → β → δ → m (ForInStep δ)} {init : δ} :
    t.forIn f init = ForIn.forIn (Const.toList t) init (fun a b => f a.1 a.2 b) :=
  Impl.Const.forIn_eq_forIn_toList

end Const

end monadic

@[simp, grind =]
theorem insertMany_nil :
    t.insertMany [] = t :=
  rfl

@[simp, grind =]
theorem insertMany_list_singleton {k : α} {v : β k} :
    t.insertMany [⟨k, v⟩] = t.insert k v :=
  rfl

@[grind _=_]
theorem insertMany_cons {l : List ((a : α) × β a)} {k : α} {v : β k} :
    t.insertMany (⟨k, v⟩ :: l) = (t.insert k v).insertMany l :=
  ext <| Impl.insertMany!_cons

@[grind _=_]
theorem insertMany_append {l₁ l₂ : List ((a : α) × β a)} :
    insertMany t (l₁ ++ l₂) = insertMany (insertMany t l₁) l₂ := by
  induction l₁ generalizing t with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[simp, grind =]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    (t.insertMany l).contains k = (t.contains k || (l.map Sigma.fst).contains k) :=
  Impl.contains_insertMany!_list h

@[simp, grind =]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ t.insertMany l ↔ k ∈ t ∨ (l.map Sigma.fst).contains k :=
  Impl.mem_insertMany!_list h

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ t.insertMany l → (l.map Sigma.fst).contains k = false → k ∈ t :=
  Impl.mem_of_mem_insertMany!_list h

theorem get?_insertMany_list_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).get? k = t.get? k :=
  Impl.get?_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem get?_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).get? k' = some (cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v) :=
  Impl.get?_insertMany!_list_of_mem h k_eq distinct mem

theorem get_insertMany_list_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α}
    (contains : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany l).get k h' =
    t.get k (mem_of_mem_insertMany_list h h' contains) :=
  Impl.get_insertMany!_list_of_contains_eq_false h contains

theorem get_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h'} :
    (t.insertMany l).get k' h' = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v :=
  Impl.get_insertMany!_list_of_mem h k_eq distinct mem

theorem get!_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).get! k = t.get! k :=
  Impl.get!_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem get!_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).get! k' = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v :=
  Impl.get!_insertMany!_list_of_mem h k_eq distinct mem

theorem getD_insertMany_list_of_contains_eq_false [TransCmp cmp]
    [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getD k fallback = t.getD k fallback :=
  Impl.getD_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getD_insertMany_list_of_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (t.insertMany l).getD k' fallback = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v :=
  Impl.getD_insertMany!_list_of_mem h k_eq distinct mem

theorem getKey?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKey? k = t.getKey? k :=
  Impl.getKey?_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey?_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKey? k' = some k :=
  Impl.getKey?_insertMany!_list_of_mem h k_eq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false)
    {h'} :
    (t.insertMany l).getKey k h' =
    t.getKey k (mem_of_mem_insertMany_list h h' contains_eq_false) :=
  Impl.getKey_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (t.insertMany l).getKey k' h' = k :=
  Impl.getKey_insertMany!_list_of_mem h k_eq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] (h : t.WF) {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKey! k = t.getKey! k :=
  Impl.getKey!_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey!_insertMany_list_of_mem [TransCmp cmp] [Inhabited α] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKey! k' = k :=
  Impl.getKey!_insertMany!_list_of_mem h k_eq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (t.insertMany l).getKeyD k fallback = t.getKeyD k fallback :=
  Impl.getKeyD_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKeyD_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (t.insertMany l).getKeyD k' fallback = k :=
  Impl.getKeyD_insertMany!_list_of_mem h k_eq distinct mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (∀ (a : α), a ∈ t → (l.map Sigma.fst).contains a = false) →
    (t.insertMany l).size = t.size + l.length :=
  Impl.size_insertMany!_list h distinct

theorem size_le_size_insertMany_list [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} :
    t.size ≤ (t.insertMany l).size :=
  Impl.size_le_size_insertMany!_list h

grind_pattern size_le_size_insertMany_list => (t.insertMany l).size

theorem size_insertMany_list_le [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} :
    (t.insertMany l).size ≤ t.size + l.length :=
  Impl.size_insertMany!_list_le h

grind_pattern size_insertMany_list_le => (t.insertMany l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [TransCmp cmp] (h : t.WF)
    {l : List ((a : α) × β a)} :
    (t.insertMany l).isEmpty = (t.isEmpty && l.isEmpty) :=
  Impl.isEmpty_insertMany!_list h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp, grind =]
theorem insertMany_nil :
    insertMany t [] = t :=
  rfl

@[simp, grind =]
theorem insertMany_list_singleton {k : α} {v : β} :
    insertMany t [⟨k, v⟩] = t.insert k v :=
  rfl

@[grind _=_]
theorem insertMany_cons {l : List (α × β)} {k : α} {v : β} :
    Const.insertMany t ((k, v) :: l) = Const.insertMany (t.insert k v) l :=
  ext <| Impl.Const.insertMany!_cons

@[grind _=_]
theorem insertMany_append {l₁ l₂ : List (α × β)} :
    insertMany t (l₁ ++ l₂) = insertMany (insertMany t l₁) l₂ := by
  induction l₁ generalizing t with
  | nil => simp
  | cons hd tl ih =>
    rw [List.cons_append, insertMany_cons, insertMany_cons, ih]

@[simp, grind =]
theorem contains_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} :
    (Const.insertMany t l).contains k = (t.contains k || (l.map Prod.fst).contains k) :=
  Impl.Const.contains_insertMany!_list h

@[simp, grind =]
theorem mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} :
    k ∈ Const.insertMany t l ↔ k ∈ t ∨ (l.map Prod.fst).contains k :=
  Impl.Const.mem_insertMany!_list h

theorem mem_of_mem_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List ( α × β )} {k : α} :
    k ∈ insertMany t l → (l.map Prod.fst).contains k = false → k ∈ t :=
  Impl.Const.mem_of_mem_insertMany!_list h

theorem getKey?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKey? k = t.getKey? k :=
  Impl.Const.getKey?_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey?_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKey? k' = some k :=
  Impl.Const.getKey?_insertMany!_list_of_mem h k_eq distinct mem

theorem getKey_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    (insertMany t l).getKey k h' =
    t.getKey k (mem_of_mem_insertMany_list h h' contains_eq_false) :=
  Impl.Const.getKey_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (insertMany t l).getKey k' h' = k :=
  Impl.Const.getKey_insertMany!_list_of_mem h k_eq distinct mem

theorem getKey!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKey! k = t.getKey! k :=
  Impl.Const.getKey!_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKey!_insertMany_list_of_mem [TransCmp cmp] [Inhabited α] (h : t.WF)
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKey! k' = k :=
  Impl.Const.getKey!_insertMany!_list_of_mem h k_eq distinct mem

theorem getKeyD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (insertMany t l).getKeyD k fallback = t.getKeyD k fallback :=
  Impl.Const.getKeyD_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getKeyD_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (insertMany t l).getKeyD k' fallback = k :=
  Impl.Const.getKeyD_insertMany!_list_of_mem h k_eq distinct mem

theorem size_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (∀ (a : α), a ∈ t → (l.map Prod.fst).contains a = false) →
    (insertMany t l).size = t.size + l.length :=
  Impl.Const.size_insertMany!_list h distinct

theorem size_le_size_insertMany_list [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} :
    t.size ≤ (insertMany t l).size :=
  Impl.Const.size_le_size_insertMany!_list h

grind_pattern size_le_size_insertMany_list => (insertMany t l).size

theorem size_insertMany_list_le [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} :
    (insertMany t l).size ≤ t.size + l.length :=
  Impl.Const.size_insertMany!_list_le h

grind_pattern size_insertMany_list_le => (insertMany t l).size

@[simp, grind =]
theorem isEmpty_insertMany_list [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} :
    (insertMany t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  Impl.Const.isEmpty_insertMany!_list h

theorem get?_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (insertMany t l) k = get? t k :=
  Impl.Const.get?_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem get?_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    get? (insertMany t l) k' = some v :=
  Impl.Const.get?_insertMany!_list_of_mem h k_eq distinct mem

@[grind =] theorem get?_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} :
    get? (insertMany t l) k =
      (l.findSomeRev? (fun ⟨a, b⟩ => if cmp a k = .eq then some b else none)).or (get? t k) :=
  Impl.Const.get?_insertMany!_list h (k := k)

theorem get_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false)
    {h'} :
    get (insertMany t l) k h' = get t k (mem_of_mem_insertMany_list h h' contains_eq_false) :=
  Impl.Const.get_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem get_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) {h'} :
    get (insertMany t l) k' h' = v :=
  Impl.Const.get_insertMany!_list_of_mem h k_eq distinct mem

@[grind =] theorem get_insertMany_list [TransCmp cmp] [BEq α] [PartialEquivBEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} {h'} :
    get (insertMany t l) k h' =
      match w : l.findSomeRev? (fun ⟨a, b⟩ => if cmp a k = .eq then some b else none) with
      | some v => v
      | none => get t k (Impl.Const.contains_of_contains_insertMany_list' h (by simpa [Impl.Const.insertMany_eq_insertMany!] using h') w) :=
  Impl.Const.get_insertMany!_list h (k := k)

theorem get!_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited β] (h : t.WF) {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (insertMany t l) k = get! t k :=
  Impl.Const.get!_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem get!_insertMany_list_of_mem [TransCmp cmp] [Inhabited β] (h : t.WF)
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    get! (insertMany t l) k' = v :=
  Impl.Const.get!_insertMany!_list_of_mem h k_eq distinct mem

@[grind =] theorem get!_insertMany_list [TransCmp cmp] [Inhabited β] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} :
    get! (insertMany t l) k =
      (l.findSomeRev? (fun ⟨a, b⟩ => if cmp a k = .eq then some b else none)).getD (get! t k) :=
  Impl.Const.get!_insertMany!_list h (k := k)

theorem getD_insertMany_list_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    (h : t.WF) {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (insertMany t l) k fallback = getD t k fallback :=
  Impl.Const.getD_insertMany!_list_of_contains_eq_false h contains_eq_false

theorem getD_insertMany_list_of_mem [TransCmp cmp] (h : t.WF)
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) (mem : ⟨k, v⟩ ∈ l) :
    getD (insertMany t l) k' fallback = v :=
  Impl.Const.getD_insertMany!_list_of_mem h k_eq distinct mem

@[grind =] theorem getD_insertMany_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List (α × β)} {k : α} {fallback : β} :
    getD (insertMany t l) k fallback =
      (l.findSomeRev? (fun ⟨a, b⟩ => if cmp a k = .eq then some b else none)).getD (getD t k fallback) :=
  Impl.Const.getD_insertMany!_list h (k := k) fallback

variable {t : Raw α Unit cmp}

@[simp]
theorem insertManyIfNewUnit_nil :
    insertManyIfNewUnit t [] = t :=
  rfl

@[simp]
theorem insertManyIfNewUnit_list_singleton {k : α} :
    insertManyIfNewUnit t [k] = t.insertIfNew k () :=
  rfl

theorem insertManyIfNewUnit_cons {l : List α} {k : α} :
    insertManyIfNewUnit t (k :: l) = insertManyIfNewUnit (t.insertIfNew k ()) l :=
  ext <| Impl.Const.insertManyIfNewUnit!_cons

@[simp]
theorem contains_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    (insertManyIfNewUnit t l).contains k = (t.contains k || l.contains k) :=
  Impl.Const.contains_insertManyIfNewUnit!_list h

@[simp]
theorem mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    k ∈ insertManyIfNewUnit t l ↔ k ∈ t ∨ l.contains k :=
  Impl.Const.mem_insertManyIfNewUnit!_list h

theorem mem_of_mem_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} (contains_eq_false : l.contains k = false) :
    k ∈ insertManyIfNewUnit t l → k ∈ t :=
  Impl.Const.mem_of_mem_insertManyIfNewUnit!_list h contains_eq_false

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF) {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false → getKey? (insertManyIfNewUnit t l) k = none :=
  Impl.Const.getKey?_insertManyIfNewUnit!_list_of_not_mem_of_contains_eq_false h

theorem getKey?_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k k' : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey? (insertManyIfNewUnit t l) k' = some k :=
  Impl.Const.getKey?_insertManyIfNewUnit!_list_of_not_mem_of_mem h k_eq

theorem getKey?_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k : α} :
    k ∈ t → getKey? (insertManyIfNewUnit t l) k = getKey? t k :=
  Impl.Const.getKey?_insertManyIfNewUnit!_list_of_mem h

theorem getKey_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k : α} {h'} (contains : k ∈ t) :
    getKey (insertManyIfNewUnit t l) k h' = getKey t k contains :=
  Impl.Const.getKey_insertManyIfNewUnit!_list_of_mem h contains

theorem getKey_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq) {h'} :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey (insertManyIfNewUnit t l) k' h' = k :=
  Impl.Const.getKey_insertManyIfNewUnit!_list_of_not_mem_of_mem h k_eq

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] [Inhabited α] (h : t.WF) {l : List α} {k : α} :
    ¬ k ∈ t → l.contains k = false →
      getKey! (insertManyIfNewUnit t l) k = default :=
  Impl.Const.getKey!_insertManyIfNewUnit!_list_of_not_mem_of_contains_eq_false h

theorem getKey!_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    [Inhabited α] (h : t.WF) {l : List α} {k k' : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKey! (insertManyIfNewUnit t l) k' = k :=
  Impl.Const.getKey!_insertManyIfNewUnit!_list_of_not_mem_of_mem h k_eq

theorem getKey!_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    [Inhabited α] (h : t.WF) {l : List α} {k : α} :
    k ∈ t → getKey! (insertManyIfNewUnit t l) k = getKey! t k :=
  Impl.Const.getKey!_insertManyIfNewUnit!_list_of_mem h

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_contains_eq_false
    [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF) {l : List α} {k fallback : α} :
    ¬ k ∈ t → l.contains k = false → getKeyD (insertManyIfNewUnit t l) k fallback = fallback :=
  Impl.Const.getKeyD_insertManyIfNewUnit!_list_of_not_mem_of_contains_eq_false h

theorem getKeyD_insertManyIfNewUnit_list_of_not_mem_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq) :
    ¬ k ∈ t → l.Pairwise (fun a b => ¬ cmp a b = .eq) → k ∈ l →
      getKeyD (insertManyIfNewUnit t l) k' fallback = k :=
  Impl.Const.getKeyD_insertManyIfNewUnit!_list_of_not_mem_of_mem h k_eq

theorem getKeyD_insertManyIfNewUnit_list_of_mem [TransCmp cmp]
    (h : t.WF) {l : List α} {k fallback : α} :
    k ∈ t → getKeyD (insertManyIfNewUnit t l) k fallback = getKeyD t k fallback :=
  Impl.Const.getKeyD_insertManyIfNewUnit!_list_of_mem h

theorem size_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (∀ (a : α), a ∈ t → l.contains a = false) →
    (insertManyIfNewUnit t l).size = t.size + l.length :=
  Impl.Const.size_insertManyIfNewUnit!_list h distinct

theorem size_le_size_insertManyIfNewUnit_list [TransCmp cmp] (h : t.WF)
    {l : List α} :
    t.size ≤ (insertManyIfNewUnit t l).size :=
  Impl.Const.size_le_size_insertManyIfNewUnit!_list h

theorem size_insertManyIfNewUnit_list_le [TransCmp cmp] (h : t.WF)
    {l : List α} :
    (insertManyIfNewUnit t l).size ≤ t.size + l.length :=
  Impl.Const.size_insertManyIfNewUnit!_list_le h

@[simp]
theorem isEmpty_insertManyIfNewUnit_list [TransCmp cmp] (h : t.WF) {l : List α} :
    (insertManyIfNewUnit t l).isEmpty = (t.isEmpty && l.isEmpty) :=
  Impl.Const.isEmpty_insertManyIfNewUnit!_list h

@[simp]
theorem get?_insertManyIfNewUnit_list [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] (h : t.WF)
    {l : List α} {k : α} :
    get? (insertManyIfNewUnit t l) k =
      if k ∈ t ∨ l.contains k then some () else none :=
  Impl.Const.get?_insertManyIfNewUnit!_list h

@[simp]
theorem get_insertManyIfNewUnit_list {l : List α} {k : α} {h'} :
    get (insertManyIfNewUnit t l) k h' = () :=
  rfl

@[simp]
theorem get!_insertManyIfNewUnit_list {l : List α} {k : α} :
    get! (insertManyIfNewUnit t l) k = () :=
  rfl

@[simp]
theorem getD_insertManyIfNewUnit_list
    {l : List α} {k : α} {fallback : Unit} :
    getD (insertManyIfNewUnit t l) k fallback = () :=
  rfl

end Const

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List ((a : α) × (β a))) cmp = ∅ :=
  rfl

@[simp, grind =]
theorem ofList_singleton {k : α} {v : β k} :
    ofList [⟨k, v⟩] cmp = (∅ : Raw α β cmp).insert k v :=
  rfl

@[grind _=_]
theorem ofList_cons {k : α} {v : β k} {tl : List ((a : α) × (β a))} :
    ofList (⟨k, v⟩ :: tl) cmp = ((∅ : Raw α β cmp).insert k v).insertMany tl :=
  ext Impl.insertMany_empty_list_cons_eq_insertMany!

theorem ofList_eq_insertMany_empty {l : List ((a : α) × (β a))} :
    ofList l cmp = insertMany (∅ : Raw α β cmp) l :=
  match l with
  | [] => by simp
  | ⟨k, v⟩ :: tl => by simp [ofList_cons, insertMany_cons]

@[simp, grind =]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    (ofList l cmp).contains k = (l.map Sigma.fst).contains k := by
  simp only [contains, ofList, Impl.ofList]
  exact Impl.contains_insertMany_empty_list (instOrd := ⟨cmp⟩) (k := k) (l := l)

@[simp, grind =]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} :
    k ∈ ofList l cmp ↔ (l.map Sigma.fst).contains k := by
  simp [← contains_iff_mem]

theorem get?_ofList_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).get? k = none :=
  Impl.get?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp).get? k' = some (cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v) :=
  Impl.get?_insertMany_empty_list_of_mem k_eq distinct mem

theorem get_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    (ofList l cmp).get k' h = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v :=
  Impl.get_insertMany_empty_list_of_mem k_eq distinct mem

theorem get!_ofList_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} [Inhabited (β k)]
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).get! k = default :=
  Impl.get!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} [Inhabited (β k')]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp).get! k' = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v :=
  Impl.get!_insertMany_empty_list_of_mem k_eq distinct mem

theorem getD_ofList_of_contains_eq_false [TransCmp cmp] [LawfulEqCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α} {fallback : β k}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getD k fallback = fallback :=
  Impl.getD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [TransCmp cmp] [LawfulEqCmp cmp]
    {l : List ((a : α) × β a)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β k} {fallback : β k'}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    (ofList l cmp).getD k' fallback = cast (by congr; apply LawfulEqCmp.compare_eq_iff_eq.mp k_eq) v :=
  Impl.getD_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getKey? k = none :=
  Impl.getKey?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l cmp).getKey? k' = some k :=
  Impl.getKey?_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey_ofList_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst)
    {h'} :
    (ofList l cmp).getKey k' h' = k :=
  Impl.getKey_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey!_ofList_of_contains_eq_false [TransCmp cmp] [Inhabited α] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getKey! k = default :=
  Impl.getKey!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [TransCmp cmp] [Inhabited α]
    {l : List ((a : α) × β a)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l cmp).getKey! k' = k :=
  Impl.getKey!_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List ((a : α) × β a)} {k fallback : α}
    (contains_eq_false : (l.map Sigma.fst).contains k = false) :
    (ofList l cmp).getKeyD k fallback = fallback :=
  Impl.getKeyD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [TransCmp cmp]
    {l : List ((a : α) × β a)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Sigma.fst) :
    (ofList l cmp).getKeyD k' fallback = k :=
  Impl.getKeyD_insertMany_empty_list_of_mem k_eq distinct mem

theorem size_ofList [TransCmp cmp]
    {l : List ((a : α) × β a)} (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (ofList l cmp).size = l.length :=
  Impl.size_insertMany_empty_list distinct

theorem size_ofList_le [TransCmp cmp] {l : List ((a : α) × β a)} :
    (ofList l cmp).1.size ≤ l.length :=
  Impl.size_insertMany_empty_list_le

grind_pattern size_ofList_le => (ofList l cmp).1.size

@[simp, grind =]
theorem isEmpty_ofList [TransCmp cmp] {l : List ((a : α) × β a)} :
    (ofList l cmp).1.isEmpty = l.isEmpty :=
  Impl.isEmpty_insertMany_empty_list

namespace Const

variable {β : Type v}

@[simp, grind =]
theorem ofList_nil :
    ofList ([] : List (α × β)) cmp = ∅ := by
  rfl

@[simp, grind =]
theorem ofList_singleton {k : α} {v : β} :
    ofList [⟨k, v⟩] cmp = (∅ : Raw α β cmp).insert k v := by
  rfl

@[grind _=_]
theorem ofList_cons {k : α} {v : β} {tl : List (α × β)} :
    ofList (⟨k, v⟩ :: tl) cmp = insertMany ((∅ : Raw α β cmp).insert k v) tl :=
  ext <| Impl.Const.insertMany_empty_list_cons_eq_insertMany!

theorem ofList_eq_insertMany_empty {l : List (α × β)} :
    ofList l cmp = insertMany (∅ : Raw α β cmp) l :=
  match l with
  | [] => by simp
  | ⟨k, v⟩ :: tl => by simp [ofList_cons, insertMany_cons]

@[simp, grind =]
theorem contains_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    (ofList l cmp).contains k = (l.map Prod.fst).contains k :=
  Impl.Const.contains_insertMany_empty_list

@[simp, grind =]
theorem mem_ofList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List (α × β)} {k : α} :
    k ∈ ofList l cmp ↔ (l.map Prod.fst).contains k := by
  simp [← contains_iff_mem]

theorem get?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get? (ofList l cmp) k = none :=
  Impl.Const.get?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get?_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    get? (ofList l cmp) k' = some v :=
  Impl.Const.get?_insertMany_empty_list_of_mem k_eq distinct mem

theorem get_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l)
    {h} :
    get (ofList l cmp) k' h = v :=
  Impl.Const.get_insertMany_empty_list_of_mem k_eq distinct mem

theorem get!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} [Inhabited β]
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    get! (ofList l cmp) k = default :=
  Impl.Const.get!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem get!_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} [Inhabited β]
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    get! (ofList l cmp) k' = v :=
  Impl.Const.get!_insertMany_empty_list_of_mem k_eq distinct mem

theorem getD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α} {fallback : β}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    getD (ofList l cmp) k fallback = fallback :=
  Impl.Const.getD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getD_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)} {k k' : α} (k_eq : cmp k k' = .eq) {v : β} {fallback : β}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : ⟨k, v⟩ ∈ l) :
    getD (ofList l cmp) k' fallback = v :=
  Impl.Const.getD_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey?_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKey? k = none :=
  Impl.Const.getKey?_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey?_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKey? k' = some k :=
  Impl.Const.getKey?_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst)
    {h'} :
    (ofList l cmp).getKey k' h' = k :=
  Impl.Const.getKey_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKey!_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    [Inhabited α] {l : List (α × β)} {k : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKey! k = default :=
  Impl.Const.getKey!_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKey!_ofList_of_mem [TransCmp cmp] [Inhabited α]
    {l : List (α × β)}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKey! k' = k :=
  Impl.Const.getKey!_insertMany_empty_list_of_mem k_eq distinct mem

theorem getKeyD_ofList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List (α × β)} {k fallback : α}
    (contains_eq_false : (l.map Prod.fst).contains k = false) :
    (ofList l cmp).getKeyD k fallback = fallback :=
  Impl.Const.getKeyD_insertMany_empty_list_of_contains_eq_false contains_eq_false

theorem getKeyD_ofList_of_mem [TransCmp cmp]
    {l : List (α × β)}
    {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq))
    (mem : k ∈ l.map Prod.fst) :
    (ofList l cmp).getKeyD k' fallback = k :=
  Impl.Const.getKeyD_insertMany_empty_list_of_mem k_eq distinct mem

theorem size_ofList [TransCmp cmp] {l : List (α × β)}
    (distinct : l.Pairwise (fun a b => ¬ cmp a.1 b.1 = .eq)) :
    (ofList l cmp).size = l.length :=
  Impl.Const.size_insertMany_empty_list distinct

theorem size_ofList_le [TransCmp cmp] {l : List (α × β)} :
    (ofList l cmp).size ≤ l.length :=
  Impl.Const.size_insertMany_empty_list_le

grind_pattern size_ofList_le => (ofList l cmp).size

@[simp, grind =]
theorem isEmpty_ofList [TransCmp cmp] {l : List (α × β)} :
    (ofList l cmp).isEmpty = l.isEmpty :=
  Impl.Const.isEmpty_insertMany_empty_list

@[simp]
theorem unitOfList_nil :
    unitOfList ([] : List α) cmp =
      (∅ : Raw α Unit cmp) :=
  rfl

@[simp]
theorem unitOfList_singleton {k : α} :
    unitOfList [k] cmp = (∅ : Raw α Unit cmp).insertIfNew k () :=
  rfl

theorem unitOfList_cons {hd : α} {tl : List α} :
    unitOfList (hd :: tl) cmp =
      insertManyIfNewUnit ((∅ : Raw α Unit cmp).insertIfNew hd ()) tl :=
  ext Impl.Const.insertManyIfNewUnit_empty_list_cons_eq_insertManyIfNewUnit!

@[simp]
theorem contains_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    (unitOfList l cmp).contains k = l.contains k :=
  Impl.Const.contains_insertManyIfNewUnit_empty_list

@[simp]
theorem mem_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    k ∈ unitOfList l cmp ↔ l.contains k := by
  simp [← contains_iff_mem]

theorem getKey?_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp]
    {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey? (unitOfList l cmp) k = none :=
  Impl.Const.getKey?_insertManyIfNewUnit_empty_list_of_contains_eq_false contains_eq_false

theorem getKey?_unitOfList_of_mem [TransCmp cmp]
    {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) (mem : k ∈ l) :
    getKey? (unitOfList l cmp) k' = some k :=
  Impl.Const.getKey?_insertManyIfNewUnit_empty_list_of_mem k_eq distinct mem

theorem getKey_unitOfList_of_mem [TransCmp cmp]
    {l : List α}
    {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) {h'} :
    getKey (unitOfList l cmp) k' h' = k :=
  Impl.Const.getKey_insertManyIfNewUnit_empty_list_of_mem k_eq distinct mem

theorem getKey!_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] [Inhabited α] {l : List α} {k : α}
    (contains_eq_false : l.contains k = false) :
    getKey! (unitOfList l cmp) k = default :=
  Impl.Const.getKey!_insertManyIfNewUnit_empty_list_of_contains_eq_false contains_eq_false

theorem getKey!_unitOfList_of_mem [TransCmp cmp]
    [Inhabited α] {l : List α} {k k' : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getKey! (unitOfList l cmp) k' = k :=
  Impl.Const.getKey!_insertManyIfNewUnit_empty_list_of_mem k_eq distinct mem

theorem getKeyD_unitOfList_of_contains_eq_false [TransCmp cmp] [BEq α]
    [LawfulBEqCmp cmp] {l : List α} {k fallback : α}
    (contains_eq_false : l.contains k = false) :
    getKeyD (unitOfList l cmp) k fallback = fallback :=
  Impl.Const.getKeyD_insertManyIfNewUnit_empty_list_of_contains_eq_false contains_eq_false

theorem getKeyD_unitOfList_of_mem [TransCmp cmp]
    {l : List α} {k k' fallback : α} (k_eq : cmp k k' = .eq)
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq))
    (mem : k ∈ l) :
    getKeyD (unitOfList l cmp) k' fallback = k :=
  Impl.Const.getKeyD_insertManyIfNewUnit_empty_list_of_mem k_eq distinct mem

theorem size_unitOfList [TransCmp cmp] {l : List α}
    (distinct : l.Pairwise (fun a b => ¬ cmp a b = .eq)) :
    (unitOfList l cmp).size = l.length :=
  Impl.Const.size_insertManyIfNewUnit_empty_list distinct

theorem size_unitOfList_le [TransCmp cmp] {l : List α} :
    (unitOfList l cmp).size ≤ l.length :=
  Impl.Const.size_insertManyIfNewUnit_empty_list_le

@[simp]
theorem isEmpty_unitOfList [TransCmp cmp] {l : List α} :
    (unitOfList l cmp).isEmpty = l.isEmpty :=
  Impl.Const.isEmpty_insertManyIfNewUnit_empty_list

@[simp]
theorem get?_unitOfList [TransCmp cmp] [BEq α] [LawfulBEqCmp cmp] {l : List α} {k : α} :
    get? (unitOfList l cmp) k = if l.contains k then some () else none :=
  Impl.Const.get?_insertManyIfNewUnit_empty_list

@[simp]
theorem get_unitOfList {l : List α} {k : α} {h} :
    get (unitOfList l cmp) k h = () :=
  Impl.Const.get_insertManyIfNewUnit_empty_list

@[simp]
theorem get!_unitOfList {l : List α} {k : α} :
    get! (unitOfList l cmp) k = () :=
  Impl.Const.get!_insertManyIfNewUnit_empty_list

@[simp]
theorem getD_unitOfList {l : List α} {k : α} {fallback : Unit} :
    getD (unitOfList l cmp) k fallback = () :=
  Impl.Const.getD_insertManyIfNewUnit_empty_list

end Const

section Alter

theorem isEmpty_alter_eq_isEmpty_erase [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).isEmpty = ((t.erase k).isEmpty && (f (t.get? k)).isNone) :=
  Impl.isEmpty_alter!_eq_isEmpty_erase h

@[simp, grind =]
theorem isEmpty_alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).isEmpty =
      (((t.isEmpty || (t.size == 1 && t.contains k))) && (f (t.get? k)).isNone) :=
  Impl.isEmpty_alter! h

@[grind =]
theorem contains_alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).contains k' = if cmp k k' = .eq then (f (t.get? k)).isSome else t.contains k' :=
  Impl.contains_alter! h

@[grind =]
theorem mem_alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    k' ∈ t.alter k f ↔ if cmp k k' = .eq then (f (t.get? k)).isSome = true else k' ∈ t :=
  Impl.mem_alter! h

theorem mem_alter_of_compare_eq [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)}
    (he : cmp k k' = .eq) :
    k' ∈ t.alter k f ↔ (f (t.get? k)).isSome :=
  Impl.mem_alter!_of_compare_eq h he

@[simp]
theorem contains_alter_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).contains k = (f (t.get? k)).isSome :=
  Impl.contains_alter!_self h

@[simp]
theorem mem_alter_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    k ∈ t.alter k f ↔ (f (t.get? k)).isSome :=
  Impl.mem_alter!_self h

theorem contains_alter_of_not_compare_eq [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} (he : ¬ cmp k k' = .eq) :
    (t.alter k f).contains k' = t.contains k' :=
  Impl.contains_alter!_of_not_compare_eq h he

theorem mem_alter_of_not_compare_eq [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} (he : ¬ cmp k k' = .eq) :
    k' ∈ t.alter k f ↔ k' ∈ t :=
  Impl.mem_alter!_of_not_compare_eq h he

@[grind =]
theorem size_alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).size =
      if k ∈ t ∧ (f (t.get? k)).isNone then
        t.size - 1
      else if k ∉ t ∧ (f (t.get? k)).isSome then
        t.size + 1
      else
        t.size :=
  Impl.size_alter! h

theorem size_alter_eq_add_one [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∉ t) (h₂ : (f (t.get? k)).isSome) :
    (t.alter k f).size = t.size + 1 :=
  Impl.size_alter!_eq_add_one h h₁ h₂

theorem size_alter_eq_sub_one [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∈ t) (h₂ : (f (t.get? k)).isNone) :
    (t.alter k f).size = t.size - 1 :=
  Impl.size_alter!_eq_sub_one h h₁ h₂

theorem size_alter_eq_self_of_not_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : ¬ k ∈ t) (h₂ : (f (t.get? k)).isNone) :
    (t.alter k f).size = t.size :=
  Impl.size_alter!_eq_self_of_not_mem h h₁ h₂

theorem size_alter_eq_self_of_mem [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} (h₁ : k ∈ t) (h₂ : (f (t.get? k)).isSome) :
    (t.alter k f).size = t.size :=
  Impl.size_alter!_eq_self_of_mem h h₁ h₂

theorem size_alter_le_size [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).size ≤ t.size + 1 :=
  Impl.size_alter!_le_size h

theorem size_le_size_alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    t.size - 1 ≤ (t.alter k f).size :=
  Impl.size_le_size_alter! h

@[grind =]
theorem get?_alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get? k' =
      if h : cmp k k' = .eq then
        cast (congrArg (Option ∘ β) (LawfulEqCmp.compare_eq_iff_eq.mp h)) (f (t.get? k))
      else
        t.get? k' :=
  Impl.get?_alter! h

@[simp]
theorem get?_alter_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get? k = f (t.get? k) := by
  simp [get?_alter h, ReflCmp.compare_self]

@[grind =]
theorem get_alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} {hc : k' ∈ (t.alter k f)} :
    (t.alter k f).get k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : (f (t.get? k)).isSome := mem_alter_of_compare_eq h heq |>.mp hc
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp heq)) <| (f (t.get? k)).get <| h'
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq h heq |>.mp hc
        t.get k' h' :=
  Impl.get_alter! h

@[simp]
theorem get_alter_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} {hc : k ∈ t.alter k f} :
    haveI h' : (f (t.get? k)).isSome := mem_alter_self h |>.mp hc
    (t.alter k f).get k hc = (f (t.get? k)).get h' :=
  Impl.get_alter!_self h

@[grind =]
theorem get!_alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k k' : α} [Inhabited (β k')]
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get! k' =
      if heq : cmp k k' = .eq then
        (f (t.get? k)).map (cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp heq))) |>.get!
      else
        t.get! k' :=
  Impl.get!_alter! h

@[simp]
theorem get!_alter_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} [Inhabited (β k)]
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).get! k = (f (t.get? k)).get! :=
  Impl.get!_alter!_self h

@[grind =]
theorem getD_alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k k' : α} {fallback : β k'}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getD k' fallback =
      if heq : cmp k k' = .eq then
        f (t.get? k) |>.map (cast (congrArg β <| LawfulEqCmp.compare_eq_iff_eq.mp heq)) |>.getD fallback
      else
        t.getD k' fallback :=
  Impl.getD_alter! h

@[simp]
theorem getD_alter_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α} {fallback : β k}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getD k fallback = (f (t.get? k)).getD fallback :=
  Impl.getD_alter!_self h

@[grind =]
theorem getKey?_alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKey? k' =
      if cmp k k' = .eq then
        if (f (t.get? k)).isSome then some k else none
      else
        t.getKey? k' :=
  Impl.getKey?_alter! h

theorem getKey?_alter_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKey? k = if (f (t.get? k)).isSome then some k else none :=
  Impl.getKey?_alter!_self h

@[grind =]
theorem getKey!_alter [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} : (t.alter k f).getKey! k' =
      if cmp k k' = .eq then
        if (f (t.get? k)).isSome then k else default
      else
        t.getKey! k' :=
  Impl.getKey!_alter! h

theorem getKey!_alter_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKey! k = if (f (t.get? k)).isSome then k else default :=
  Impl.getKey!_alter!_self h

@[deprecated getKey_eq (since := "2025-01-05")]
theorem getKey_alter [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k k' : α}
    {f : Option (β k) → Option (β k)} {hc : k' ∈ t.alter k f} :
    (t.alter k f).getKey k' hc =
      if heq : cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq h heq |>.mp hc
        t.getKey k' h' :=
  Impl.getKey_alter! h

@[simp]
theorem getKey_alter_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k : α}
    {f : Option (β k) → Option (β k)} {hc : k ∈ t.alter k f} :
    (t.alter k f).getKey k hc = k :=
  Impl.getKey_alter!_self h

@[grind =]
theorem getKeyD_alter [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k k' fallback : α}
    {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if (f (t.get? k)).isSome then k else fallback
      else
        t.getKeyD k' fallback :=
  Impl.getKeyD_alter! h

@[simp]
theorem getKeyD_alter_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k : α}
    {fallback : α} {f : Option (β k) → Option (β k)} :
    (t.alter k f).getKeyD k fallback = if (f (t.get? k)).isSome then k else fallback :=
  Impl.getKeyD_alter!_self h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem isEmpty_alter_eq_isEmpty_erase [TransCmp cmp] (h : t.WF) {k : α}
    {f : Option β → Option β} :
    (alter t k f).isEmpty = ((t.erase k).isEmpty && (f (get? t k)).isNone) :=
   Impl.Const.isEmpty_alter!_eq_isEmpty_erase h

@[simp, grind =]
theorem isEmpty_alter [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter t k f).isEmpty =
      (((t.isEmpty || (t.size == 1 && t.contains k))) && (f (get? t k)).isNone) :=
  Impl.Const.isEmpty_alter! h

@[grind =]
theorem contains_alter [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter t k f).contains k' =
      if cmp k k' = .eq then (f (get? t k)).isSome else t.contains k' :=
  Impl.Const.contains_alter! h

@[grind =]
theorem mem_alter [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    k' ∈ alter t k f ↔
      if cmp k k' = .eq then (f (get? t k)).isSome = true else k' ∈ t :=
  Impl.Const.mem_alter! h

theorem mem_alter_of_compare_eq [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β}
    (he : cmp k k' = .eq) :
    k' ∈ alter t k f ↔ (f (get? t k)).isSome :=
  Impl.Const.mem_alter!_of_compare_eq h he

@[simp]
theorem contains_alter_self [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter t k f).contains k = (f (get? t k)).isSome :=
  Impl.Const.contains_alter!_self h

@[simp]
theorem mem_alter_self [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    k ∈ alter t k f ↔ (f (get? t k)).isSome :=
  Impl.Const.mem_alter!_self h

theorem contains_alter_of_not_compare_eq [TransCmp cmp] (h : t.WF) {k k' : α}
    {f : Option β → Option β} (he : ¬ cmp k k' = .eq) :
    (alter t k f).contains k' = t.contains k' :=
  Impl.Const.contains_alter!_of_not_compare_eq h he

theorem mem_alter_of_not_compare_eq [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β}
    (he : ¬ cmp k k' = .eq) :
    k' ∈ alter t k f ↔ k' ∈ t :=
  Impl.Const.mem_alter!_of_not_compare_eq h he

@[grind =]
theorem size_alter [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter t k f).size =
      if k ∈ t ∧ (f (get? t k)).isNone then
        t.size - 1
      else if k ∉ t ∧ (f (get? t k)).isSome then
        t.size + 1
      else
        t.size :=
  Impl.Const.size_alter! h

theorem size_alter_eq_add_one [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∉ t) (h₂ : (f (get? t k)).isSome) :
    (alter t k f).size = t.size + 1 :=
  Impl.Const.size_alter!_eq_add_one h h₁ h₂

theorem size_alter_eq_sub_one [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f (get? t k)).isNone) :
    (alter t k f).size = t.size - 1 :=
  Impl.Const.size_alter!_eq_sub_one h h₁ h₂

theorem size_alter_eq_self_of_not_mem [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : ¬ k ∈ t) (h₂ : (f (get? t k)).isNone) :
    (alter t k f).size = t.size :=
  Impl.Const.size_alter!_eq_self_of_not_mem h h₁ h₂

theorem size_alter_eq_self_of_mem [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β}
    (h₁ : k ∈ t) (h₂ : (f (get? t k)).isSome) :
    (alter t k f).size = t.size :=
  Impl.Const.size_alter!_eq_self_of_mem h h₁ h₂

theorem size_alter_le_size [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter t k f).size ≤ t.size + 1 :=
  Impl.Const.size_alter!_le_size h

theorem size_le_size_alter [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    t.size - 1 ≤ (alter t k f).size :=
  Impl.Const.size_le_size_alter! h

@[grind =]
theorem get?_alter [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    get? (alter t k f) k' =
      if cmp k k' = .eq then
        f (get? t k)
      else
        get? t k' :=
  Impl.Const.get?_alter! h

@[simp]
theorem get?_alter_self [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    get? (alter t k f) k = f (get? t k) :=
  Impl.Const.get?_alter!_self h

@[grind =]
theorem get_alter [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ (alter t k f)} :
    get (alter t k f) k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : (f (get? t k)).isSome := mem_alter_of_compare_eq h heq |>.mp hc
        (f (get? t k)).get h'
      else
        haveI h' : k' ∈ t := mem_alter_of_not_compare_eq h heq |>.mp hc
        get t k' h' :=
  Impl.Const.get_alter! h

@[simp]
theorem get_alter_self [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    haveI h' : (f (get? t k)).isSome := mem_alter_self h |>.mp hc
    get (alter t k f) k hc = (f (get? t k)).get h' :=
  Impl.Const.get_alter!_self h

@[grind =]
theorem get!_alter [TransCmp cmp] (h : t.WF) {k k' : α} [Inhabited β] {f : Option β → Option β} :
    get! (alter t k f) k' =
      if cmp k k' = .eq then
        (f (get? t k)).get!
      else
        get! t k' :=
  Impl.Const.get!_alter! h

@[simp]
theorem get!_alter_self [TransCmp cmp] (h : t.WF) {k : α} [Inhabited β] {f : Option β → Option β} :
    get! (alter t k f) k = (f (get? t k)).get! :=
  Impl.Const.get!_alter!_self h

@[grind =]
theorem getD_alter [TransCmp cmp] (h : t.WF) {k k' : α} {fallback : β} {f : Option β → Option β} :
    getD (alter t k f) k' fallback =
      if cmp k k' = .eq then
        f (get? t k) |>.getD fallback
      else
        getD t k' fallback :=
  Impl.Const.getD_alter! h

@[simp]
theorem getD_alter_self [TransCmp cmp] (h : t.WF) {k : α} {fallback : β}
    {f : Option β → Option β} :
    getD (alter t k f) k fallback = (f (get? t k)).getD fallback :=
  Impl.Const.getD_alter!_self h

@[grind =]
theorem getKey?_alter [TransCmp cmp] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey? k' =
      if cmp k k' = .eq then
        if (f (get? t k)).isSome then some k else none
      else
        t.getKey? k' :=
  Impl.Const.getKey?_alter! h

theorem getKey?_alter_self [TransCmp cmp] (h : t.WF) {k : α} {f : Option β → Option β} :
    (alter t k f).getKey? k = if (f (get? t k)).isSome then some k else none :=
  Impl.Const.getKey?_alter!_self h

@[grind =]
theorem getKey!_alter [TransCmp cmp] [Inhabited α] (h : t.WF) {k k' : α} {f : Option β → Option β} :
    (alter t k f).getKey! k' =
      if cmp k k' = .eq then
        if (f (get? t k)).isSome then k else default
      else
        t.getKey! k' :=
  Impl.Const.getKey!_alter! h

theorem getKey!_alter_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k : α}
    {f : Option β → Option β} :
    (alter t k f).getKey! k = if (f (get? t k)).isSome then k else default :=
  Impl.Const.getKey!_alter!_self h

@[grind =]
theorem getKey_alter [TransCmp cmp] [Inhabited α] (h : t.WF) {k k' : α} {f : Option β → Option β}
    {hc : k' ∈ alter t k f} :
    (alter t k f).getKey k' hc =
      if heq : cmp k k' = .eq then
        k
      else
        haveI h' : t.contains k' := mem_alter_of_not_compare_eq h heq |>.mp hc
        t.getKey k' h' :=
  Impl.Const.getKey_alter! h

@[simp]
theorem getKey_alter_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k : α} {f : Option β → Option β}
    {hc : k ∈ alter t k f} :
    (alter t k f).getKey k hc = k :=
  Impl.Const.getKey_alter!_self h

@[grind =]
theorem getKeyD_alter [TransCmp cmp] (h : t.WF) {k k' fallback : α} {f : Option β → Option β} :
    (alter t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if (f (get? t k)).isSome then k else fallback
      else
        t.getKeyD k' fallback :=
  Impl.Const.getKeyD_alter! h

@[simp]
theorem getKeyD_alter_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k : α} {fallback : α}
    {f : Option β → Option β} :
    (alter t k f).getKeyD k fallback = if (f (get? t k)).isSome then k else fallback :=
  Impl.Const.getKeyD_alter!_self h

end Const

end Alter

section Modify

variable [TransCmp cmp]

section Dependent

variable [LawfulEqCmp cmp]

@[simp, grind =]
theorem isEmpty_modify (h : t.WF) {k : α} {f : β k → β k} :
    (t.modify k f).isEmpty = t.isEmpty :=
  Impl.isEmpty_modify h

@[grind =]
theorem contains_modify (h : t.WF) {k k' : α} {f : β k → β k} :
    (t.modify k f).contains k' = t.contains k' :=
  Impl.contains_modify h

@[grind =]
theorem mem_modify (h : t.WF) {k k' : α} {f : β k → β k} :
    k' ∈ t.modify k f ↔ k' ∈ t :=
  Impl.mem_modify h

@[grind =]
theorem size_modify (h : t.WF) {k : α} {f : β k → β k} :
    (t.modify k f).size = t.size :=
  Impl.size_modify h

@[grind =]
theorem get?_modify (h : t.WF) {k k' : α} {f : β k → β k} :
    (t.modify k f).get? k' =
      if h : cmp k k' = .eq then
        (cast (congrArg (Option ∘ β) (LawfulEqCmp.compare_eq_iff_eq.mp h)) ((t.get? k).map f))
      else
        t.get? k' :=
  Impl.get?_modify h

@[simp]
theorem get?_modify_self (h : t.WF) {k : α} {f : β k → β k} :
    (t.modify k f).get? k = (t.get? k).map f :=
  Impl.get?_modify_self h

@[grind =]
theorem get_modify (h : t.WF) {k k' : α} {f : β k → β k} {hc : k' ∈ t.modify k f} :
    (t.modify k f).get k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : k ∈ t := mem_congr h heq |>.mpr <| mem_modify h |>.mp hc
        cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp heq)) <| f (t.get k h')
      else
        haveI h' : k' ∈ t := (mem_modify h).mp hc
        t.get k' h' :=
  Impl.get_modify h

@[simp]
theorem get_modify_self (h : t.WF) {k : α} {f : β k → β k} {hc : k ∈ t.modify k f} :
    haveI h' : k ∈ t := mem_modify h |>.mp hc
    (t.modify k f).get k hc = f (t.get k h') :=
  Impl.get_modify_self h

@[grind =]
theorem get!_modify (h : t.WF) {k k' : α} [hi : Inhabited (β k')] {f : β k → β k} :
    (t.modify k f).get! k' =
      if heq : cmp k k' = .eq then
        t.get? k |>.map f |>.map (cast (congrArg β (LawfulEqCmp.compare_eq_iff_eq.mp heq))) |>.get!
      else
        t.get! k' :=
  Impl.get!_modify h

@[simp]
theorem get!_modify_self (h : t.WF) {k : α} [Inhabited (β k)] {f : β k → β k} :
    (t.modify k f).get! k = ((t.get? k).map f).get! :=
  Impl.get!_modify_self h

@[grind =]
theorem getD_modify (h : t.WF) {k k' : α} {fallback : β k'} {f : β k → β k} :
    (t.modify k f).getD k' fallback =
      if heq : cmp k k' = .eq then
        t.get? k |>.map f |>.map (cast (congrArg β <| LawfulEqCmp.compare_eq_iff_eq.mp heq)) |>.getD fallback
      else
        t.getD k' fallback :=
  Impl.getD_modify h

@[simp]
theorem getD_modify_self (h : t.WF) {k : α} {fallback : β k} {f : β k → β k} :
    (t.modify k f).getD k fallback = ((t.get? k).map f).getD fallback :=
  Impl.getD_modify_self h

@[grind =]
theorem getKey?_modify (h : t.WF) {k k' : α} {f : β k → β k} :
    (t.modify k f).getKey? k' =
      if cmp k k' = .eq then
        if k ∈ t then some k else none
      else
        t.getKey? k' :=
  Impl.getKey?_modify h

theorem getKey?_modify_self (h : t.WF) {k : α} {f : β k → β k} :
    (t.modify k f).getKey? k = if k ∈ t then some k else none :=
  Impl.getKey?_modify_self h

@[grind =]
theorem getKey!_modify (h : t.WF) [Inhabited α] {k k' : α} {f : β k → β k} :
    (t.modify k f).getKey! k' =
      if cmp k k' = .eq then
        if k ∈ t then k else default
      else
        t.getKey! k' :=
  Impl.getKey!_modify h

theorem getKey!_modify_self (h : t.WF) [Inhabited α] {k : α} {f : β k → β k} :
    (t.modify k f).getKey! k = if k ∈ t then k else default :=
  Impl.getKey!_modify_self h

@[grind =]
theorem getKey_modify (h : t.WF) [Inhabited α] {k k' : α} {f : β k → β k}
    {hc : k' ∈ t.modify k f} :
    (t.modify k f).getKey k' hc =
      if cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_modify h |>.mp hc
        t.getKey k' h' :=
  Impl.getKey_modify h

@[simp]
theorem getKey_modify_self (h : t.WF) [Inhabited α] {k : α} {f : β k → β k}
    {hc : k ∈ t.modify k f} : (t.modify k f).getKey k hc = k :=
  Impl.getKey_modify_self h

@[grind =]
theorem getKeyD_modify (h : t.WF) {k k' fallback : α} {f : β k → β k} :
    (t.modify k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if k ∈ t then k else fallback
      else
        t.getKeyD k' fallback :=
  Impl.getKeyD_modify h

theorem getKeyD_modify_self (h : t.WF) [Inhabited α] {k fallback : α} {f : β k → β k} :
    (t.modify k f).getKeyD k fallback = if k ∈ t then k else fallback :=
  Impl.getKeyD_modify_self h

end Dependent

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[simp, grind =]
theorem isEmpty_modify (h : t.WF) {k : α} {f : β → β} :
    (modify t k f).isEmpty = t.isEmpty :=
  Impl.Const.isEmpty_modify h

@[grind =]
theorem contains_modify (h : t.WF) {k k' : α} {f : β → β} :
    (modify t k f).contains k' = t.contains k' :=
  Impl.Const.contains_modify h

@[grind =]
theorem mem_modify (h : t.WF) {k k' : α} {f : β → β} :
    k' ∈ modify t k f ↔ k' ∈ t :=
  Impl.Const.mem_modify h

@[grind =]
theorem size_modify (h : t.WF) {k : α} {f : β → β} :
    (modify t k f).size = t.size :=
  Impl.Const.size_modify h

@[grind =]
theorem get?_modify (h : t.WF) {k k' : α} {f : β → β} :
    get? (modify t k f) k' =
      if cmp k k' = .eq then
        (get? t k).map f
      else
        get? t k' :=
  Impl.Const.get?_modify h

@[simp]
theorem get?_modify_self (h : t.WF) {k : α} {f : β → β} :
    get? (modify t k f) k = (get? t k).map f :=
  Impl.Const.get?_modify_self h

@[grind =]
theorem get_modify (h : t.WF) {k k' : α} {f : β → β} {hc : k' ∈ modify t k f} :
    get (modify t k f) k' hc =
      if heq : cmp k k' = .eq then
        haveI h' : k ∈ t := mem_congr h heq |>.mpr <| mem_modify h |>.mp hc
        f (get t k h')
      else
        haveI h' : k' ∈ t := mem_modify h |>.mp hc
        get t k' h' :=
  Impl.Const.get_modify h

@[simp]
theorem get_modify_self (h : t.WF) {k : α} {f : β → β} {hc : k ∈ modify t k f} :
    haveI h' : k ∈ t := mem_modify h |>.mp hc
    get (modify t k f) k hc = f (get t k h') :=
  Impl.Const.get_modify_self h

@[grind =]
theorem get!_modify (h : t.WF) {k k' : α} [hi : Inhabited β] {f : β → β} :
    get! (modify t k f) k' =
      if cmp k k' = .eq then
        get? t k |>.map f |>.get!
      else
        get! t k' :=
  Impl.Const.get!_modify h

@[simp]
theorem get!_modify_self (h : t.WF) {k : α} [Inhabited β] {f : β → β} :
    get! (modify t k f) k = ((get? t k).map f).get! :=
  Impl.Const.get!_modify_self h

@[grind =]
theorem getD_modify (h : t.WF) {k k' : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k' fallback =
      if cmp k k' = .eq then
        get? t k |>.map f |>.getD fallback
      else
        getD t k' fallback :=
  Impl.Const.getD_modify h

@[simp]
theorem getD_modify_self (h : t.WF) {k : α} {fallback : β} {f : β → β} :
    getD (modify t k f) k fallback = ((get? t k).map f).getD fallback :=
  Impl.Const.getD_modify_self h

@[grind =]
theorem getKey?_modify (h : t.WF) {k k' : α} {f : β → β} :
    (modify t k f).getKey? k' =
      if cmp k k' = .eq then
        if k ∈ t then some k else none
      else
        t.getKey? k' :=
  Impl.Const.getKey?_modify h

theorem getKey?_modify_self (h : t.WF) {k : α} {f : β → β} :
    (modify t k f).getKey? k = if k ∈ t then some k else none :=
  Impl.Const.getKey?_modify_self h

@[grind =]
theorem getKey!_modify (h : t.WF) [Inhabited α] {k k' : α} {f : β → β} :
    (modify t k f).getKey! k' =
      if cmp k k' = .eq then
        if k ∈ t then k else default
      else
        t.getKey! k' :=
  Impl.Const.getKey!_modify h

theorem getKey!_modify_self (h : t.WF) [Inhabited α] {k : α} {f : β → β} :
    (modify t k f).getKey! k = if k ∈ t then k else default :=
  Impl.Const.getKey!_modify_self h

@[grind =]
theorem getKey_modify (h : t.WF) [Inhabited α] {k k' : α} {f : β → β}
    {hc : k' ∈ modify t k f} :
    (modify t k f).getKey k' hc =
      if cmp k k' = .eq then
        k
      else
        haveI h' : k' ∈ t := mem_modify h |>.mp hc
        t.getKey k' h' :=
  Impl.Const.getKey_modify h

@[simp]
theorem getKey_modify_self (h : t.WF) [Inhabited α] {k : α} {f : β → β}
    {hc : k ∈ modify t k f} : (modify t k f).getKey k hc = k :=
  Impl.Const.getKey_modify_self h

@[grind =]
theorem getKeyD_modify (h : t.WF) {k k' fallback : α} {f : β → β} :
    (modify t k f).getKeyD k' fallback =
      if cmp k k' = .eq then
        if k ∈ t then k else fallback
      else
        t.getKeyD k' fallback :=
  Impl.Const.getKeyD_modify h

theorem getKeyD_modify_self (h : t.WF) [Inhabited α] {k fallback : α} {f : β → β} :
    (modify t k f).getKeyD k fallback = if k ∈ t then k else fallback :=
  Impl.Const.getKeyD_modify_self h

end Const

end Modify

section Min

@[simp, grind =]
theorem minKey?_emptyc :
    (∅ : Raw α β cmp).minKey? = none :=
  Impl.minKey?_empty

theorem minKey?_of_isEmpty [TransCmp cmp] (h : t.WF) :
    (he : t.isEmpty) → t.minKey? = none :=
  Impl.minKey?_of_isEmpty h (instOrd := ⟨cmp⟩)

@[simp, grind =]
theorem minKey?_eq_none_iff [TransCmp cmp] (h : t.WF) :
    t.minKey? = none ↔ t.isEmpty :=
  Impl.minKey?_eq_none_iff h (instOrd := ⟨cmp⟩)

theorem minKey?_eq_some_iff_getKey?_eq_self_and_forall [TransCmp cmp] (h : t.WF) {km} :
    t.minKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp km k).isLE :=
  Impl.minKey?_eq_some_iff_getKey?_eq_self_and_forall h

theorem minKey?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {km} :
    t.minKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp km k).isLE :=
  Impl.minKey?_eq_some_iff_mem_and_forall h

@[simp, grind =]
theorem isNone_minKey?_eq_isEmpty [TransCmp cmp] (h : t.WF) :
    t.minKey?.isNone = t.isEmpty :=
  Impl.isNone_minKey?_eq_isEmpty h (instOrd := ⟨cmp⟩)

@[simp, grind =]
theorem isSome_minKey?_eq_not_isEmpty [TransCmp cmp] (h : t.WF) :
    t.minKey?.isSome = !t.isEmpty :=
  Impl.isSome_minKey?_eq_not_isEmpty h (instOrd := ⟨cmp⟩)

theorem isSome_minKey?_iff_isEmpty_eq_false [TransCmp cmp] (h : t.WF) :
    t.minKey?.isSome ↔ t.isEmpty = false :=
  Impl.isSome_minKey?_iff_isEmpty_eq_false h (instOrd := ⟨cmp⟩)

@[grind =]
theorem minKey?_insert [TransCmp cmp] (h : t.WF) {k v} :
    (t.insert k v).minKey? =
      some (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  Impl.minKey?_insert! h

@[grind =]
theorem isSome_minKey?_insert [TransCmp cmp] (h : t.WF) {k v} :
    (t.insert k v).minKey?.isSome :=
  Impl.isSome_minKey?_insert! h

theorem minKey?_insert_le_minKey? [TransCmp cmp] (h : t.WF) {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insert k v |>.minKey? |>.get <| isSome_minKey?_insert h) = kmi) →
    cmp kmi km |>.isLE :=
  Impl.minKey?_insert!_le_minKey? h

theorem minKey?_insert_le_self [TransCmp cmp] (h : t.WF) {k v kmi} :
    (hkmi : (t.insert k v |>.minKey?.get <| isSome_minKey?_insert h) = kmi) →
    cmp kmi k |>.isLE :=
  Impl.minKey?_insert!_le_self h

theorem contains_minKey? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.minKey? = some km) →
    t.contains km :=
  Impl.contains_minKey? h

theorem minKey?_mem [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.minKey? = some km) →
    km ∈ t:=
  Impl.minKey?_mem h

theorem isSome_minKey?_of_contains [TransCmp cmp] (h : t.WF) {k} :
    (hc : t.contains k) → t.minKey?.isSome :=
  Impl.isSome_minKey?_of_contains h

theorem isSome_minKey?_of_mem [TransCmp cmp] (h : t.WF) {k} :
    k ∈ t → t.minKey?.isSome :=
  Impl.isSome_minKey?_of_mem h

theorem minKey?_le_of_contains [TransCmp cmp] (h : t.WF) {k km} :
    (hc : t.contains k) → (hkm : (t.minKey?.get <| isSome_minKey?_of_contains h hc) = km) →
    cmp km k |>.isLE :=
  Impl.minKey?_le_of_contains h

theorem minKey?_le_of_mem [TransCmp cmp] (h : t.WF) {k km} :
    (hc : k ∈ t) → (hkm : (t.minKey?.get <| isSome_minKey?_of_mem h hc) = km) →
    cmp km k |>.isLE :=
  Impl.minKey?_le_of_mem h

theorem le_minKey? [TransCmp cmp] {k} (h : t.WF) :
    (∀ k', t.minKey? = some k' → (cmp k k').isLE) ↔
      (∀ k', k' ∈ t → (cmp k k').isLE) :=
  Impl.le_minKey? h (instOrd := ⟨cmp⟩)

theorem getKey?_minKey? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.minKey? = some km) → t.getKey? km = some km :=
  Impl.getKey?_minKey? h

theorem getKey_minKey? [TransCmp cmp] (h : t.WF) {km hc} :
    (hkm : t.minKey?.get (isSome_minKey?_of_contains h hc) = km) → t.getKey km hc = km :=
  Impl.getKey_minKey? h

theorem getKey!_minKey? [TransCmp cmp] [Inhabited α] (h : t.WF) {km} :
    (hkm : t.minKey? = some km) → t.getKey! km = km :=
  Impl.getKey!_minKey? h

theorem getKeyD_minKey? [TransCmp cmp] (h : t.WF) {km fallback} :
    (hkm : t.minKey? = some km) → t.getKeyD km fallback = km :=
  Impl.getKeyD_minKey? h

@[simp]
theorem minKey?_bind_getKey? [TransCmp cmp] (h : t.WF) :
    t.minKey?.bind t.getKey? = t.minKey? :=
  Impl.minKey?_bind_getKey? h

theorem minKey?_erase_eq_iff_not_compare_eq_minKey? [TransCmp cmp] (h : t.WF) {k} :
    (t.erase k |>.minKey?) = t.minKey? ↔
      ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq :=
  Impl.minKey?_erase!_eq_iff_not_compare_eq_minKey? h

theorem minKey?_erase_eq_of_not_compare_eq_minKey? [TransCmp cmp] (h : t.WF) {k} :
    (hc : ∀ {km}, t.minKey? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.minKey?) = t.minKey? :=
  Impl.minKey?_erase!_eq_of_not_compare_eq_minKey? h (instOrd := ⟨cmp⟩)

theorem isSome_minKey?_of_isSome_minKey?_erase [TransCmp cmp] (h : t.WF) {k} :
    (hs : t.erase k |>.minKey?.isSome) →
    t.minKey?.isSome :=
  Impl.isSome_minKey?_of_isSome_minKey?_erase! h

theorem minKey?_le_minKey?_erase [TransCmp cmp] (h : t.WF) {k km kme} :
    (hkme : (t.erase k |>.minKey?) = some kme) →
    (hkm : (t.minKey?.get <|
      isSome_minKey?_of_isSome_minKey?_erase h <| hkme ▸ Option.isSome_some) = km) →
    cmp km kme |>.isLE :=
  Impl.minKey?_le_minKey?_erase! h

@[grind =]
theorem minKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v} :
    (t.insertIfNew k v).minKey? =
      some (t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k') :=
  Impl.minKey?_insertIfNew! h

@[grind =]
theorem isSome_minKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v} :
    (t.insertIfNew k v).minKey?.isSome :=
  Impl.isSome_minKey?_insertIfNew! h

theorem minKey?_insertIfNew_le_minKey? [TransCmp cmp] (h : t.WF) {k v km kmi} :
    (hkm : t.minKey? = some km) →
    (hkmi : (t.insertIfNew k v |>.minKey? |>.get <| isSome_minKey?_insertIfNew h) = kmi) →
    cmp kmi km |>.isLE :=
  Impl.minKey?_insertIfNew!_le_minKey? h

theorem minKey?_insertIfNew_le_self [TransCmp cmp] (h : t.WF) {k v kmi} :
    (hkmi : (t.insertIfNew k v |>.minKey?.get <| isSome_minKey?_insertIfNew h) = kmi) →
    cmp kmi k |>.isLE :=
  Impl.minKey?_insertIfNew!_le_self h

@[grind =_]
theorem minKey?_eq_head?_keys [TransCmp cmp] (h : t.WF) :
    t.minKey? = t.keys.head? :=
  Impl.minKey?_eq_head?_keys h (instOrd := ⟨cmp⟩)

@[simp, grind =]
theorem minKey?_modify [TransCmp cmp] [LawfulEqCmp cmp] {k f} (h : t.WF) :
    (t.modify k f).minKey? = t.minKey? :=
  Impl.minKey?_modify h

theorem minKey?_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f} :
    (t.alter k f).minKey? = some k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.minKey?_alter!_eq_self h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

@[grind =]
theorem minKey?_modify [TransCmp cmp] (h : t.WF) {k f} :
    (Const.modify t k f).minKey? = t.minKey?.map fun km => if cmp km k = .eq then k else km :=
  Impl.Const.minKey?_modify h

@[simp, grind =]
theorem minKey?_modify_eq_minKey? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f} :
    (Const.modify t k f).minKey? = t.minKey? :=
  Impl.Const.minKey?_modify_eq_minKey? h

@[grind =]
theorem isSome_minKey?_modify [TransCmp cmp] {k f} (h : t.WF) :
    (Const.modify t k f).minKey?.isSome = !t.isEmpty :=
  Impl.Const.isSome_minKey?_modify h

theorem isSome_minKey?_modify_eq_isSome [TransCmp cmp] (h : t.WF) {k f} :
    (Const.modify t k f).minKey?.isSome = t.minKey?.isSome :=
  Impl.Const.isSome_minKey?_modify_eq_isSome h

theorem compare_minKey?_modify_eq [TransCmp cmp] (h : t.WF) {k f km kmm} :
    (hkm : t.minKey? = some km) →
    (hkmm : (Const.modify t k f |>.minKey? |>.get <|
        (isSome_minKey?_modify_eq_isSome h).trans <| hkm ▸ Option.isSome_some) = kmm) →
    cmp kmm km = .eq :=
  Impl.Const.compare_minKey?_modify_eq h

theorem minKey?_alter_eq_self [TransCmp cmp] (h : t.WF) {k f} :
    (Const.alter t k f).minKey? = some k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.Const.minKey?_alter!_eq_self h

end Const

theorem minKey?_eq_some_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.minKey? = some t.minKey! :=
  Impl.minKey?_eq_some_minKey! h he (instOrd := ⟨cmp⟩)

theorem minKey!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty) :
    t.minKey! = default :=
  Impl.minKey!_eq_default h he (instOrd := ⟨cmp⟩)

theorem minKey!_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.minKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  Impl.minKey!_eq_iff_getKey?_eq_self_and_forall h he

theorem minKey!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.minKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  Impl.minKey!_eq_iff_mem_and_forall h he

@[grind =]
theorem minKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    (t.insert k v).minKey! =
      (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  Impl.minKey!_insert! h

theorem minKey!_insert_le_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false)
    {k v} :
    cmp (t.insert k v).minKey! t.minKey! |>.isLE :=
  Impl.minKey!_insert!_le_minKey! h he (instOrd := ⟨cmp⟩)

theorem minKey!_insert_le_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    cmp (t.insert k v).minKey! k |>.isLE :=
  Impl.minKey!_insert!_le_self h (instOrd := ⟨cmp⟩)

@[grind =]
theorem contains_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.contains t.minKey! :=
  Impl.contains_minKey! h he

@[grind]
theorem minKey!_mem [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.minKey! ∈ t :=
  Impl.minKey!_mem h he

theorem minKey!_le_of_contains [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : t.contains k) :
    cmp t.minKey! k |>.isLE :=
  Impl.minKey!_le_of_contains h hc

theorem minKey!_le_of_mem [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : k ∈ t) :
    cmp t.minKey! k |>.isLE :=
  Impl.minKey!_le_of_mem h hc

theorem le_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {k} :
    (cmp k t.minKey!).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  Impl.le_minKey! h he (instOrd := ⟨cmp⟩)

theorem getKey?_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.getKey? t.minKey! = some t.minKey! :=
  Impl.getKey?_minKey! h he

theorem getKey_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {hc} :
    t.getKey t.minKey! hc = t.minKey! :=
  Impl.getKey_minKey! h

theorem getKey!_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.getKey! t.minKey! = t.minKey! :=
  Impl.getKey!_minKey! h he

theorem getKeyD_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKeyD t.minKey! fallback = t.minKey! :=
  Impl.getKeyD_minKey! h he

theorem minKey!_erase_eq_of_not_compare_minKey!_eq [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k t.minKey! = .eq) :
    (t.erase k).minKey! = t.minKey! :=
  Impl.minKey!_erase!_eq_of_not_compare_minKey!_eq h he heq

theorem minKey!_le_minKey!_erase [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) :
    cmp t.minKey! (t.erase k).minKey! |>.isLE :=
  Impl.minKey!_le_minKey!_erase! h he

@[grind =]
theorem minKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    (t.insertIfNew k v).minKey! =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  Impl.minKey!_insertIfNew! h

theorem minKey!_insertIfNew_le_minKey! [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {k v} :
    cmp (t.insertIfNew k v).minKey! t.minKey! |>.isLE :=
  Impl.minKey!_insertIfNew!_le_minKey! h he (instOrd := ⟨cmp⟩)

theorem minKey!_insertIfNew_le_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    cmp (t.insertIfNew k v).minKey! k |>.isLE :=
  Impl.minKey!_insertIfNew!_le_self h (instOrd := ⟨cmp⟩)

@[grind =_]
theorem minKey!_eq_head!_keys [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.minKey! = t.keys.head! :=
  Impl.minKey!_eq_head!_keys h (instOrd := ⟨cmp⟩)

@[simp]
theorem minKey!_modify [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k f} :
    (t.modify k f).minKey! = t.minKey! :=
  Impl.minKey!_modify h

theorem minKey!_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k f}
    (he : (t.alter k f).isEmpty = false) :
    (t.alter k f).minKey! = k ↔ (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.minKey!_alter!_eq_self h he

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem minKey!_modify [TransCmp cmp] [Inhabited α] (h : t.WF) {k f}
    (he : (modify t k f).isEmpty = false) :
    (modify t k f).minKey! = if cmp t.minKey! k = .eq then k else t.minKey! :=
  Impl.Const.minKey!_modify h he

@[simp]
theorem minKey!_modify_eq_minKey! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k f} :
    (modify t k f).minKey! = t.minKey! :=
  Impl.Const.minKey!_modify_eq_minKey! h

theorem compare_minKey!_modify_eq [TransCmp cmp] [Inhabited α] (h : t.WF) {k f} :
    cmp (modify t k f).minKey! t.minKey! = .eq :=
  Impl.Const.compare_minKey!_modify_eq h (instOrd := ⟨cmp⟩)

@[simp]
theorem ordCompare_minKey!_modify_eq [Ord α] [TransOrd α] {t : Raw α β} [Inhabited α] (h : t.WF)
    {k f} :
    compare (modify t k f).minKey! t.minKey! = .eq :=
  compare_minKey!_modify_eq h

theorem minKey!_alter_eq_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k f}
    (he : (alter t k f).isEmpty = false) :
    (alter t k f).minKey! = k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.Const.minKey!_alter!_eq_self h he

end Const

theorem minKey?_eq_some_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.minKey? = some (t.minKeyD fallback) :=
  Impl.minKey?_eq_some_minKeyD h he (instOrd := ⟨cmp⟩)

theorem minKeyD_eq_fallback [TransCmp cmp] (h : t.WF) (he : t.isEmpty) {fallback} :
    t.minKeyD fallback = fallback :=
  Impl.minKeyD_eq_fallback h he (instOrd := ⟨cmp⟩)

theorem minKey!_eq_minKeyD_default [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.minKey! = t.minKeyD default :=
  Impl.minKey!_eq_minKeyD_default h (instOrd := ⟨cmp⟩)

theorem minKeyD_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.minKeyD fallback = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  Impl.minKeyD_eq_iff_getKey?_eq_self_and_forall h he

theorem minKeyD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.minKeyD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp km k).isLE :=
  Impl.minKeyD_eq_iff_mem_and_forall h he

@[grind =]
theorem minKeyD_insert [TransCmp cmp] (h : t.WF) {k v fallback} :
    (t.insert k v |>.minKeyD fallback) =
      (t.minKey?.elim k fun k' => if cmp k k' |>.isLE then k else k') :=
  Impl.minKeyD_insert! h

theorem minKeyD_insert_le_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false)
    {k v fallback} :
    cmp (t.insert k v |>.minKeyD fallback) (t.minKeyD fallback) |>.isLE :=
  Impl.minKeyD_insert!_le_minKeyD h he (instOrd := ⟨cmp⟩)

theorem minKeyD_insert_le_self [TransCmp cmp] (h : t.WF) {k v fallback} :
    cmp (t.insert k v |>.minKeyD fallback) k |>.isLE :=
  Impl.minKeyD_insert!_le_self h (instOrd := ⟨cmp⟩)

theorem contains_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.contains (t.minKeyD fallback) :=
  Impl.contains_minKeyD h he

theorem minKeyD_mem [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.minKeyD fallback ∈ t :=
  Impl.minKeyD_mem h he

theorem minKeyD_le_of_contains [TransCmp cmp] (h : t.WF) {k} (hc : t.contains k) {fallback} :
    cmp (t.minKeyD fallback) k |>.isLE :=
  Impl.minKeyD_le_of_contains h hc

theorem minKeyD_le_of_mem [TransCmp cmp] (h : t.WF) {k} (hc : k ∈ t) {fallback} :
    cmp (t.minKeyD fallback) k |>.isLE :=
  Impl.minKeyD_le_of_mem h hc

theorem le_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {k fallback} :
    (cmp k (t.minKeyD fallback)).isLE ↔ (∀ k', k' ∈ t → (cmp k k').isLE) :=
  Impl.le_minKeyD h he (instOrd := ⟨cmp⟩)

theorem getKey?_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKey? (t.minKeyD fallback) = some (t.minKeyD fallback) :=
  Impl.getKey?_minKeyD h he

theorem getKey_minKeyD [TransCmp cmp] (h : t.WF) {fallback hc} :
    t.getKey (t.minKeyD fallback) hc = t.minKeyD fallback :=
  Impl.getKey_minKeyD h

theorem getKey!_minKeyD [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKey! (t.minKeyD fallback) = t.minKeyD fallback :=
  Impl.getKey!_minKeyD h he

theorem getKeyD_minKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback fallback'} :
    t.getKeyD (t.minKeyD fallback) fallback' = t.minKeyD fallback :=
  Impl.getKeyD_minKeyD h he

theorem minKeyD_erase_eq_of_not_compare_minKeyD_eq [TransCmp cmp] (h : t.WF) {k fallback}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k (t.minKeyD fallback) = .eq) :
    (t.erase k |>.minKeyD fallback) = t.minKeyD fallback :=
  Impl.minKeyD_erase!_eq_of_not_compare_minKeyD_eq h he heq

theorem minKeyD_le_minKeyD_erase [TransCmp cmp] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) {fallback} :
    cmp (t.minKeyD fallback) (t.erase k |>.minKeyD fallback) |>.isLE :=
  Impl.minKeyD_le_minKeyD_erase! h he

@[grind =]
theorem minKeyD_insertIfNew [TransCmp cmp] (h : t.WF) {k v fallback} :
    (t.insertIfNew k v |>.minKeyD fallback) =
      t.minKey?.elim k fun k' => if cmp k k' = .lt then k else k' :=
  Impl.minKeyD_insertIfNew! h

theorem minKeyD_insertIfNew_le_minKeyD [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {k v fallback} :
    cmp (t.insertIfNew k v |>.minKeyD fallback) (t.minKeyD fallback) |>.isLE :=
  Impl.minKeyD_insertIfNew!_le_minKeyD h he (instOrd := ⟨cmp⟩)

theorem minKeyD_insertIfNew_le_self [TransCmp cmp] (h : t.WF) {k v fallback} :
    cmp (t.insertIfNew k v |>.minKeyD fallback) k |>.isLE :=
  Impl.minKeyD_insertIfNew!_le_self h (instOrd := ⟨cmp⟩)

theorem minKeyD_eq_headD_keys [TransCmp cmp] (h : t.WF) {fallback} :
    t.minKeyD fallback = t.keys.headD fallback :=
  Impl.minKeyD_eq_headD_keys h (instOrd := ⟨cmp⟩)

@[simp, grind =]
theorem minKeyD_modify [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f fallback} :
    (t.modify k f |>.minKeyD fallback) = t.minKeyD fallback :=
  Impl.minKeyD_modify h

theorem minKeyD_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f}
    (he : (t.alter k f).isEmpty = false) {fallback} :
    (t.alter k f |>.minKeyD fallback) = k ↔ (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.minKeyD_alter!_eq_self h he

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem minKeyD_modify [TransCmp cmp] (h : t.WF) {k f}
    (he : (modify t k f).isEmpty = false) {fallback} :
    (modify t k f |>.minKeyD fallback) =
      if cmp (t.minKeyD fallback) k = .eq then k else (t.minKeyD fallback) :=
  Impl.Const.minKeyD_modify h he

@[simp, grind =]
theorem minKeyD_modify_eq_minKeyD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f fallback} :
    (modify t k f |>.minKeyD fallback) = t.minKeyD fallback :=
  Impl.Const.minKeyD_modify_eq_minKeyD h

theorem compare_minKeyD_modify_eq [TransCmp cmp] (h : t.WF) {k f fallback} :
    cmp (modify t k f |>.minKeyD fallback) (t.minKeyD fallback) = .eq :=
  Impl.Const.compare_minKeyD_modify_eq h (instOrd := ⟨cmp⟩)

@[simp]
theorem ordCompare_minKeyD_modify_eq [Ord α] [TransOrd α] {t : Raw α β} (h : t.WF) {k f fallback} :
    compare (modify t k f |>.minKeyD fallback) (t.minKeyD fallback) = .eq :=
  compare_minKeyD_modify_eq h

theorem minKeyD_alter_eq_self [TransCmp cmp] (h : t.WF) {k f}
    (he : (alter t k f).isEmpty = false) {fallback} :
    (alter t k f |>.minKeyD fallback) = k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k k').isLE :=
  Impl.Const.minKeyD_alter!_eq_self h he

end Const

end Min

section Max

@[simp, grind =]
theorem maxKey?_emptyc :
    (∅ : Raw α β cmp).maxKey? = none :=
  Impl.maxKey?_empty

theorem maxKey?_of_isEmpty [TransCmp cmp] (h : t.WF) :
    (he : t.isEmpty) → t.maxKey? = none :=
  Impl.maxKey?_of_isEmpty h (instOrd := ⟨cmp⟩)

@[simp, grind =]
theorem maxKey?_eq_none_iff [TransCmp cmp] (h : t.WF) :
    t.maxKey? = none ↔ t.isEmpty :=
  Impl.maxKey?_eq_none_iff h (instOrd := ⟨cmp⟩)

theorem maxKey?_eq_some_iff_getKey?_eq_self_and_forall [TransCmp cmp] (h : t.WF) {km} :
    t.maxKey? = some km ↔ t.getKey? km = some km ∧ ∀ k ∈ t, (cmp k km).isLE :=
  Impl.maxKey?_eq_some_iff_getKey?_eq_self_and_forall h

theorem maxKey?_eq_some_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {km} :
    t.maxKey? = some km ↔ km ∈ t ∧ ∀ k ∈ t, (cmp k km).isLE :=
  Impl.maxKey?_eq_some_iff_mem_and_forall h

@[simp, grind =]
theorem isNone_maxKey?_eq_isEmpty [TransCmp cmp] (h : t.WF) :
    t.maxKey?.isNone = t.isEmpty :=
  Impl.isNone_maxKey?_eq_isEmpty h (instOrd := ⟨cmp⟩)

@[simp]
theorem isSome_maxKey?_eq_not_isEmpty [TransCmp cmp] (h : t.WF) :
    t.maxKey?.isSome = !t.isEmpty :=
  Impl.isSome_maxKey?_eq_not_isEmpty h (instOrd := ⟨cmp⟩)

theorem isSome_maxKey?_iff_isEmpty_eq_false [TransCmp cmp] (h : t.WF) :
    t.maxKey?.isSome ↔ t.isEmpty = false :=
  Impl.isSome_maxKey?_iff_isEmpty_eq_false h (instOrd := ⟨cmp⟩)

@[grind =]
theorem maxKey?_insert [TransCmp cmp] (h : t.WF) {k v} :
    (t.insert k v).maxKey? =
      some (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  Impl.maxKey?_insert! h

@[grind =]
theorem isSome_maxKey?_insert [TransCmp cmp] (h : t.WF) {k v} :
    (t.insert k v).maxKey?.isSome :=
  Impl.isSome_maxKey?_insert! h

theorem maxKey?_le_maxKey?_insert [TransCmp cmp] (h : t.WF) {k v km kmi} :
    (hkm : t.maxKey? = some km) →
    (hkmi : (t.insert k v |>.maxKey? |>.get <| isSome_maxKey?_insert h) = kmi) →
    cmp km kmi |>.isLE :=
  Impl.maxKey?_le_maxKey?_insert! h

theorem self_le_maxKey?_insert [TransCmp cmp] (h : t.WF) {k v kmi} :
    (hkmi : (t.insert k v |>.maxKey?.get <| isSome_maxKey?_insert h) = kmi) →
    cmp k kmi |>.isLE :=
  Impl.self_le_maxKey?_insert! h

theorem contains_maxKey? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.maxKey? = some km) →
    t.contains km :=
  Impl.contains_maxKey? h

theorem maxKey?_mem [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.maxKey? = some km) →
    km ∈ t:=
  Impl.maxKey?_mem h

theorem isSome_maxKey?_of_contains [TransCmp cmp] (h : t.WF) {k} :
    (hc : t.contains k) → t.maxKey?.isSome :=
  Impl.isSome_maxKey?_of_contains h

theorem isSome_maxKey?_of_mem [TransCmp cmp] (h : t.WF) {k} :
    k ∈ t → t.maxKey?.isSome :=
  Impl.isSome_maxKey?_of_mem h

theorem le_maxKey?_of_contains [TransCmp cmp] (h : t.WF) {k km} :
    (hc : t.contains k) → (hkm : (t.maxKey?.get <| isSome_maxKey?_of_contains h hc) = km) →
    cmp k km |>.isLE :=
  Impl.le_maxKey?_of_contains h

theorem le_maxKey?_of_mem [TransCmp cmp] (h : t.WF) {k km} :
    (hc : k ∈ t) → (hkm : (t.maxKey?.get <| isSome_maxKey?_of_mem h hc) = km) →
    cmp k km |>.isLE :=
  Impl.le_maxKey?_of_mem h

theorem maxKey?_le [TransCmp cmp] {k} (h : t.WF) :
    (∀ k', t.maxKey? = some k' → (cmp k' k).isLE) ↔
      (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  Impl.maxKey?_le h (instOrd := ⟨cmp⟩)

theorem getKey?_maxKey? [TransCmp cmp] (h : t.WF) {km} :
    (hkm : t.maxKey? = some km) → t.getKey? km = some km :=
  Impl.getKey?_maxKey? h

theorem getKey_maxKey? [TransCmp cmp] (h : t.WF) {km hc} :
    (hkm : t.maxKey?.get (isSome_maxKey?_of_contains h hc) = km) → t.getKey km hc = km :=
  Impl.getKey_maxKey? h

theorem getKey!_maxKey? [TransCmp cmp] [Inhabited α] (h : t.WF) {km} :
    (hkm : t.maxKey? = some km) → t.getKey! km = km :=
  Impl.getKey!_maxKey? h

theorem getKeyD_maxKey? [TransCmp cmp] (h : t.WF) {km fallback} :
    (hkm : t.maxKey? = some km) → t.getKeyD km fallback = km :=
  Impl.getKeyD_maxKey? h

@[simp]
theorem maxKey?_bind_getKey? [TransCmp cmp] (h : t.WF) :
    t.maxKey?.bind t.getKey? = t.maxKey? :=
  Impl.maxKey?_bind_getKey? h

theorem maxKey?_erase_eq_iff_not_compare_eq_maxKey? [TransCmp cmp] (h : t.WF) {k} :
    (t.erase k |>.maxKey?) = t.maxKey? ↔
      ∀ {km}, t.maxKey? = some km → ¬ cmp k km = .eq :=
  Impl.maxKey?_erase!_eq_iff_not_compare_eq_maxKey? h

theorem maxKey?_erase_eq_of_not_compare_eq_maxKey? [TransCmp cmp] (h : t.WF) {k} :
    (hc : ∀ {km}, t.maxKey? = some km → ¬ cmp k km = .eq) →
    (t.erase k |>.maxKey?) = t.maxKey? :=
  Impl.maxKey?_erase!_eq_of_not_compare_eq_maxKey? h (instOrd := ⟨cmp⟩)

theorem isSome_maxKey?_of_isSome_maxKey?_erase [TransCmp cmp] (h : t.WF) {k} :
    (hs : t.erase k |>.maxKey?.isSome) →
    t.maxKey?.isSome :=
  Impl.isSome_maxKey?_of_isSome_maxKey?_erase! h

theorem maxKey?_erase_le_maxKey? [TransCmp cmp] (h : t.WF) {k km kme} :
    (hkme : (t.erase k |>.maxKey?) = some kme) →
    (hkm : (t.maxKey?.get <|
      isSome_maxKey?_of_isSome_maxKey?_erase h <| hkme ▸ Option.isSome_some) = km) →
    cmp kme km |>.isLE :=
  Impl.maxKey?_erase!_le_maxKey? h

@[grind =]
theorem maxKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v} :
    (t.insertIfNew k v).maxKey? =
      some (t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k') :=
  Impl.maxKey?_insertIfNew! h

@[grind =]
theorem isSome_maxKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v} :
    (t.insertIfNew k v).maxKey?.isSome :=
  Impl.isSome_maxKey?_insertIfNew! h

theorem maxKey?_le_maxKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v km kmi} :
    (hkm : t.maxKey? = some km) →
    (hkmi : (t.insertIfNew k v |>.maxKey? |>.get <| isSome_maxKey?_insertIfNew h) = kmi) →
    cmp km kmi |>.isLE :=
  Impl.maxKey?_le_maxKey?_insertIfNew! h

theorem self_le_maxKey?_insertIfNew [TransCmp cmp] (h : t.WF) {k v kmi} :
    (hkmi : (t.insertIfNew k v |>.maxKey?.get <| isSome_maxKey?_insertIfNew h) = kmi) →
    cmp k kmi |>.isLE :=
  Impl.self_le_maxKey?_insertIfNew! h

@[grind =_]
theorem maxKey?_eq_getLast?_keys [TransCmp cmp] (h : t.WF) :
    t.maxKey? = t.keys.getLast? :=
  Impl.maxKey?_eq_getLast?_keys h (instOrd := ⟨cmp⟩)

@[simp, grind =]
theorem maxKey?_modify [TransCmp cmp] [LawfulEqCmp cmp] {k f} (h : t.WF) :
    (t.modify k f).maxKey? = t.maxKey? :=
  Impl.maxKey?_modify h

theorem maxKey?_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f} :
    (t.alter k f).maxKey? = some k ↔
      (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  Impl.maxKey?_alter!_eq_self h

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem maxKey?_modify [TransCmp cmp] (h : t.WF) {k f} :
    (Const.modify t k f).maxKey? = t.maxKey?.map fun km => if cmp km k = .eq then k else km :=
  Impl.Const.maxKey?_modify h

@[simp, grind =]
theorem maxKey?_modify_eq_maxKey? [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f} :
    (Const.modify t k f).maxKey? = t.maxKey? :=
  Impl.Const.maxKey?_modify_eq_maxKey? h

theorem isSome_maxKey?_modify [TransCmp cmp] {k f} (h : t.WF) :
    (Const.modify t k f).maxKey?.isSome = !t.isEmpty :=
  Impl.Const.isSome_maxKey?_modify h

theorem isSome_maxKey?_modify_eq_isSome [TransCmp cmp] (h : t.WF) {k f} :
    (Const.modify t k f).maxKey?.isSome = t.maxKey?.isSome :=
  Impl.Const.isSome_maxKey?_modify_eq_isSome h

theorem compare_maxKey?_modify_eq [TransCmp cmp] (h : t.WF) {k f km kmm} :
    (hkm : t.maxKey? = some km) →
    (hkmm : (Const.modify t k f |>.maxKey? |>.get <|
        (isSome_maxKey?_modify_eq_isSome h).trans <| hkm ▸ Option.isSome_some) = kmm) →
    cmp kmm km = .eq :=
  Impl.Const.compare_maxKey?_modify_eq h

theorem maxKey?_alter_eq_self [TransCmp cmp] (h : t.WF) {k f} :
    (Const.alter t k f).maxKey? = some k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  Impl.Const.maxKey?_alter!_eq_self h

end Const

theorem maxKey?_eq_some_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.maxKey? = some t.maxKey! :=
  Impl.maxKey?_eq_some_maxKey! h he (instOrd := ⟨cmp⟩)

theorem maxKey!_eq_default [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty) :
    t.maxKey! = default :=
  Impl.maxKey!_eq_default h he (instOrd := ⟨cmp⟩)

theorem maxKey!_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.maxKey! = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  Impl.maxKey!_eq_iff_getKey?_eq_self_and_forall h he

theorem maxKey!_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {km} :
    t.maxKey! = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  Impl.maxKey!_eq_iff_mem_and_forall h he

@[grind =]
theorem maxKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    (t.insert k v).maxKey! =
      (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  Impl.maxKey!_insert! h

theorem maxKey!_le_maxKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false)
    {k v} :
    cmp t.maxKey! (t.insert k v).maxKey! |>.isLE :=
  Impl.maxKey!_le_maxKey!_insert! h he (instOrd := ⟨cmp⟩)

theorem self_le_maxKey!_insert [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    cmp k (t.insert k v).maxKey! |>.isLE :=
  Impl.self_le_maxKey!_insert! h (instOrd := ⟨cmp⟩)

@[grind =]
theorem contains_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.contains t.maxKey! :=
  Impl.contains_maxKey! h he

@[grind]
theorem maxKey!_mem [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.maxKey! ∈ t :=
  Impl.maxKey!_mem h he

theorem le_maxKey!_of_contains [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : t.contains k) :
    cmp k t.maxKey! |>.isLE :=
  Impl.le_maxKey!_of_contains h hc

theorem le_maxKey!_of_mem [TransCmp cmp] [Inhabited α] (h : t.WF) {k} (hc : k ∈ t) :
    cmp k t.maxKey! |>.isLE :=
  Impl.le_maxKey!_of_mem h hc

theorem maxKey!_le [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {k} :
    (cmp t.maxKey! k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  Impl.maxKey!_le h he (instOrd := ⟨cmp⟩)

theorem getKey?_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.getKey? t.maxKey! = some t.maxKey! :=
  Impl.getKey?_maxKey! h he

theorem getKey_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {hc} :
    t.getKey t.maxKey! hc = t.maxKey! :=
  Impl.getKey_maxKey! h

theorem getKey!_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) :
    t.getKey! t.maxKey! = t.maxKey! :=
  Impl.getKey!_maxKey! h he

theorem getKeyD_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKeyD t.maxKey! fallback = t.maxKey! :=
  Impl.getKeyD_maxKey! h he

theorem maxKey!_erase_eq_of_not_compare_maxKey!_eq [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k t.maxKey! = .eq) :
    (t.erase k).maxKey! = t.maxKey! :=
  Impl.maxKey!_erase!_eq_of_not_compare_maxKey!_eq h he heq

theorem maxKey!_erase_le_maxKey! [TransCmp cmp] [Inhabited α] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) :
    cmp (t.erase k).maxKey! t.maxKey! |>.isLE :=
  Impl.maxKey!_erase!_le_maxKey! h he

@[grind =]
theorem maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    (t.insertIfNew k v).maxKey! =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  Impl.maxKey!_insertIfNew! h

theorem maxKey!_le_maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF)
    (he : t.isEmpty = false) {k v} :
    cmp t.maxKey! (t.insertIfNew k v).maxKey! |>.isLE :=
  Impl.maxKey!_le_maxKey!_insertIfNew! h he (instOrd := ⟨cmp⟩)

theorem self_le_maxKey!_insertIfNew [TransCmp cmp] [Inhabited α] (h : t.WF) {k v} :
    cmp k (t.insertIfNew k v).maxKey! |>.isLE :=
  Impl.self_le_maxKey!_insertIfNew! h (instOrd := ⟨cmp⟩)

@[grind =_]
theorem maxKey!_eq_getLast!_keys [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.maxKey! = t.keys.getLast! :=
  Impl.maxKey!_eq_getLast!_keys h (instOrd := ⟨cmp⟩)

@[simp, grind =]
theorem maxKey!_modify [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k f} :
    (t.modify k f).maxKey! = t.maxKey! :=
  Impl.maxKey!_modify h

theorem maxKey!_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k f}
    (he : (t.alter k f).isEmpty = false) :
    (t.alter k f).maxKey! = k ↔ (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  Impl.maxKey!_alter!_eq_self h he

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem maxKey!_modify [TransCmp cmp] [Inhabited α] (h : t.WF) {k f}
    (he : (modify t k f).isEmpty = false) :
    (modify t k f).maxKey! = if cmp t.maxKey! k = .eq then k else t.maxKey! :=
  Impl.Const.maxKey!_modify h he

@[simp, grind =]
theorem maxKey!_modify_eq_maxKey! [TransCmp cmp] [LawfulEqCmp cmp] [Inhabited α] (h : t.WF) {k f} :
    (modify t k f).maxKey! = t.maxKey! :=
  Impl.Const.maxKey!_modify_eq_maxKey! h

theorem compare_maxKey!_modify_eq [TransCmp cmp] [Inhabited α] (h : t.WF) {k f} :
    cmp (modify t k f).maxKey! t.maxKey! = .eq :=
  Impl.Const.compare_maxKey!_modify_eq h (instOrd := ⟨cmp⟩)

@[simp]
theorem ordCompare_maxKey!_modify_eq [Ord α] [TransOrd α] {t : Raw α β} [Inhabited α] (h : t.WF)
    {k f} :
    compare (modify t k f).maxKey! t.maxKey! = .eq :=
  compare_maxKey!_modify_eq h

theorem maxKey!_alter_eq_self [TransCmp cmp] [Inhabited α] (h : t.WF) {k f}
    (he : (alter t k f).isEmpty = false) :
    (alter t k f).maxKey! = k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  Impl.Const.maxKey!_alter!_eq_self h he

end Const

theorem maxKey?_eq_some_maxKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.maxKey? = some (t.maxKeyD fallback) :=
  Impl.maxKey?_eq_some_maxKeyD h he (instOrd := ⟨cmp⟩)

theorem maxKeyD_eq_fallback [TransCmp cmp] (h : t.WF) (he : t.isEmpty) {fallback} :
    t.maxKeyD fallback = fallback :=
  Impl.maxKeyD_eq_fallback h he (instOrd := ⟨cmp⟩)

theorem maxKey!_eq_maxKeyD_default [TransCmp cmp] [Inhabited α] (h : t.WF) :
    t.maxKey! = t.maxKeyD default :=
  Impl.maxKey!_eq_maxKeyD_default h (instOrd := ⟨cmp⟩)

theorem maxKeyD_eq_iff_getKey?_eq_self_and_forall [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.maxKeyD fallback = km ↔ t.getKey? km = some km ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  Impl.maxKeyD_eq_iff_getKey?_eq_self_and_forall h he

theorem maxKeyD_eq_iff_mem_and_forall [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {km fallback} :
    t.maxKeyD fallback = km ↔ km ∈ t ∧ ∀ k, k ∈ t → (cmp k km).isLE :=
  Impl.maxKeyD_eq_iff_mem_and_forall h he

@[grind =]
theorem maxKeyD_insert [TransCmp cmp] (h : t.WF) {k v fallback} :
    (t.insert k v |>.maxKeyD fallback) =
      (t.maxKey?.elim k fun k' => if cmp k' k |>.isLE then k else k') :=
  Impl.maxKeyD_insert! h

theorem maxKeyD_le_maxKeyD_insert [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false)
    {k v fallback} :
    cmp (t.maxKeyD fallback) (t.insert k v |>.maxKeyD fallback) |>.isLE :=
  Impl.maxKeyD_le_maxKeyD_insert! h he (instOrd := ⟨cmp⟩)

theorem self_le_maxKeyD_insert [TransCmp cmp] (h : t.WF) {k v fallback} :
    cmp k (t.insert k v |>.maxKeyD fallback) |>.isLE :=
  Impl.self_le_maxKeyD_insert! h (instOrd := ⟨cmp⟩)

@[grind =]
theorem contains_maxKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.contains (t.maxKeyD fallback) :=
  Impl.contains_maxKeyD h he

@[grind]
theorem maxKeyD_mem [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.maxKeyD fallback ∈ t :=
  Impl.maxKeyD_mem h he

theorem le_maxKeyD_of_contains [TransCmp cmp] (h : t.WF) {k} (hc : t.contains k) {fallback} :
    cmp k (t.maxKeyD fallback) |>.isLE :=
  Impl.le_maxKeyD_of_contains h hc

theorem le_maxKeyD_of_mem [TransCmp cmp] (h : t.WF) {k} (hc : k ∈ t) {fallback} :
    cmp k (t.maxKeyD fallback) |>.isLE :=
  Impl.le_maxKeyD_of_mem h hc

theorem maxKeyD_le [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {k fallback} :
    (cmp (t.maxKeyD fallback) k).isLE ↔ (∀ k', k' ∈ t → (cmp k' k).isLE) :=
  Impl.maxKeyD_le h he (instOrd := ⟨cmp⟩)

theorem getKey?_maxKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKey? (t.maxKeyD fallback) = some (t.maxKeyD fallback) :=
  Impl.getKey?_maxKeyD h he

theorem getKey_maxKeyD [TransCmp cmp] (h : t.WF) {fallback hc} :
    t.getKey (t.maxKeyD fallback) hc = t.maxKeyD fallback :=
  Impl.getKey_maxKeyD h

theorem getKey!_maxKeyD [TransCmp cmp] [Inhabited α] (h : t.WF) (he : t.isEmpty = false) {fallback} :
    t.getKey! (t.maxKeyD fallback) = t.maxKeyD fallback :=
  Impl.getKey!_maxKeyD h he

theorem getKeyD_maxKeyD [TransCmp cmp] (h : t.WF) (he : t.isEmpty = false) {fallback fallback'} :
    t.getKeyD (t.maxKeyD fallback) fallback' = t.maxKeyD fallback :=
  Impl.getKeyD_maxKeyD h he

theorem maxKeyD_erase_eq_of_not_compare_maxKeyD_eq [TransCmp cmp] (h : t.WF) {k fallback}
    (he : (t.erase k).isEmpty = false) (heq : ¬ cmp k (t.maxKeyD fallback) = .eq) :
    (t.erase k |>.maxKeyD fallback) = t.maxKeyD fallback :=
  Impl.maxKeyD_erase!_eq_of_not_compare_maxKeyD_eq h he heq

theorem maxKeyD_erase_le_maxKeyD [TransCmp cmp] (h : t.WF) {k}
    (he : (t.erase k).isEmpty = false) {fallback} :
    cmp (t.erase k |>.maxKeyD fallback) (t.maxKeyD fallback) |>.isLE :=
  Impl.maxKeyD_erase!_le_maxKeyD h he

@[grind =]
theorem maxKeyD_insertIfNew [TransCmp cmp] (h : t.WF) {k v fallback} :
    (t.insertIfNew k v |>.maxKeyD fallback) =
      t.maxKey?.elim k fun k' => if cmp k' k = .lt then k else k' :=
  Impl.maxKeyD_insertIfNew! h

theorem maxKeyD_le_maxKeyD_insertIfNew [TransCmp cmp] (h : t.WF)
    (he : t.isEmpty = false) {k v fallback} :
    cmp (t.maxKeyD fallback) (t.insertIfNew k v |>.maxKeyD fallback) |>.isLE :=
  Impl.maxKeyD_le_maxKeyD_insertIfNew! h he (instOrd := ⟨cmp⟩)

theorem self_le_maxKeyD_insertIfNew [TransCmp cmp] (h : t.WF) {k v fallback} :
    cmp k (t.insertIfNew k v |>.maxKeyD fallback) |>.isLE :=
  Impl.self_le_maxKeyD_insertIfNew! h (instOrd := ⟨cmp⟩)

@[grind =_]
theorem maxKeyD_eq_getLastD_keys [TransCmp cmp] (h : t.WF) {fallback} :
    t.maxKeyD fallback = t.keys.getLastD fallback :=
  Impl.maxKeyD_eq_getLastD_keys h (instOrd := ⟨cmp⟩)

@[simp, grind =]
theorem maxKeyD_modify [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f fallback} :
    (t.modify k f |>.maxKeyD fallback) = t.maxKeyD fallback :=
  Impl.maxKeyD_modify h

theorem maxKeyD_alter_eq_self [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f}
    (he : (t.alter k f).isEmpty = false) {fallback} :
    (t.alter k f |>.maxKeyD fallback) = k ↔ (f (t.get? k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  Impl.maxKeyD_alter!_eq_self h he

namespace Const

variable {β : Type v} {t : Raw α β cmp}

theorem maxKeyD_modify [TransCmp cmp] (h : t.WF) {k f}
    (he : (modify t k f).isEmpty = false) {fallback} :
    (modify t k f |>.maxKeyD fallback) =
      if cmp (t.maxKeyD fallback) k = .eq then k else (t.maxKeyD fallback) :=
  Impl.Const.maxKeyD_modify h he

@[simp, grind =]
theorem maxKeyD_modify_eq_maxKeyD [TransCmp cmp] [LawfulEqCmp cmp] (h : t.WF) {k f fallback} :
    (modify t k f |>.maxKeyD fallback) = t.maxKeyD fallback :=
  Impl.Const.maxKeyD_modify_eq_maxKeyD h

theorem compare_maxKeyD_modify_eq [TransCmp cmp] (h : t.WF) {k f fallback} :
    cmp (modify t k f |>.maxKeyD fallback) (t.maxKeyD fallback) = .eq :=
  Impl.Const.compare_maxKeyD_modify_eq h (instOrd := ⟨cmp⟩)

@[simp]
theorem ordCompare_maxKeyD_modify_eq [Ord α] [TransOrd α] {t : Raw α β} (h : t.WF) {k f fallback} :
    compare (modify t k f |>.maxKeyD fallback) (t.maxKeyD fallback) = .eq :=
  compare_maxKeyD_modify_eq h

theorem maxKeyD_alter_eq_self [TransCmp cmp] (h : t.WF) {k f}
    (he : (alter t k f).isEmpty = false) {fallback} :
    (alter t k f |>.maxKeyD fallback) = k ↔
      (f (Const.get? t k)).isSome ∧ ∀ k', k' ∈ t → (cmp k' k).isLE :=
  Impl.Const.maxKeyD_alter!_eq_self h he

end Const

end Max

namespace Equiv

variable {t₁ t₂ t₃ t₄ : Raw α β cmp} {δ : Type w} {m : Type w → Type w'}

@[refl, simp] theorem rfl : Equiv t t := ⟨.rfl⟩

@[symm] theorem symm : Equiv t₁ t₂ → Equiv t₂ t₁
  | ⟨h⟩ => ⟨h.symm⟩

theorem trans : Equiv t₁ t₂ → Equiv t₂ t₃ → Equiv t₁ t₃
  | ⟨h⟩, ⟨h'⟩ => ⟨h.trans h'⟩

instance instTrans : @Trans (Raw α β cmp) _ _ Equiv Equiv Equiv := ⟨trans⟩

theorem comm : t₁ ~m t₂ ↔ t₂ ~m t₁ := ⟨symm, symm⟩
theorem congr_left (h : t₁ ~m t₂) : t₁ ~m t₃ ↔ t₂ ~m t₃ := ⟨h.symm.trans, h.trans⟩
theorem congr_right (h : t₁ ~m t₂) : t₃ ~m t₁ ↔ t₃ ~m t₂ :=
  ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

-- congruence lemmas

theorem isEmpty_eq (h : t₁ ~m t₂) : t₁.isEmpty = t₂.isEmpty :=
  h.1.isEmpty_eq

theorem contains_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.contains k = t₂.contains k :=
  h.1.contains_eq h₁.1 h₂.1

theorem mem_iff [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    k ∈ t₁ ↔ k ∈ t₂ :=
  h.1.mem_iff h₁.1 h₂.1

theorem size_eq (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.size = t₂.size :=
  h.1.size_eq h₁.1 h₂.1

theorem get?_eq [TransCmp cmp] [LawfulEqCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.get? k = t₂.get? k :=
  h.1.get?_eq h₁.1 h₂.1

theorem get_eq [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {hk : k ∈ t₁} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.get k hk = t₂.get k ((h.mem_iff h₁ h₂).mp hk) :=
  h.1.get_eq h₁.1 h₂.1 hk

theorem get!_eq [TransCmp cmp] [LawfulEqCmp cmp] {k : α} [Inhabited (β k)] (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.get! k = t₂.get! k :=
  h.1.get!_eq h₁.1 h₂.1

theorem getD_eq [TransCmp cmp] [LawfulEqCmp cmp] {k : α} {fallback : β k} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.getD k fallback = t₂.getD k fallback :=
  h.1.getD_eq h₁.1 h₂.1

theorem getKey?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKey? k = t₂.getKey? k :=
  h.1.getKey?_eq h₁.1 h₂.1

theorem getKey_eq [TransCmp cmp] {k : α} {hk : k ∈ t₁} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKey k hk = t₂.getKey k ((h.mem_iff h₁ h₂).mp hk) :=
  h.1.getKey_eq h₁.1 h₂.1 hk

theorem getKey!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKey! k = t₂.getKey! k :=
  h.1.getKey!_eq h₁.1 h₂.1

theorem getKeyD_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyD k fallback = t₂.getKeyD k fallback :=
  h.1.getKeyD_eq h₁.1 h₂.1

theorem toList_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.toList = t₂.toList :=
  h.1.toList_eq h₁.1 h₂.1

theorem toArray_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.toArray = t₂.toArray :=
  h.1.toArray_eq h₁.1 h₂.1

theorem keys_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.keys = t₂.keys :=
  h.1.keys_eq h₁.1 h₂.1

theorem keysArray_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.keysArray = t₂.keysArray :=
  h.1.keysArray_eq h₁.1 h₂.1

theorem foldlM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : δ → (a : α) → β a → m δ}
    {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.foldlM f init = t₂.foldlM f init :=
  h.1.foldlM_eq h₁.1 h₂.1

theorem foldl_eq [TransCmp cmp] {f : δ → (a : α) → β a → δ} {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) :
    t₁.foldl f init = t₂.foldl f init :=
  h.1.foldl_eq h₁.1 h₂.1

theorem foldrM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : (a : α) → β a → δ → m δ}
    {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.foldrM f init = t₂.foldrM f init :=
  h.1.foldrM_eq h₁.1 h₂.1

theorem foldr_eq [TransCmp cmp] {f : (a : α) → β a → δ → δ} {init : δ} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) :
    t₁.foldr f init = t₂.foldr f init :=
  h.1.foldr_eq h₁.1 h₂.1

theorem forIn_eq [TransCmp cmp] [Monad m] [LawfulMonad m]
    {b : δ} {f : (a : α) × β a → δ → m (ForInStep δ)} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    ForIn.forIn t₁ b f = ForIn.forIn t₂ b f :=
  h.1.forIn_eq h₁.1 h₂.1

theorem forM_eq [TransCmp cmp] [Monad m] [LawfulMonad m] {f : (a : α) × β a → m PUnit}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    ForM.forM t₁ f = ForM.forM t₂ f :=
  h.1.forM_eq h₁.1 h₂.1

theorem any_eq [TransCmp cmp] {p : (a : α) → β a → Bool} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.any p = t₂.any p := by
  simp only [any, h.forIn_eq h₁ h₂]

theorem all_eq [TransCmp cmp] {p : (a : α) → β a → Bool} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.all p = t₂.all p := by
  simp only [all, h.forIn_eq h₁ h₂]

theorem minKey?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.minKey? = t₂.minKey? :=
  h.1.minKey?_eq h₁.1 h₂.1

theorem minKey!_eq [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.minKey! = t₂.minKey! :=
  h.1.minKey!_eq h₁.1 h₂.1

theorem minKeyD_eq [TransCmp cmp] {fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.minKeyD fallback = t₂.minKeyD fallback :=
  h.1.minKeyD_eq h₁.1 h₂.1

theorem maxKey?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.maxKey? = t₂.maxKey? :=
  h.1.maxKey?_eq h₁.1 h₂.1

theorem maxKey!_eq [TransCmp cmp] [Inhabited α] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.maxKey! = t₂.maxKey! :=
  h.1.maxKey!_eq h₁.1 h₂.1

theorem maxKeyD_eq [TransCmp cmp] {fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.maxKeyD fallback = t₂.maxKeyD fallback :=
  h.1.maxKeyD_eq h₁.1 h₂.1

theorem minEntry?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.minEntry? = t₂.minEntry? :=
  h.1.minEntry?_eq h₁.1 h₂.1

theorem minEntry!_eq [TransCmp cmp] [Inhabited ((a : α) × β a)] (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.minEntry! = t₂.minEntry! :=
  h.1.minEntry!_eq h₁.1 h₂.1

theorem minEntryD_eq [TransCmp cmp] {fallback : (a : α) × β a} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.minEntryD fallback = t₂.minEntryD fallback :=
  h.1.minEntryD_eq h₁.1 h₂.1

theorem maxEntry?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.maxEntry? = t₂.maxEntry? :=
  h.1.maxEntry?_eq h₁.1 h₂.1

theorem maxEntry!_eq [TransCmp cmp] [Inhabited ((a : α) × β a)] (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.maxEntry! = t₂.maxEntry! :=
  h.1.maxEntry!_eq h₁.1 h₂.1

theorem maxEntryD_eq [TransCmp cmp] {fallback : (a : α) × β a} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.maxEntryD fallback = t₂.maxEntryD fallback :=
  h.1.maxEntryD_eq h₁.1 h₂.1

theorem entryAtIdx?_eq [TransCmp cmp] {i : Nat} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.entryAtIdx? i = t₂.entryAtIdx? i :=
  h.1.entryAtIdx?_eq h₁.1 h₂.1

theorem entryAtIdx!_eq [TransCmp cmp] [Inhabited ((a : α) × β a)] {i : Nat} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.entryAtIdx! i = t₂.entryAtIdx! i :=
  h.1.entryAtIdx!_eq h₁.1 h₂.1

theorem entryAtIdxD_eq [TransCmp cmp] {i : Nat} {fallback : (a : α) × β a} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.entryAtIdxD i fallback = t₂.entryAtIdxD i fallback :=
  h.1.entryAtIdxD_eq h₁.1 h₂.1

theorem keyAtIdx?_eq [TransCmp cmp] {i : Nat} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.keyAtIdx? i = t₂.keyAtIdx? i :=
  h.1.keyAtIdx?_eq h₁.1 h₂.1

theorem keyAtIdx!_eq [TransCmp cmp] [Inhabited α] {i : Nat} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.keyAtIdx! i = t₂.keyAtIdx! i :=
  h.1.keyAtIdx!_eq h₁.1 h₂.1

theorem keyAtIdxD_eq [TransCmp cmp] {i : Nat} {fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.keyAtIdxD i fallback = t₂.keyAtIdxD i fallback :=
  h.1.keyAtIdxD_eq h₁.1 h₂.1

theorem getEntryGE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getEntryGE? k = t₂.getEntryGE? k :=
  h.1.getEntryGE?_eq h₁.1 h₂.1

theorem getEntryGE!_eq [TransCmp cmp] [Inhabited ((a : α) × β a)] {k : α} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.getEntryGE! k = t₂.getEntryGE! k :=
  h.1.getEntryGE!_eq h₁.1 h₂.1

theorem getEntryGED_eq [TransCmp cmp] {k : α} {fallback : (a : α) × β a} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.getEntryGED k fallback = t₂.getEntryGED k fallback :=
  h.1.getEntryGED_eq h₁.1 h₂.1

theorem getEntryGT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getEntryGT? k = t₂.getEntryGT? k :=
  h.1.getEntryGT?_eq h₁.1 h₂.1

theorem getEntryGT!_eq [TransCmp cmp] [Inhabited ((a : α) × β a)] {k : α} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.getEntryGT! k = t₂.getEntryGT! k :=
  h.1.getEntryGT!_eq h₁.1 h₂.1

theorem getEntryGTD_eq [TransCmp cmp] {k : α} {fallback : (a : α) × β a} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.getEntryGTD k fallback = t₂.getEntryGTD k fallback :=
  h.1.getEntryGTD_eq h₁.1 h₂.1

theorem getEntryLE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getEntryLE? k = t₂.getEntryLE? k :=
  h.1.getEntryLE?_eq h₁.1 h₂.1

theorem getEntryLE!_eq [TransCmp cmp] [Inhabited ((a : α) × β a)] {k : α} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.getEntryLE! k = t₂.getEntryLE! k :=
  h.1.getEntryLE!_eq h₁.1 h₂.1

theorem getEntryLED_eq [TransCmp cmp] {k : α} {fallback : (a : α) × β a} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.getEntryLED k fallback = t₂.getEntryLED k fallback :=
  h.1.getEntryLED_eq h₁.1 h₂.1

theorem getEntryLT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getEntryLT? k = t₂.getEntryLT? k :=
  h.1.getEntryLT?_eq h₁.1 h₂.1

theorem getEntryLT!_eq [TransCmp cmp] [Inhabited ((a : α) × β a)] {k : α} (h₁ : t₁.WF)
    (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.getEntryLT! k = t₂.getEntryLT! k :=
  h.1.getEntryLT!_eq h₁.1 h₂.1

theorem getEntryLTD_eq [TransCmp cmp] {k : α} {fallback : (a : α) × β a} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : t₁.getEntryLTD k fallback = t₂.getEntryLTD k fallback :=
  h.1.getEntryLTD_eq h₁.1 h₂.1

theorem getKeyGE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGE? k = t₂.getKeyGE? k :=
  h.1.getKeyGE?_eq h₁.1 h₂.1

theorem getKeyGE!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGE! k = t₂.getKeyGE! k :=
  h.1.getKeyGE!_eq h₁.1 h₂.1

theorem getKeyGED_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGED k fallback = t₂.getKeyGED k fallback :=
  h.1.getKeyGED_eq h₁.1 h₂.1

theorem getKeyGT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGT? k = t₂.getKeyGT? k :=
  h.1.getKeyGT?_eq h₁.1 h₂.1

theorem getKeyGT!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGT! k = t₂.getKeyGT! k :=
  h.1.getKeyGT!_eq h₁.1 h₂.1

theorem getKeyGTD_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyGTD k fallback = t₂.getKeyGTD k fallback :=
  h.1.getKeyGTD_eq h₁.1 h₂.1

theorem getKeyLE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLE? k = t₂.getKeyLE? k :=
  h.1.getKeyLE?_eq h₁.1 h₂.1

theorem getKeyLE!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLE! k = t₂.getKeyLE! k :=
  h.1.getKeyLE!_eq h₁.1 h₂.1

theorem getKeyLED_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLED k fallback = t₂.getKeyLED k fallback :=
  h.1.getKeyLED_eq h₁.1 h₂.1

theorem getKeyLT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLT? k = t₂.getKeyLT? k :=
  h.1.getKeyLT?_eq h₁.1 h₂.1

theorem getKeyLT!_eq [TransCmp cmp] [Inhabited α] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLT! k = t₂.getKeyLT! k :=
  h.1.getKeyLT!_eq h₁.1 h₂.1

theorem getKeyLTD_eq [TransCmp cmp] {k fallback : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.getKeyLTD k fallback = t₂.getKeyLTD k fallback :=
  h.1.getKeyLTD_eq h₁.1 h₂.1

theorem insert [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) (v : β k) : t₁.insert k v ~m t₂.insert k v :=
  ⟨h.1.insert! h₁.1 h₂.1⟩

theorem erase [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) : t₁.erase k ~m t₂.erase k :=
  ⟨h.1.erase! h₁.1 h₂.1⟩

theorem insertIfNew [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) (v : β k) : t₁.insertIfNew k v ~m t₂.insertIfNew k v :=
  ⟨h.1.insertIfNew! h₁.1 h₂.1⟩

theorem alter [TransCmp cmp] [LawfulEqCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) (f : Option (β k) → Option (β k)) :
    t₁.alter k f ~m t₂.alter k f :=
  ⟨h.1.alter! h₁.1 h₂.1⟩

theorem modify [TransCmp cmp] [LawfulEqCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) (f : β k → β k) : t₁.modify k f ~m t₂.modify k f :=
  ⟨h.1.modify h₁.1 h₂.1⟩

theorem filter (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (f : (a : α) → β a → Bool) :
    t₁.filter f ~m t₂.filter f :=
  ⟨h.1.filter! h₁.1 h₂.1⟩

theorem map (h : t₁ ~m t₂) (f : (a : α) → β a → γ a) :
    t₁.map f ~m t₂.map f :=
  ⟨h.1.map⟩

theorem filterMap  (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (f : (a : α) → β a → Option (γ a)) :
    t₁.filterMap f ~m t₂.filterMap f :=
  ⟨h.1.filterMap! h₁.1 h₂.1⟩

theorem insertMany_list [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (l : List ((a : α) × β a)) : t₁.insertMany l ~m t₂.insertMany l :=
  ⟨h.1.insertMany!_list h₁.1 h₂.1⟩

theorem eraseMany_list [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (l : List α) :
    t₁.eraseMany l ~m t₂.eraseMany l :=
  ⟨h.1.eraseMany!_list h₁.1 h₂.1⟩

theorem mergeWith [TransCmp cmp] [LawfulEqCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h₃ : t₃.WF) (h₄ : t₄.WF)
    (f : (a : α) → β a → β a → β a)
    (h : t₁ ~m t₂) (h' : t₃ ~m t₄) :
    t₁.mergeWith f t₃ ~m t₂.mergeWith f t₄ :=
  ⟨h.1.mergeWith! h'.1 h₁.1 h₂.1 h₃.1 h₄.1⟩

section Const

variable {β : Type v} {t₁ t₂ t₃ t₄ : Raw α β cmp} (δ : Type w) (m : Type w → Type w)

theorem constGet?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.get? t₁ k = Const.get? t₂ k :=
  h.1.constGet?_eq h₁.1 h₂.1

theorem constGet_eq [TransCmp cmp] {k : α} {hk : k ∈ t₁} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.get t₁ k hk = Const.get t₂ k ((h.mem_iff h₁ h₂).mp hk) :=
  h.1.constGet_eq h₁.1 h₂.1 hk

theorem constGet!_eq [TransCmp cmp] [Inhabited β] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.get! t₁ k = Const.get! t₂ k :=
  h.1.constGet!_eq h₁.1 h₂.1

theorem constGetD_eq [TransCmp cmp] {k : α} {fallback : β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.getD t₁ k fallback = Const.getD t₂ k fallback :=
  h.1.constGetD_eq h₁.1 h₂.1

theorem constToList_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.toList t₁ = Const.toList t₂ :=
  h.1.constToList_eq h₁.1 h₂.1

theorem constToArray_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.toArray t₁ = Const.toArray t₂ :=
  h.1.constToArray_eq h₁.1 h₂.1

theorem values_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) : t₁.values = t₂.values :=
  h.1.values_eq h₁.1 h₂.1

theorem valuesArray_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    t₁.valuesArray = t₂.valuesArray :=
  h.1.valuesArray_eq h₁.1 h₂.1

theorem constMinEntry?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.minEntry? t₁ = Const.minEntry? t₂ :=
  h.1.constMinEntry?_eq h₁.1 h₂.1

theorem constMinEntry!_eq [TransCmp cmp] [Inhabited (α × β)] (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.minEntry! t₁ = Const.minEntry! t₂ :=
  h.1.constMinEntry!_eq h₁.1 h₂.1

theorem constMinEntryD_eq [TransCmp cmp] {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.minEntryD t₁ fallback = Const.minEntryD t₂ fallback :=
  h.1.constMinEntryD_eq h₁.1 h₂.1

theorem constMaxEntry?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.maxEntry? t₁ = Const.maxEntry? t₂ :=
  h.1.constMaxEntry?_eq h₁.1 h₂.1

theorem constMaxEntry!_eq [TransCmp cmp] [Inhabited (α × β)] (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.maxEntry! t₁ = Const.maxEntry! t₂ :=
  h.1.constMaxEntry!_eq h₁.1 h₂.1

theorem constMaxEntryD_eq [TransCmp cmp] {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.maxEntryD t₁ fallback = Const.maxEntryD t₂ fallback :=
  h.1.constMaxEntryD_eq h₁.1 h₂.1

theorem constEntryAtIdx?_eq [TransCmp cmp] {i : Nat} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.entryAtIdx? t₁ i = Const.entryAtIdx? t₂ i :=
  h.1.constEntryAtIdx?_eq h₁.1 h₂.1

theorem constEntryAtIdx!_eq [TransCmp cmp] [Inhabited (α × β)] {i : Nat} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.entryAtIdx! t₁ i = Const.entryAtIdx! t₂ i :=
  h.1.constEntryAtIdx!_eq h₁.1 h₂.1

theorem constEntryAtIdxD_eq [TransCmp cmp] {i : Nat} {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.entryAtIdxD t₁ i fallback = Const.entryAtIdxD t₂ i fallback :=
  h.1.constEntryAtIdxD_eq h₁.1 h₂.1

theorem constGetEntryGE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.getEntryGE? t₁ k = Const.getEntryGE? t₂ k :=
  h.1.constGetEntryGE?_eq h₁.1 h₂.1

theorem constGetEntryGE!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.getEntryGE! t₁ k = Const.getEntryGE! t₂ k :=
  h.1.constGetEntryGE!_eq h₁.1 h₂.1

theorem constGetEntryGED_eq [TransCmp cmp] {k : α} {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.getEntryGED t₁ k fallback = Const.getEntryGED t₂ k fallback :=
  h.1.constGetEntryGED_eq h₁.1 h₂.1

theorem constGetEntryGT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.getEntryGT? t₁ k = Const.getEntryGT? t₂ k :=
  h.1.constGetEntryGT?_eq h₁.1 h₂.1

theorem constGetEntryGT!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.getEntryGT! t₁ k = Const.getEntryGT! t₂ k :=
  h.1.constGetEntryGT!_eq h₁.1 h₂.1

theorem constGetEntryGTD_eq [TransCmp cmp] {k : α} {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.getEntryGTD t₁ k fallback = Const.getEntryGTD t₂ k fallback :=
  h.1.constGetEntryGTD_eq h₁.1 h₂.1

theorem constGetEntryLE?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.getEntryLE? t₁ k = Const.getEntryLE? t₂ k :=
  h.1.constGetEntryLE?_eq h₁.1 h₂.1

theorem constGetEntryLE!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.getEntryLE! t₁ k = Const.getEntryLE! t₂ k :=
  h.1.constGetEntryLE!_eq h₁.1 h₂.1

theorem constGetEntryLED_eq [TransCmp cmp] {k : α} {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.getEntryLED t₁ k fallback = Const.getEntryLED t₂ k fallback :=
  h.1.constGetEntryLED_eq h₁.1 h₂.1

theorem constGetEntryLT?_eq [TransCmp cmp] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) :
    Const.getEntryLT? t₁ k = Const.getEntryLT? t₂ k :=
  h.1.constGetEntryLT?_eq h₁.1 h₂.1

theorem constGetEntryLT!_eq [TransCmp cmp] [Inhabited (α × β)] {k : α} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.getEntryLT! t₁ k = Const.getEntryLT! t₂ k :=
  h.1.constGetEntryLT!_eq h₁.1 h₂.1

theorem constGetEntryLTD_eq [TransCmp cmp] {k : α} {fallback : α × β} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : t₁ ~m t₂) : Const.getEntryLTD t₁ k fallback = Const.getEntryLTD t₂ k fallback :=
  h.1.constGetEntryLTD_eq h₁.1 h₂.1

theorem constAlter [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) (f : Option β → Option β) :
    Const.alter t₁ k f ~m Const.alter t₂ k f :=
  ⟨h.1.constAlter! h₁.1 h₂.1⟩

theorem constModify [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (k : α) (f : β → β) : Const.modify t₁ k f ~m Const.modify t₂ k f :=
  ⟨h.1.constModify h₁.1 h₂.1⟩

theorem constInsertMany_list [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂)
    (l : List (α × β)) : Const.insertMany t₁ l ~m Const.insertMany t₂ l :=
  ⟨h.1.constInsertMany!_list h₁.1 h₂.1⟩

theorem constInsertManyIfNewUnit_list [TransCmp cmp] {t₁ t₂ : Raw α Unit cmp}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h : t₁ ~m t₂) (l : List α) :
    Const.insertManyIfNewUnit t₁ l ~m Const.insertManyIfNewUnit t₂ l :=
  ⟨h.1.constInsertManyIfNewUnit!_list h₁.1 h₂.1⟩

theorem constMergeWith [TransCmp cmp]
    (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h₃ : t₃.WF) (h₄ : t₄.WF)
    (f : α → β → β → β)
    (h : t₁ ~m t₂) (h' : t₃ ~m t₄) :
    Const.mergeWith f t₁ t₃ ~m Const.mergeWith f t₂ t₄ :=
  ⟨h.1.constMergeWith! h'.1 h₁.1 h₂.1 h₃.1 h₄.1⟩

end Const

-- extensionalities

theorem of_forall_get?_eq [TransCmp cmp] [LawfulEqCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ k, t₁.get? k = t₂.get? k) : t₁ ~m t₂ :=
  ⟨.of_forall_get?_eq h₁.1 h₂.1 h⟩

section Const

variable {β : Type v} {t₁ t₂ : Raw α β cmp}

theorem of_forall_getKey_eq_of_forall_constGet?_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    (hk : ∀ k hk hk', t₁.getKey k hk = t₂.getKey k hk')
    (hv : ∀ k, Const.get? t₁ k = Const.get? t₂ k) : t₁ ~m t₂ :=
  ⟨.of_forall_getKey_eq_of_forall_constGet?_eq h₁.1 h₂.1 hk hv⟩

theorem of_forall_constGet?_eq [TransCmp cmp] [LawfulEqCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ k, Const.get? t₁ k = Const.get? t₂ k) : t₁ ~m t₂ :=
  ⟨.of_forall_constGet?_eq h₁.1 h₂.1 h⟩

theorem of_forall_getKey?_unit_eq [TransCmp cmp] {t₁ t₂ : Raw α Unit cmp}
    (h₁ : t₁.WF) (h₂ : t₂.WF) (h : ∀ k, t₁.getKey? k = t₂.getKey? k) : t₁ ~m t₂ :=
  ⟨.of_forall_getKey?_unit_eq h₁.1 h₂.1 h⟩

theorem of_forall_contains_unit_eq [TransCmp cmp] [LawfulEqCmp cmp]
    {t₁ t₂ : Raw α Unit cmp} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ k, t₁.contains k = t₂.contains k) : t₁ ~m t₂ :=
  ⟨.of_forall_contains_unit_eq h₁.1 h₂.1 h⟩

theorem of_forall_mem_unit_iff [TransCmp cmp] [LawfulEqCmp cmp]
    {t₁ t₂ : Raw α Unit cmp} (h₁ : t₁.WF) (h₂ : t₂.WF)
    (h : ∀ k, k ∈ t₁ ↔ k ∈ t₂) : t₁ ~m t₂ :=
  ⟨.of_forall_mem_unit_iff h₁.1 h₂.1 h⟩

end Const

end Equiv

section Equiv

variable {t₁ t₂ : Raw α β cmp}

private theorem equiv_iff : t₁ ~m t₂ ↔ t₁.1.Equiv t₂.1 :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem equiv_empty_iff_isEmpty : t ~m empty ↔ t.isEmpty :=
  equiv_iff.trans Impl.equiv_empty_iff_isEmpty

theorem empty_equiv_iff_isEmpty : empty ~m t ↔ t.isEmpty :=
  equiv_iff.trans Impl.empty_equiv_iff_isEmpty

theorem equiv_iff_toList_perm : t₁ ~m t₂ ↔ t₁.toList.Perm t₂.toList :=
  equiv_iff.trans Impl.equiv_iff_toList_perm

theorem Equiv.of_toList_perm (h : t₁.toList.Perm t₂.toList) : t₁ ~m t₂ :=
  ⟨.of_toList_perm h⟩

theorem equiv_iff_toList_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) :
    t₁ ~m t₂ ↔ t₁.toList = t₂.toList :=
  equiv_iff.trans (Impl.equiv_iff_toList_eq h₁.1 h₂.1)

section Const

variable {β : Type v} {t₁ t₂ : Raw α β cmp}

theorem Const.equiv_iff_toList_perm : t₁ ~m t₂ ↔ (Const.toList t₁).Perm (Const.toList t₂) :=
  equiv_iff.trans Impl.Const.equiv_iff_toList_perm

theorem Const.equiv_iff_toList_eq [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) :
    t₁ ~m t₂ ↔ Const.toList t₁ = Const.toList t₂ :=
  equiv_iff.trans (Impl.Const.equiv_iff_toList_eq h₁.1 h₂.1)

theorem Const.equiv_iff_keys_unit_perm {t₁ t₂ : Raw α Unit cmp} :
    t₁ ~m t₂ ↔ t₁.keys.Perm t₂.keys :=
  equiv_iff.trans Impl.Const.equiv_iff_keys_perm

theorem Const.equiv_iff_keys_unit_eq {t₁ t₂ : Raw α Unit cmp} [TransCmp cmp] (h₁ : t₁.WF) (h₂ : t₂.WF) :
    t₁ ~m t₂ ↔ t₁.keys = t₂.keys :=
  equiv_iff.trans (Impl.Const.equiv_iff_keys_eq h₁.1 h₂.1)

theorem Equiv.of_constToList_perm : (Const.toList t₁).Perm (Const.toList t₂) → t₁ ~m t₂ :=
  Const.equiv_iff_toList_perm.mpr

theorem Equiv.of_keys_unit_perm {t₁ t₂ : Raw α Unit cmp} : t₁.keys.Perm t₂.keys → t₁ ~m t₂ :=
  Const.equiv_iff_keys_unit_perm.mpr

end Const

end Equiv

end Std.DTreeMap.Raw
