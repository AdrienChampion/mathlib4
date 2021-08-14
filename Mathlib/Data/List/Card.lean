/-
Author: Jeremy Avigad

This is a makeshift theory of the cardinality of a list. Any list can be taken to represent the
finite set of its elements. Cardinality counts the number of distinct elements. Cardinality
respects equivalence and is preserved by any mapping that is injective on its elements.

It might make sense to remove this when we have a proper theory of finite sets.
-/
import Mathlib.Data.List.Basic

namespace List

def disjoint (as bs : List α) := ∀ {x}, x ∈ as → x ∈ bs → False

def inj_on (f : α → β) (as : List α) := ∀ {x y}, x ∈ as → y ∈ as → f x = f y → x = y

theorem inj_on_of_subset {f : α → β} {as bs : List α} (h : inj_on f bs) (hsub : as ⊆ bs) :
  inj_on f as := fun xas yas heq => h (hsub xas) (hsub yas) heq

protected def equiv (as bs : List α) := ∀ x, x ∈ as ↔ x ∈ bs

theorem equiv_iff_subset_and_subset {as bs : List α} : as.equiv bs ↔ as ⊆ bs ∧ bs ⊆ as :=
  ⟨fun h => ⟨fun xas => (h _).1 xas, fun xbs => (h _).2 xbs⟩, fun ⟨h1, h2⟩ x => ⟨h1, h2⟩⟩

theorem insert_equiv_cons [DecidableEq α] (a : α) (as : List α) : (insert a as).equiv (a :: as) :=
  fun x => by simp

theorem union_equiv_append [DecidableEq α] (as bs : List α) : (as.union bs).equiv (as ++ bs) :=
  fun x => by simp

section decidable_eq
variable [DecidableEq α] [DecidableEq β]

/- remove -/

def remove (a : α) : List α → List α
  | [] => []
  | (b :: bs) => if a = b then remove a bs else b :: remove a bs

theorem mem_remove_iff {a b : α} {as : List α} : b ∈ remove a as ↔ b ∈ as ∧ b ≠ a := by
  induction as with
  | nil => simp [remove]
  | cons a' as ih =>
    simp [remove]
    cases Decidable.em (a = a') with
    | inl h =>
      simp [if_pos h, ih]
      exact ⟨fun ⟨h1, h2⟩ => ⟨Or.inr h1, h2⟩, fun ⟨h1, h2⟩ => ⟨Or.resolve_left h1 (h ▸ h2), h2⟩⟩
    | inr h =>
      simp [if_neg h, ih]
      split
        focus
        intro h'
        cases h' with
        | inl h₁ => exact ⟨Or.inl h₁, h₁.symm ▸ (Ne.symm h)⟩
        | inr h₁ => exact ⟨Or.inr h₁.1, h₁.2⟩
      intro ⟨h1, h2⟩
      cases h1 with
      | inl h1' => exact Or.inl h1'
      | inr h1' => exact Or.inr ⟨h1', h2⟩

theorem remove_eq_of_not_mem {a : α} : ∀ {as : List α}, (a ∉ as) → remove a as = as
  | [], _ => by simp [remove]
  | a' :: as, h => by
    have h1 : a ≠ a' := fun h' => h (by rw [h']; apply mem_cons_self)
    have h2 : a ∉ as := fun h' => h (mem_cons_of_mem _ h')
    simp [remove, h1, remove_eq_of_not_mem h2]

theorem mem_of_mem_remove {a b : α} {as : List α} (h : b ∈ remove a as) : b ∈ as := by
  rw [mem_remove_iff] at h; exact h.1

/- card -/

def card : List α → Nat
  | [] => 0
  | a :: as => if a ∈ as then card as else card as + 1

@[simp] theorem card_nil : card ([] : List α) = 0 := rfl

@[simp] theorem card_cons_of_mem {a : α} {as : List α} (h : a ∈ as) :
    card (a :: as) = card as := by simp [card]; rw [if_pos h]

@[simp] theorem card_cons_of_not_mem {a : α} {as : List α} (h : a ∉ as) :
    card (a :: as) = card as + 1 := by simp [card]; rw [if_neg h]

theorem card_le_card_cons (a : α) (as : List α) : card as ≤ card (a :: as) := by
  cases Decidable.em (a ∈ as) with
  | inl h => simp [h, Nat.le_refl]
  | inr h => simp [h, Nat.le_succ]

@[simp] theorem card_insert_of_mem {a : α} {as : List α} (h : a ∈ as) :
    card (insert a as) = card as := by simp [h]

@[simp] theorem card_insert_of_not_mem {a : α} {as : List α} (h : a ∉ as) :
    card (insert a as) = card as + 1 := by simp [h]

theorem card_remove_of_mem {a : α} : ∀ {as : List α}, a ∈ as → card as = card (remove a as) + 1
  | [], h => False.elim (not_mem_nil _ h)
  | (a' :: as), h => by
    cases Decidable.em (a = a') with
    | inl h' =>
      simp [remove, if_pos h']
      cases Decidable.em (a ∈ as) with
      | inl h'' =>
        have h₃ : a' ∈ as := h' ▸ h''
        simp [card_remove_of_mem h'', h₃]
      | inr h'' =>
        have h₃ : a' ∉ as := h' ▸ h''
        simp [card_cons_of_not_mem h₃, remove_eq_of_not_mem h'']
    | inr h' =>
        have h₃ : a ∈ as := Or.resolve_left h h'
        simp [remove, h']
        cases Decidable.em (a' ∈ as) with
        | inl h'' =>
          have : a' ∈ remove a as := by rw [mem_remove_iff]; exact ⟨h'', Ne.symm h'⟩
          simp [h'', this, card_remove_of_mem h₃]
        | inr h'' =>
          have : a' ∉ remove a as := fun h => h'' (mem_of_mem_remove h)
          simp [h'', this, card_remove_of_mem h₃]

theorem card_subset_le : ∀ {as bs : List α}, as ⊆ bs → card as ≤ card bs
  | [], bs, _ => by simp; apply Nat.zero_le
  | (a :: as), bs, hsub => by
    cases Decidable.em (a ∈ as) with
    | inl h' =>
      have hsub' : as ⊆ bs := fun xmem => hsub (mem_cons_of_mem a xmem)
      simp [h', card_subset_le hsub']
    | inr h' =>
      have : a ∈ bs := hsub (Or.inl rfl)
      simp [h', card_remove_of_mem this]
      apply Nat.add_le_add_right
      apply card_subset_le
      intro x xmem
      rw [mem_remove_iff]
      exact ⟨hsub (mem_cons_of_mem _ xmem), fun h => h' (h ▸ xmem)⟩

theorem card_map_le (f : α → β) (as : List α) : card (as.map f) ≤ card as := by
  induction as with
  | nil => simp
  | cons a as ih =>
    cases Decidable.em (f a ∈ map f as) with
    | inl h => simp [h]; apply Nat.le_trans ih (card_le_card_cons ..)
    | inr h =>
      have : a ∉ as := fun h'' => h (mem_map_of_mem _ h'')
      simp [h, this]
      exact Nat.add_le_add_right ih _

theorem card_map_eq_of_inj_on {f : α → β} {as : List α} :
    inj_on f as →  card (as.map f) = card as := by
  induction as with
  | nil => simp
  | cons a as ih =>
    cases Decidable.em (f a ∈ map f as) with
    | inl h =>
      intro inj_on'
      cases (exists_of_mem_map h) with
      | intro x hx =>
        have : x = a := inj_on' (mem_cons_of_mem _ hx.1) (mem_cons_self ..) hx.2
        have h1 : a ∈ as := this ▸ hx.1
        have h2 : inj_on f as := inj_on_of_subset inj_on' (subset_cons _ _)
        simp  [h1, mem_map_of_mem f h1, ih h2]
    | inr h =>
      intro inj_on'
      have h1 : a ∉ as := fun h'' => h (mem_map_of_mem _ h'')
      have h2 : inj_on f as := inj_on_of_subset inj_on' (subset_cons _ _)
      simp [h, h1, ih h2]

theorem card_eq_of_equiv {as bs : List α} (h : as.equiv bs) : card as = card bs :=
  let sub_and_sub := equiv_iff_subset_and_subset.1 h
  Nat.le_antisymm (card_subset_le sub_and_sub.1) (card_subset_le sub_and_sub.2)

theorem card_append_disjoint : ∀ {as bs : List α},
    disjoint as bs → card (as ++ bs) = card as + card bs
  | [], bs, disj => by simp
  | a :: as, bs, disj => by
    have disj' : disjoint as bs := fun h1 h2 => disj (mem_cons_of_mem a h1) h2
    cases Decidable.em (a ∈ as) with
    | inl h =>
      simp [h, card_append_disjoint disj']
    | inr h =>
      have h1 : a ∉ bs := fun h' => disj (mem_cons_self a as) h'
      simp [h, h1, card_append_disjoint disj', Nat.add_right_comm]

theorem card_union_disjoint {as bs : List α} (h : disjoint as bs) :
    card (as.union bs) = card as + card bs := by
  rw [card_eq_of_equiv (union_equiv_append as bs), card_append_disjoint h]

end decidable_eq

end List
