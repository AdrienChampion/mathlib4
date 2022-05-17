/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Data.List.Lemmas
import Init.Data.Nat.Basic
import Mathlib.Data.FStream.Defs

/-!
# Lemmas over Streams

This file is mostly composed of lemmas over `FStream`'s basic operations and a few type classes
instantiations such as `Inhabited`.


## Notable Definitions and Lemmas

- `FStream.ext`: stream extensionality, lifted directly from functional extensionality.
- `FStream.eq_of_bisim`: proves stream equality from a bisimulation relation.
- `FStream.coinduction`: proves stream equality from
  - head equality, and
  - for any stream of functions `fr` over the elements, `fr`-mapped stream equality implies
    `fr`-mapped tail equality.


## File History

This file used to be in the Lean 3 core library. It was moved to `mathlib` and renamed to
[mathlib/data/stream/init.lean][init] to avoid name clashes. It was rewritten for Lean 4 and renamed
to `MathLib/data/FStream/Lemma.lean` to better  `String`) rewrite.

[init]: https://github.com/leanprover-community/mathlib/tree/master/src/data/stream/init.lean
-/

open FStream.Notation

universe u v w

variable
  {α : Type u}
  {β : Type v}
  {δ : Type w}

instance [inst : Inhabited α] : Inhabited (FStream α) where
  default :=
    FStream.const inst.default

namespace FStream

@[ext]
protected partial def ext
  {s₁ s₂ : FStream α}
  : (∀ (n : ℕ), s₁.nth n = s₂.nth n) → s₁ = s₂
:=
  funext

protected theorem eta (s : FStream α) : s.head ::ₛ s.tail = s :=
  FStream.ext
    fun i => by cases i <;> rfl

theorem nth_zero_cons (a : α) (s : FStream α) : (a::ₛs).nth 0 = a :=
  rfl

theorem head_cons (a : α) (s : FStream α) : (a ::ₛ s).head = a :=
  rfl

theorem tail_cons (a : α) (s : FStream α) : (a ::ₛ s).tail = s :=
  rfl

theorem tail_drop (n : ℕ) (s : FStream α)
  : (s.drop n).tail = s.tail.drop n
:=
  FStream.ext
    fun i => by
      simp [drop, tail, nth]
      conv =>
        left ; congr
        rw [Nat.add_comm, Nat.add_left_comm]

theorem nth_drop (n m : ℕ) (s : FStream α) : (s.drop m).nth n = s.nth (n + m) :=
  rfl

theorem tail_eq_drop (s : FStream α) : s.tail = s.drop 1 :=
  rfl

theorem drop_drop (n m : ℕ) (s : FStream α) : (s.drop m).drop n = s.drop (n+m) :=
  FStream.ext
    fun i => by
      simp [drop, nth]
      rw [Nat.add_assoc]

theorem nth_succ (n : ℕ) (s : FStream α) : s.nth n.succ = s.tail.nth n :=
  rfl

theorem drop_succ (n : ℕ) (s : FStream α) : s.drop n.succ = s.tail.drop n :=
  rfl

@[simp]
lemma head_drop {α} (s : FStream α) (n : ℕ) : (s.drop n).head = s.nth n :=
  by
    simp [drop, nth, head]

theorem all_def (p : α → Prop) (s : FStream α) : all p s = ∀ n, p (nth s n) :=
  rfl

theorem any_def (p : α → Prop) (s : FStream α) : any p s = ∃ n, p (nth s n) :=
  rfl

theorem mem_cons (a : α) (s : FStream α) : a ∈ (a::ₛs) :=
  ⟨0, rfl⟩

theorem mem_cons_of_mem {a : α} {s : FStream α} (b : α) : a ∈ s → a ∈ b ::ₛ s :=
  fun ⟨nₐ, hₐ⟩ =>
    Exists.intro
      (nₐ + 1)
      (by rw [nth_succ, tail_cons]; exact hₐ)

theorem eq_or_mem_of_mem_cons {a b : α} {s : FStream α} : a ∈ b::ₛs → a = b ∨ a ∈ s :=
  fun ⟨nₐ, hₐ⟩ =>
    match nVal : nₐ with
    | 0 => Or.inl hₐ
    | n+1 => Or.inr (
      by
        rw [nth_succ, tail_cons] at hₐ
        exact ⟨n, hₐ⟩
    )

theorem mem_of_nth_eq {n : ℕ} {s : FStream α} {a : α} : a = s.nth n → a ∈ s :=
  (⟨n, ·⟩)



section map

  variable
    (f : α → β)

  theorem drop_map (n : ℕ) (s : FStream α) : (s.map f).drop n = (s.drop n).map f :=
    FStream.ext
      fun _ => rfl

  theorem nth_map (n : ℕ) (s : FStream α) : (s.map f).nth n = f (s.nth n) :=
    rfl

  theorem tail_map (s : FStream α) : tail (map f s) = map f (tail s) :=
    by
      rw [tail_eq_drop]
      rfl

  theorem head_map (s : FStream α) : head (map f s) = f (head s) :=
    rfl

  theorem map_eq (s : FStream α) : map f s = f (head s) ::ₛ map f (tail s) :=
    by
      rw [← FStream.eta (map f s), tail_map, head_map]

  theorem map_cons (a : α) (s : FStream α) : map f (a ::ₛ s) = f a ::ₛ map f s :=
    by
      rw [← FStream.eta (map f (a ::ₛ s)), map_eq]
      rfl

  theorem map_id (s : FStream α) : map id s = s :=
    rfl

  theorem map_map (g : β → δ) (f : α → β) (s : FStream α) : map g (map f s) = map (g ∘ f) s :=
    rfl

  theorem map_tail (s : FStream α) : map f (tail s) = tail (map f s) :=
    rfl

  theorem mem_map {a : α} {s : FStream α} : a ∈ s → f a ∈ map f s :=
    fun ⟨nₐ, hₐ⟩ =>
      ⟨nₐ, (by rw [nth_map, hₐ])⟩

  theorem exists_of_mem_map {f} {b : β} {s : FStream α} : b ∈ map f s → ∃ a, a ∈ s ∧ f a = b :=
    fun ⟨n, h⟩ =>
      ⟨nth s n, ⟨n, rfl⟩, h.symm⟩

end map



section zip

  variable
    (f : α → β → δ)

  theorem drop_zip (n : ℕ) (s₁ : FStream α) (s₂ : FStream β)
    : (s₁.zip f s₂).drop n = (s₁.drop n).zip f (s₂.drop n)
  :=
    FStream.ext
      fun _ => rfl

  theorem nth_zip (n : ℕ) (s₁ : FStream α) (s₂ : FStream β)
    : (s₁.zip f s₂).nth n = f (s₁.nth n) (s₂.nth n)
  :=
    rfl

  theorem head_zip (s₁ : FStream α) (s₂ : FStream β)
    : head (s₁.zip f s₂) = f s₁.head s₂.head
  :=
  rfl

  theorem tail_zip (s₁ : FStream α) (s₂ : FStream β)
    : (s₁.zip f s₂).tail = s₁.tail.zip f s₂.tail
  :=
    rfl

  theorem zip_eq (s₁ : FStream α) (s₂ : FStream β)
    : s₁.zip f s₂ = f s₁.head s₂.head ::ₛ s₁.tail.zip f (tail s₂)
  :=
    by
      rw [← FStream.eta (s₁.zip f s₂)]
      rfl

end zip



section const

  theorem mem_const (a : α) : a ∈ const a :=
    ⟨0, rfl⟩

  theorem const_eq (a : α) : const a = a ::ₛ const a :=
    FStream.ext
      fun n => by cases n <;> rfl

  theorem tail_const (a : α) : (const a).tail = const a :=
    by
      conv =>
        left
        rw [const_eq, tail_cons]

  theorem map_const (f : α → β) (a : α) : (const a).map f = const (f a) :=
    rfl

  theorem nth_const (n : ℕ) (a : α) : (const a).nth n = a :=
    rfl

  theorem drop_const (n : ℕ) (a : α) : (const a).drop n = const a :=
    rfl

end const



section iterate

  theorem head_iterate (f : α → α) (a : α) : (iterate f a).head = a :=
    rfl

  theorem tail_iterate (f : α → α) (a : α) : (iterate f a).tail = iterate f (f a) :=
    FStream.ext
      fun n =>
        by
          induction n with
          | zero => rfl
          | succ n ih =>
            simp [tail, nth, iterate, iterate.loop] at *
            rw [ih]

  theorem iterate_eq (f : α → α) (a : α) : iterate f a = a ::ₛ iterate f (f a) :=
    by
      rw [← FStream.eta (iterate f a), tail_iterate]
      rfl

  theorem nth_zero_iterate (f : α → α) (a : α) : nth (iterate f a) 0 = a :=
    rfl

  theorem nth_succ_iterate (n : Nat) (f : α → α) (a : α)
    : (iterate f a).nth (n + 1) = (iterate f (f a)).nth n
  :=
    by
      rw [nth_succ, tail_iterate]

end iterate



section bisim
  variable
    (R : FStream α → FStream α → Prop)

  local infix:50 " ~ " => R

  def is_bisim :=
    ∀ ⦃s₁ s₂⦄, s₁ ~ s₂
    → s₁.head = s₂.head
    ∧ s₁.tail ~ s₂.tail

  theorem nth_of_bisim (bisim : is_bisim R) :
    ∀ {s₁ s₂} n, s₁ ~ s₂
    → s₁.nth n = s₂.nth n
    ∧ s₁.drop (n+1) ~ s₂.drop (n+1)
  | s₁, s₂, 0, h => bisim h
  | s₁, s₂, n+1, h =>
      let ⟨h₁, trel⟩ := bisim h
      nth_of_bisim bisim n trel

  -- If two streams are bisimilar, then they are equal
  theorem eq_of_bisim (bisim : is_bisim R) : ∀ {s₁ s₂}, s₁ ~ s₂ → s₁ = s₂ :=
    fun {s₁ s₂} bisim₁₂ =>
      FStream.ext
        fun n =>
          nth_of_bisim R bisim n bisim₁₂
          |>.left

  theorem bisim_simple (s₁ s₂ : FStream α) :
    s₁.head = s₂.head → s₁ = s₁.tail → s₂ = s₂.tail → s₁ = s₂
  :=
    fun hd₁₂ tl₁ tl₂ =>
      let bisim s₁ s₂ :=
        s₁.head = s₂.head
        ∧ s₁ = s₁.tail
        ∧ s₂ = s₂.tail
      let isBisim : is_bisim bisim :=
        fun s₁ s₂ ⟨hd₁₂, tl₁, tl₂⟩ =>
          And.intro hd₁₂ (
            by
              rwa [←tl₁, ←tl₂]
          )
      eq_of_bisim bisim isBisim ⟨hd₁₂, tl₁, tl₂⟩

end bisim



theorem coinduction {s₁ s₂ : FStream α} :
  s₁.head = s₂.head
  → (
    ∀ (β : Type u) (fr : FStream α → β),
      fr s₁ = fr s₂ →
      fr s₁.tail = fr s₂.tail
  )
  → s₁ = s₂
:=
  fun eqHead eqTail =>
    let bisim s₁ s₂ :=
      s₁.head = s₂.head
      ∧ ∀ (β : Type u) (fr : FStream α → β),
        fr s₁ = fr s₂
        → fr s₁.tail = fr s₂.tail
    let isBisim : is_bisim bisim :=
      fun s₁ s₂ h =>
        let eqHead := h.left
        let eqHeadTail :=
          h.right α (@head α) eqHead
        let eqTailTail (β : Type u) (fr : FStream α → β) :=
          h.right β (fun s => fr s.tail)
        ⟨eqHead, eqHeadTail, eqTailTail⟩
    eq_of_bisim bisim isBisim ⟨eqHead, eqTail⟩



theorem iterate_id (a : α) : iterate id a = const a :=
  coinduction
    rfl
    (fun β fr ch =>
      by
        rw [tail_iterate, tail_const]
        exact ch
    )



theorem map_iterate (f : α → α) (a : α) : iterate f (f a) = (iterate f a).map f :=
  FStream.ext
    fun i =>
      by
        induction i with
        | zero => rfl
        | succ n ih =>
          rw [nth, iterate, iterate.loop, ih] at *
          rfl



section corec
  theorem corec_def (f : α → β) (g : α → α) (a : α) : corec f g a = map f (iterate g a) :=
    rfl

  theorem corec_eq (f : α → β) (g : α → α) (a : α) : corec f g a = f a ::ₛ corec f g (g a) :=
    by
      rw [corec_def, map_eq, head_iterate, tail_iterate]
      rfl

  theorem corec_id_id_eq_const (a : α) : corec id id a = const a :=
    by
      rw [corec_def, map_id, iterate_id]

  theorem corec_id_f_eq_iterate (f : α → α) (a : α) : corec id f a = iterate f a :=
    rfl
end corec



section corec'

  theorem corec'_eq (f : α → β × α) (a : α) :
    corec' f a = (f a).1 ::ₛ corec' f (f a).2
  :=
    corec_eq _ _ _

end corec'



section unfolds

  theorem unfolds_eq (g : α → β) (f : α → α) (a : α) :
    unfolds g f a = g a ::ₛ unfolds g f (f a)
  :=
    by
      unfold unfolds
      rw [corec_eq]

  theorem nth_unfolds_head_tail :
    ∀ (n : Nat) (s : FStream α),
      (unfolds head tail s).nth n = s.nth n
  :=
    fun n =>
      by
        induction n with
        | zero => intro ; rfl
        | succ n ih =>
          intro s
          rw [nth_succ, nth_succ, unfolds_eq, tail_cons, ih]

  theorem unfolds_head_eq : ∀ (s : FStream α), unfolds head tail s = s :=
    fun s =>
      FStream.ext
        fun n =>
          nth_unfolds_head_tail n s

end unfolds



section interleave
  theorem interleave_eq (s₁ s₂ : FStream α) :
    s₁ ⋈ s₂ = head s₁ ::ₛ head s₂ ::ₛ (s₁.tail ⋈ s₂.tail)
  := by
    rw [interleave, corecOn, corec_eq, corec_eq]
    rfl

  theorem tail_interleave (s₁ s₂ : FStream α) :
    (s₁ ⋈ s₂).tail = s₂ ⋈ s₁.tail
  := by
    rw [interleave, corecOn, corec_eq]
    rfl

  theorem interleave_tail_tail (s₁ s₂ : FStream α) :
    s₁.tail ⋈ s₂.tail = (s₁ ⋈ s₂).tail.tail
  := by
    rw [interleave_eq s₁ s₂]
    rfl

  theorem nth_interleave_left :
    ∀ (n : Nat) (s₁ s₂ : FStream α),
      (s₁ ⋈ s₂).nth (2 * n) = s₁.nth n
  | 0, s₁, s₂ => rfl
  | n + 1, s₁, s₂ => by
    change (s₁ ⋈ s₂).nth (2 * n).succ.succ = s₁.nth (n + 1)
    rw [
        nth_succ, nth_succ,
        interleave_eq,
        tail_cons, tail_cons,
        nth_interleave_left n s₁.tail s₂.tail,
    ]
    rfl

  theorem nth_interleave_right :
    ∀ (n : Nat) (s₁ s₂ : FStream α),
      (s₁ ⋈ s₂).nth (2 * n + 1) = s₂.nth n
  | 0, s₁, s₂ => rfl
  | n + 1, s₁, s₂ => by
    change (s₁ ⋈ s₂).nth (2 * n + 1).succ.succ = s₂.nth (n + 1)
    rw [
        nth_succ, nth_succ,
        interleave_eq,
        tail_cons, tail_cons,
        nth_interleave_right n s₁.tail s₂.tail,
    ]
    rfl

  theorem mem_interleave_left {a : α} {s₁ : FStream α} (s₁ : FStream α) :
    a ∈ s₁ → a ∈ s₁ ⋈ s₂
  :=
    fun ⟨n, h⟩ => ⟨
      2 * n,
      by rw [h, nth_interleave_left]
    ⟩

  theorem mem_interleave_right {a : α} {s₁ : FStream α} (s₂ : FStream α) :
    a ∈ s₂ → a ∈ s₁ ⋈ s₂
  :=
    fun ⟨n, h⟩ => ⟨
      2 * n + 1,
      by rw [h, nth_interleave_right]
    ⟩

end interleave



section even_odd

  theorem odd_eq (s : FStream α) : odd s = s.tail.even :=
    rfl

  theorem head_even (s : FStream α) : s.even.head = s.head :=
    rfl

  theorem tail_even (s : FStream α) : s.even.tail = s.tail.tail.even := by
    rw [even, corecOn, corec_eq]
    rfl

  theorem even_cons_cons (a₁ a₂ : α) (s : FStream α) :
    (a₁ ::ₛ a₂ ::ₛ s).even = a₁ ::ₛ s.even
  := by
    rw [even, corecOn, corec_eq]
    rfl

  theorem even_tail (s : FStream α) : s.tail.even = odd s :=
    rfl

  theorem even_interleave (s₁ s₂ : FStream α) : (s₁ ⋈ s₂).even = s₁ :=
    eq_of_bisim
      (fun s₁' s₁ => ∃ s₂, s₁' = (s₁ ⋈ s₂).even)
      (fun s₁' s₁ ⟨s₂, h₁⟩ => by
        rw [h₁]
        constructor
        · rfl
        · exact ⟨
          s₂.tail,
          by
            rw [interleave_eq, even_cons_cons, tail_cons]
        ⟩
      )
      ⟨s₂, rfl⟩

  theorem interleave_even_odd (s : FStream α) : s.even ⋈ s.odd = s :=
    eq_of_bisim
      (fun s₁ s₂ =>
        s₁ = s₂.even ⋈ s₂.odd
      )
      (fun s₁ s₂ (h : s₁ = s₂.even ⋈ s₂.odd) => by
        rw [h]
        constructor
        · rfl
        · simp [odd_eq, odd_eq, tail_interleave, tail_even]
      )
      rfl

  theorem nth_even : (n : Nat) → (s : FStream α) → s.even.nth n = s.nth (2 * n)
  | 0, s => rfl
  | n + 1, s => by
    change s.even.nth (n + 1) = s.nth (2 * n).succ.succ
    rw [
      nth_succ, nth_succ,
      tail_even,
      nth_even n s.tail.tail,
    ]
    rfl

  theorem nth_odd (n : Nat) (s : FStream α) : s.odd.nth n = s.nth (2 * n + 1) := by
    rw [odd_eq, nth_even]
    rfl

end even_odd



section mem

  theorem mem_of_mem_even (a : α) (s : FStream α) : a ∈ s.even → a ∈ s :=
    fun ⟨n, h⟩ => ⟨
        2 * n,
        by rw [h, nth_even]
    ⟩

  theorem mem_of_mem_odd (a : α) (s : FStream α) : a ∈ odd s → a ∈ s :=
    fun ⟨n, h⟩ => ⟨
      2 * n + 1,
      by rw [h, nth_odd]
    ⟩

end mem



section appendStream

  theorem nil_appendStream (s : FStream α) : [] ++ₛ s = s :=
    rfl

  theorem cons_appendStream (a : α) (l : List α) (s : FStream α) :
    (List.cons a l) ++ₛ s = a ::ₛ (l ++ₛ s)
  :=
    rfl

  theorem append_appendStream :
    ∀ (l₁ l₂ : List α) (s : FStream α),
      (l₁ ++ l₂) ++ₛ s = l₁ ++ₛ (l₂ ++ₛ s)
  | [], l₂, s => rfl
  | List.cons a l₁, l₂, s => by
    rw [
      List.cons_append,
      cons_appendStream, cons_appendStream,
      append_appendStream l₁ l₂ s,
    ]

  theorem map_appendStream (f : α → β) :
    ∀ (l : List α) (s : FStream α),
      (l ++ₛ s).map f = l.map f ++ₛ s.map f
  | [], s => rfl
  | List.cons a l, s => by
    rw [
      cons_appendStream,
      List.map_cons,
      map_cons,
      cons_appendStream,
      map_appendStream f l s,
    ]

  theorem drop_appendStream :
    ∀ (l : List α) (s : FStream α),
      (l ++ₛ s).drop l.length = s
  | [], s => by
    rfl
  | List.cons a l, s => by
    rw [
      List.length_cons,
      drop_succ,
      cons_appendStream,
      tail_cons,
      drop_appendStream l s,
    ]

  theorem appendStream_head_tail (s : FStream α) : [s.head] ++ₛ s.tail = s := by
    rw [cons_appendStream, nil_appendStream, FStream.eta]

  theorem mem_appendStream_right :
    ∀ {a : α} (l : List α) {s : FStream α},
      a ∈ s → a ∈ l ++ₛ s
  | a, [], s, h => h
  | a, List.cons b l, s, h =>
    let ih : a ∈ l ++ₛ s :=
      mem_appendStream_right l h
    mem_cons_of_mem _ ih


  theorem mem_appendStream_left :
    ∀ {a : α} {l : List α} (s : FStream α),
      a ∈ l → a ∈ l ++ₛ s
  | a, [], s, h =>
    absurd h (List.not_mem_nil _)
  | a, List.cons b l, s, h =>
    Or.elim
      (List.eq_or_mem_of_mem_cons h)
      (fun a_eq_b : a = b =>
        ⟨0, a_eq_b⟩
      )
      (fun a_in_l : a ∈ l =>
        mem_cons_of_mem b (mem_appendStream_left s a_in_l)
      )

end appendStream



section take

  @[simp]
  theorem take_zero (s : FStream α) :
    s.take 0 = []
  :=
    rfl

  @[simp]
  theorem take_succ (n : Nat) (s : FStream α) :
    s.take n.succ = s.head :: s.tail.take n
  :=
    rfl

  @[simp]
  theorem length_take (n : Nat) (s : FStream α) :
    (s.take n).length = n
  := by
    induction n generalizing s <;> simp [*]

  theorem nth_take_succ :
    ∀ (n : Nat) (s : FStream α),
      List.get? (s.take (n + 1)) n = some (s.nth n)
  | 0, s => rfl
  | n + 1, s => by
    rw [take_succ, Nat.add_one, List.get?, nth_take_succ n]
    rfl

  theorem appendStream_take_drop :
    ∀ (n : Nat) (s : FStream α),
      (s.take n) ++ₛ (s.drop n) = s
  := by
    intro n
    induction n with
    | zero =>
      intro s
      rfl
    | succ n ih =>
      intro s
      rw [take_succ, drop_succ, cons_appendStream, ih s.tail, FStream.eta]

end take



--- Reduces a proof of equality of infinite streams to an induction over all their finite
--- approximations.
theorem take_theorem (s₁ s₂ : FStream α) :
  (∀ (n : Nat), s₁.take n = s₂.take n) → s₁ = s₂
:= by
  intro h
  apply FStream.ext
  intro n
  induction n with
  | zero =>
    have take₁ := h 1
    simp [head] at take₁
    exact take₁
  | succ n ih =>
    have h₁ : some (s₁.nth n.succ) = some (s₂.nth n.succ) := by
      rw [←nth_take_succ, ←nth_take_succ, h n.succ.succ]
    injection h₁
    assumption

protected theorem cycle_g_cons (a a₁ : α) (l₁ : List α) (a₀ : α) (l₀ : List α) :
  FStream.cycleG (a, a₁ :: l₁, a₀, l₀) = (a₁, l₁, a₀, l₀)
:=
  rfl

theorem cycle_eq :
  ∀ (l : List α) (h : l ≠ []),
    cycle l h = l ++ₛ cycle l h
| [], h => absurd rfl h
| List.cons a l, h =>
  have gen :
    ∀ l' a',
      corec FStream.cycleF FStream.cycleG (a', l', a, l)
      =
      a' ::ₛ (l' ++ₛ corec FStream.cycleF FStream.cycleG (a, l, a, l))
  := by
    intro l'
    induction l' with
    | nil =>
      intros
      rw [corec_eq]
      rfl
    | cons a₁ l₁ ih =>
      intros
      rw [corec_eq, FStream.cycle_g_cons, ih a₁]
      rfl
  gen l a

theorem mem_cycle {a : α} {l : List α} :
  ∀ (h : l ≠ []),
    a ∈ l → a ∈ cycle l h
:=
  fun h a_in_l => by
    rw [cycle_eq]
    exact mem_appendStream_left _ a_in_l

theorem cycle_singleton (a : α) (h : [a] ≠ []) : cycle [a] h = const a :=
  coinduction
    rfl
    fun β fr ch => by
      rwa [cycle_eq, const_eq]

theorem tails_eq (s : FStream α) : s.tails = s.tail ::ₛ s.tail.tails := by
  unfold tails
  <;> rw [corec_eq]
  <;> rfl

theorem nth_tails :
  ∀ (n : Nat) (s : FStream α),
    s.tails.nth n = s.tail.drop n
:= by
  intro n
  induction n with
  | zero =>
    intros
    rfl
  | succ n ih =>
    intro s
    rw [nth_succ, drop_succ, tails_eq, tail_cons, ih]

theorem tails_eq_iterate (s : FStream α) :
  s.tails = iterate tail s.tail
:=
  rfl

theorem initsCore_eq (l: List α) (s : FStream α) :
  s.initsCore l = l ::ₛ s.tail.initsCore (l ++ [s.head])
:= by
  rw [FStream.initsCore, corecOn, corec_eq]
  rfl

theorem tail_inits (s : FStream α) :
  s.inits.tail = s.tail.tail.initsCore [s.head, s.tail.head]
:= by
  rw [inits, initsCore_eq]
  rfl

theorem inits_tail (s: FStream α) :
  s.tail.inits = s.tail.tail.initsCore [s.tail.head]
:= by
  rfl

theorem cons_nth_initsCore :
  ∀ (a : α) (n : Nat) (l : List α) (s : FStream α),
    a :: (s.initsCore l |>.nth n) = (s.initsCore (a :: l) |>.nth n)
:= by
  intro a n
  induction n with
  | zero =>
    intros
    rfl
  | succ n ih =>
    intro l s
    rw [nth_succ, initsCore_eq, tail_cons, ih, initsCore_eq (a :: l) s]
    rfl

theorem nth_inits :
  ∀ (n : Nat) (s : FStream α),
    s.inits.nth n = s.take n.succ
:= by
  intro n
  induction n with
  | zero =>
    intros
    rfl
  | succ n ih =>
    intros
    rw [nth_succ, take_succ, ←ih, tail_inits, inits_tail, cons_nth_initsCore]

theorem inits_eq (s : FStream α) :
  s.inits = [s.head] ::ₛ map (List.cons s.head) s.tail.inits
:= by
  apply FStream.ext
  intro n
  cases n
  · rfl
  · rw [nth_inits, nth_succ, tail_cons, nth_map, nth_inits]
    rfl

theorem zip_inits_tails (s : FStream α) :
  zip List.appendStream s.inits s.tails = const s
:= by
  apply FStream.ext
  intro n
  rw [
    nth_zip, nth_inits, nth_tails, nth_const,
    take_succ,
    cons_appendStream, appendStream_take_drop, FStream.eta,
  ]

theorem identity (s : FStream α) : pure id⊛s = s :=
  rfl

theorem composition
  (g : FStream (β → δ))
  (f : FStream (α → β))
  (s : FStream α)
  : (pure Function.comp) ⊛ g ⊛ f ⊛ s = g ⊛ (f ⊛ s)
:=
  rfl

theorem homomorphism (f : α → β) (a : α) :
  (pure f) ⊛ (pure a) = pure (f a)
:=
  rfl

theorem interchange (fs : FStream (α → β)) (a : α) :
  fs ⊛ pure a = (pure fun f : α → β => f a) ⊛ fs
:=
  rfl

theorem map_eq_apply (f : α → β) (s : FStream α) :
  map f s = (pure f) ⊛ s
:=
  rfl

theorem nth_nats (n : Nat) : nth nats n = n :=
  rfl

theorem nats_eq : nats = 0 ::ₛ (nats.map Nat.succ) := by
  apply FStream.ext
  intro n
  cases n with
  | zero =>
    rfl
  | succ n =>
    rw [nth_succ]
    rfl
