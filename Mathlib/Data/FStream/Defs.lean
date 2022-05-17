/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Data.Nat.Basic

/-!
# Streams a.k.a. infinite lists a.k.a. infinite sequences

A stream `FStream α` is an infinite sequence of elements of `α`. One can also think about it as an
infinite list. Alternatively, a stream can be seen as a function from *discrete moments in time* (ℕ)
to elements of `α`.

In this file, we define `FStream` and some functions that take and/or return streams.


## Notation

- `a ::ₛ s` for `s.cons a`, which prepends an element to a stream; input as `::\_s`.
- `s₁ ⋈ s₂` for `s₁.interleave s₂`, the even (odd) elements of which are the elements of `s₁`
  (`s₂`); input as `\bow` or `\bowtie`.
- `l ++ₛ s` for `s.prependList l` or `l.appendStream s`, the stream that starts with the elements of
  list `l` followed by the elements of `s`; input as `++\_s`.
- `sFuns ⊛ s` for `sFuns.apply s`, the stream of applying the functions (`α → β`) in `sFuns` to the
  elements of `s`; input as `\circledast`.


## Notable Definitions

Notably, this file defines `FStream.corec` *a.k.a.* `FStream.unfolds`, which generates a stream of
`β` from a value (of type `α`), a *step* function (`α → α`) and a *yield* function (`α → β`).
Several variations are defined, including `FStream.correcState` which performs corecursion using a
state monad.


## File History

This is a Lean 4 version of [`mathlib/data/stream/defs.lean`][defs], where `FStream` is called
`stream` instead. Lean 4 already has a `Stream` type, so it was renamed to `FStream` to avoid
nameclashes.

[defs]: https://github.com/leanprover-community/mathlib/tree/master/src/data/stream/defs.lean
-/

universe u v w

--- A stream `FStream α` is an infinite sequence of elements of `α`
def FStream (α : Type u) :=
  Nat → α

def FStream.nth (s : FStream α) (n : Nat) :=
  s n



variable
  {α : Type u}
  {β : Type v}
  {δ : Type w}



--- Prepends an element to a stream.
def FStream.cons (a : α) (s : FStream α) : FStream α
| 0 => a
| n + 1 => s n

namespace FStream.Notation
  --- List-like notation for `cons`.
  scoped infixr:65 "::ₛ" => FStream.cons
end FStream.Notation

open FStream.Notation


--- Head of a stream.
def FStream.head (s: FStream α) : α :=
  s.nth 0



--- Drop first `n` elements of a stream.
def FStream.drop (count : ℕ) (s: FStream α) : FStream α
| n => s.nth (n + count)

--- Tail of a stream: `(h::ₛt).tail = t`.
def FStream.tail (s : FStream α) : FStream α
| n => s.nth (n + 1)



--- Proposition saying that all elements of a stream satisfy a predicate.
def FStream.all (P : α → Prop) (s : FStream α) :=
  ∀ (n : ℕ), s.nth n |> P

--- Proposition saying that at least on element of a stream satisfies a predicate.
def FStream.any (P : α → Prop) (s : FStream α) :=
  ∃ (n : ℕ), s.nth n |> P



--- `a ∈ s` means that `a = s.nth n` for some `n`.
instance : Membership α (FStream α) where
  mem a s :=
    s.any (a = ·)



--- Apply a function `f` to all elements of a stream `s`.
def FStream.map (f : α → β) (s : FStream α) : FStream β
| n => s.nth n |> f

--- Zip two streams using a binary operation.
---
--- `(s₁.zip f s₂).nth n = f (s₁.nth n) (s₂.nth n)`
def FStream.zip (f : α → β → δ) (s₁ : FStream α) (s₂ : FStream β) : FStream δ
| n => f (s₁.nth n) (s₂.nth n)

--- The constant stream: `(FStream.const a).nth n = a`.
def FStream.const (a : α) : FStream α
| n => a



section iter

  instance : Stream (FStream α) α where
    next? s := (s.head, s.tail)



  protected partial def FStream.forIn
    {m : Type v → Type w}
    [Monad m]
    [Inhabited α]
    [Inhabited β]
    (s : FStream α)
    (init : β)
    (f : α → β → m (ForInStep β))
    : m β
  := do
    match (← f s.head init) with
    | ForInStep.done b =>
      pure b
    | ForInStep.yield b =>
      FStream.forIn s.tail init f

  -- instance [Inhabited α] : ForIn m (FStream α) α where
  --   -- missing `[Inhabited β]` :(
  --   forIn := FStream.forIn



  --- Iterates of a function as a stream.
  def FStream.iterate (f : α → α) (a : α) : FStream α
  | n =>
    let rec loop : ℕ → α
      | 0 => a
      | n + 1 => f (loop n)
    loop n



  --- Generates a stream from an `init`ial value by iterating `step` and applying `yield` to each
  --- element.
  def FStream.corec (yield : α → β) (step : α → α) (init : α): FStream β :=
    FStream.iterate step init |>.map yield

  --- Same as `FStream.corecOn` but `init` is the first argument.
  def FStream.corecOn (init : α) (yield : α → β) (step : α → α) : FStream β :=
    FStream.corec yield step init

  --- Same as `FStream.corec` but takes a single function combining `step` and `yield`.
  def FStream.corec' (step : α → β × α) : α → FStream β :=
    FStream.corec
      (Prod.fst ∘ step)
      (Prod.snd ∘ step)



  --- Use a state monad to generate a stream through corecursion.
  def FStream.corecState {σ α} (cmd : StateM σ α) (s : σ) : FStream α :=
    FStream.corec
      Prod.fst
      (cmd.run ∘ Prod.snd)
      (cmd.run s)

  -- `FStream.corec` is also known as unfold.
  def FStream.unfolds (g : α → β) (f : α → α) (a : α) : FStream β :=
    FStream.corec g f a

end iter



--- Interleave two streams.
def FStream.interleave (s₁ s₂ : FStream α) : FStream α :=
  FStream.corecOn (s₁, s₂)
    (fun (s₁, s₂) => s₁.head)
    (fun (s₁, s₂) => (s₂, s₁.tail))

namespace FStream.Notation
  --- Nice notation for `FStream.interleave`.
  scoped infix:65 "⋈" => FStream.interleave
end FStream.Notation


--- Elements of a stream with even indices.
def FStream.even (s : FStream α) : FStream α :=
  FStream.corecOn s
    (fun s => s.head)
    (fun s => tail (tail s))

--- Elements of a stream with odd indices.
def FStream.odd (s : FStream α) : FStream α :=
  s.tail.even



--- Prepend a list to a stream.
def FStream.prependList : List α → FStream α → FStream α
  | [], s =>
    s
  | List.cons hd tl, s =>
    hd ::ₛ (s.prependList tl)

--- Append a stream to a list.
def List.appendStream (l : List α) (s : FStream α) : FStream α :=
  s.prependList l

namespace FStream.Notation
  --- Nice notation for `FStream.prependList`.
  infixl:65 "++ₛ" => List.appendStream
end FStream.Notation



--- `s.take n` returns a list of the `n` first elements of stream `s`.
def FStream.take : ℕ → FStream α → List α
  | 0, s => []
  | n + 1, s =>
    let tailTakeN := s.tail.take n
    List.cons s.head tailTakeN



--- Defines `FStream.cycle` which interprets a non-empty list as a cyclic stream.
section cycle
  --- Auxiliary definition for `FStream.cycle` corecursive def.
  protected def FStream.cycleF : α × List α × α × List α → α
    | (v, _, _ , _) => v

  --- Auxiliary definition for `FStream.cycle` corecursive def.
  protected def FStream.cycleG : α × List α × α × List α → α × List α × α × List α
    | (_, [], v₀, l₀) => (v₀, l₀, v₀, l₀)
    | (_, List.cons v₂ l₂, v₀, l₀) => (v₂, l₂, v₀, l₀)

  --- Interpret a non-empty list as a cyclic stream.
  def FStream.cycle : (l : List α) → l ≠ [] → FStream α
  | [], h =>
    absurd rfl h
  | List.cons hd tl, h =>
    FStream.corec
      FStream.cycleF
      FStream.cycleG
      (hd, tl, hd, tl)
end cycle



--- Tails of a stream, starting with `s.tail`.
def FStream.tails (s : FStream α) : FStream (FStream α) :=
  FStream.corec id tail s.tail



--- Defines `FStream.inits` which produces the non-empty initial segments of a stream.
section inits

  --- Auxiliary definition for `FStream.inits`.
  protected def FStream.initsCore (l : List α) (s : FStream α) : FStream (List α) :=
    FStream.corecOn (l, s)
      (fun ⟨a, b⟩ => a)
      (fun (l', s') =>
        (l' ++ [head s'], tail s')
      )

  --- Non-empty initial segments of a stream.
  def FStream.inits (s : FStream α) : FStream (List α) :=
    FStream.initsCore [s.head] s.tail

end inits



--- A constant stream, same as `FStream.const`.
@[inline]
def FStream.pure (a : α) : FStream α :=
  const a



--- Given a stream of functions and a stream of values, apply `n`-th function to `n`-th value.
def FStream.apply (funs : FStream (α → β)) (args : FStream α) : FStream β
| n =>
  let f := funs.nth n
  let arg := args.nth n
  f arg

namespace FStream.Notation
  --- Input as `\circledast`.
  infixl:75 "⊛" => FStream.apply
end FStream.Notation



--- The stream of natural numbers: `FStream.nats.nth n = n`.
def FStream.nats : FStream ℕ :=
  id
