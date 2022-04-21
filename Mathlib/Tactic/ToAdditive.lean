/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov, Floris van Doorn
Ported by: E.W.Ayers
-/
import Mathlib.Data.String.Defs
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.Expr.ReplaceRec
import Mathlib.Lean.Expr
import Lean
import Lean.Data

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Command

syntax (name := toAdditiveIgnoreArgs) "to_additive_ignore_args" num* : attr
syntax (name := toAdditiveRelevantArg) "to_additive_relevant_arg" num : attr
syntax (name := toAdditiveReorder) "to_additive_reorder" num* : attr
syntax (name := to_additive) "to_additive" "!"? (ppSpace ident)? (ppSpace str)? : attr

namespace ToAdditive

initialize registerTraceClass `to_additive
initialize registerTraceClass `to_additive.replace

initialize ignore_args_attr : ParametricAttribute (List Nat) ←
  registerParametricAttribute {
  name      := `to_additive_ignore_args
  descr     := "Auxiliary attribute for `to_additive` stating that certain arguments are not additivized.",
  getParam := fun decl stx => do
      let ids ← match stx with
        | `(attr|to_additive_ignore_args $[$ids:num]*) => pure $ ids.map (·.isNatLit?.get!)
        | _ => throwError "unexpected to_additive_reorder syntax {stx}"
      return ids.toList
  }

initialize reorder_attr : ParametricAttribute (List Nat) ←
  registerParametricAttribute {
    name := `toAdditiveReorder
    descr := "Auxiliary attribute for `to_additive` that stores arguments that need to be reordered."
    getParam := fun decl stx =>
      match stx with
      | `(attr|to_additive_reorder $[$ids:num]*) => pure $ Array.toList $ ids.map (·.isNatLit?.get!)
      | _ => throwError "unexpected to_additive_reorder syntax {stx}"
  }

initialize relevant_arg_attr : ParametricAttribute (Nat) ←
  registerParametricAttribute {
    name := `to_additive_relevant_arg
    descr := "Auxiliary attribute for `to_additive` stating which arguments are the types with a multiplicative structure."
    getParam := fun decl stx =>
      match stx with
      | `(attr|to_additive_relevant_arg $id) => pure $ id.isNatLit?.get!
      | _ => throwError "unexpected to_additive_relevant_arg syntax {stx}"
  }

-- [todo] replace with MapDeclarationExtension when https://github.com/leanprover/lean4/issues/1111 is fixed.
/- Maps multiplicative names to their additive counterparts. -/
initialize translations : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    name          := `translations,
    addImportedFn := fun ass => ass.foldl (fun | names, as => as.foldl (fun | names, (a,b) => names.insert a b) names) ∅,
    addEntryFn    := fun s n => s.insert n.1 n.2 ,
    toArrayFn     := fun es => es.toArray
  }

def find_translation? (env : Environment) : Name → Option Name :=
  (ToAdditive.translations.getState env).find?

def insert_translation (src tgt : Name) : CoreM Unit := do
  if let some tgt' := find_translation? (←getEnv) src then
    throwError "Already exists translation {src} ↦ {tgt'}"
  (ToAdditive.translations.addEntry (←getEnv)) (src, tgt) |> setEnv
  trace[to_additive] "Added translation {src} ↦ {tgt}."

variable {M} [Monad M]

def getNameFn  [MonadEnv M] : M (Name → Option Name) := do
  let env ← getEnv
  return find_translation? env

def runNameFn  [MonadEnv M] : Name → M (Option Name)
  | n => do return find_translation? (← getEnv) n

def ignore  [MonadEnv M]: Name → M (Option (List Nat))
  | n => do return ignore_args_attr.getParam (← getEnv) n

def getReorder  [MonadEnv M]: Name →  M (List Nat)
  | n => do return reorder_attr.getParam (← getEnv) n |> (Option.getD · [])

def shouldReorder  [MonadEnv M]: Name → Nat → M Bool
  | n, i => (i ∈ .) <$> (getReorder n)

def isRelevant  [MonadEnv M]: Name → Nat → M Bool
  | n, i => do
    match relevant_arg_attr.getParam (← getEnv) n with
    | some j => return i == j
    | none => return i == 0

/-- Get whether or not the replace-all flag is set. -/
def replaceAll  [MonadOptions M] : M Bool :=
  do return (← getOptions).getBool `to_additive.replaceAll

variable [MonadOptions M] [MonadEnv M]

/-- Auxilliary function for `additive_test`. The bool argument *only* matters when applied
to exactly a constant. -/
private def additiveTestAux: Bool → Expr → M Bool
  | b, Expr.const n _ _           => return b || (← runNameFn n).isSome
  | b, (Expr.app e a _) => do
      if (← additiveTestAux true e) then
        return true
      if let (some n) := e.getAppFn.constName? then
        if let (some l) ← ignore n then
          if e.getAppNumArgs + 1 ∈ l then
            return true
      additiveTestAux false a
  | b, (Expr.lam n e t _) => additiveTestAux false t
  | b, (Expr.forallE n e t _) => additiveTestAux false t
  | b, (Expr.letE n g e body _) =>
    return (←additiveTestAux false e) && (← additiveTestAux false body)
  | b, _                => return true

/--
`additive_test e` tests whether the expression `e` contains no constant
`nm` that is not applied to any arguments, and such that `f nm = none`.
This is used in `@[to_additive]` for deciding which subexpressions to transform: we only transform
constants if `additive_test` applied to their first argument returns `tt`.
This means we will replace expression applied to e.g. `α` or `α × β`, but not when applied to
e.g. `ℕ` or `ℝ × α`.
`f` is the dictionary of declarations that are in the `to_additive` dictionary.
We ignore all arguments specified in the `name_map` `ignore`.
If `replace_all` is `tt` the test always return `tt`.
-/
def additiveTest (e : Expr) : M Bool := do
  if (←replaceAll) then
    return true
  else
    additiveTestAux false e

/--
`e.apply_replacement_fun f test` applies `f` to each identifier
(inductive type, defined function etc) in an expression, unless
* The identifier occurs in an application with first argument `arg`; and
* `test arg` is false.
However, if `f` is in the dictionary `relevant`, then the argument `relevant.find f`
is tested, instead of the first argument.

Reorder contains the information about what arguments to reorder:
e.g. `g x₁ x₂ x₃ ... xₙ` becomes `g x₂ x₁ x₃ ... xₙ` if `reorder.find g = some [1]`.
We assume that all functions where we want to reorder arguments are fully applied.
This can be done by applying `expr.eta_expand` first.
-/
def applyReplacementFun : Expr → MetaM Expr :=
  Lean.Expr.replaceRecM fun r e => do
    match e with
    | Expr.lit (Literal.natVal 1) _    => pure <| mkNatLit 0
    | Expr.const n₀ ls _ => do
      let nameFun ← getNameFn
      let n₁ := Name.mapPrefix nameFun n₀
      if n₀ != n₁ then
        trace[to_additive.replace] "replace {n₀} → {n₁}"
      let ls : List Level ← (do -- [todo] just get Lean to figure out the levels?
        if ← shouldReorder n₀ 1 then
            return ls.get! 1::ls.head!::ls.drop 2
        return ls)
      return some $ Lean.mkConst n₁ ls
    | Expr.app g x _ => do
      let gf := g.getAppFn
      if let some nm := gf.constName? then
        let nArgs := g.getAppNumArgs
        -- e = `($gf y₁ .. yₙ $x)
        if ← shouldReorder nm nArgs then
            if ← additiveTest g.getAppArgs[0] then
              -- interchange `x` and the last argument of `g`
              let x ← r x
              let gf ← r (g.appFn!)
              let ga ← r (g.appArg!)
              let e₂ :=  mkApp2 gf x ga
              trace[to_additive.replace] "reordering {nm}: {x} ↔ {ga}\nBefore: {e}\nAfter:  {e₂}"
              return some e₂
        if ← isRelevant nm nArgs then
          if gf.isConst && not (← additiveTest x) then
            let x ← r x
            let args ← g.getAppArgs.mapM r
            return some $ mkApp (mkAppN gf args) x
      return none
    | _ => return none

/-- Eta expands `e` at most `n` times.-/
def etaExpandN (n : Nat) (e : Expr): MetaM Expr := do
  let t ← inferType e
  let e₂ ← forallBoundedTelescope t (some n) fun xs _ => do
    let e' ← mkLambdaFVars xs (mkAppN e xs)
    trace[to_additive] "η-expand({n}):\n{e}\n{xs}\n{(mkAppN e xs)}\n{e'}"
    return e'
  trace[to_additive] "η-expand:\nBefore: {e}\nAfter:  {e₂}"
  return e₂

open TransformStep in
/-- `e.expand` eta-expands all expressions that have as head a constant `n` in
`reorder`. They are expanded until they are applied to one more argument than the maximum in
`reorder.find n`. -/
private def expand : Expr → MetaM Expr
| e => do
  let e₂ ←e.replaceRecMeta $ fun r e => do
    let e0 := e.getAppFn
    let es := e.getAppArgs
    let some e0n := e0.constName? | return none
    let reorder ← getReorder e0n
    if reorder.isEmpty then
      -- no need of expand if nothing needs reordering
      return none
    let e' := mkAppN e0 $ ← es.mapM r
    let needed_n := reorder.foldr Nat.max 0 + 1
    if needed_n ≤ es.size then
      return some e'
    else
      let e' ← etaExpandN (needed_n - es.size) e'
      return some $ e'
  trace[to_additive] "expand:\nBefore: {e}\nAfter:  {e₂}"
  return e₂

def updateWithFun
  (tgt : Name) (decl : ConstantInfo)
  : MetaM ConstantInfo := do
  let mut decl := decl.updateName tgt
  decl := decl.updateType $ (← applyReplacementFun (← expand decl.type))
  if let some v := decl.value? then
    decl := decl.updateValue (← applyReplacementFun (← expand v))
  return decl


/-- transform the declaration `src` and all declarations `pre._proof_i` occurring in `src`
using the dictionary `f`.
`replace_all`, `trace`, `ignore` and `reorder` are configuration options.
`pre` is the declaration that got the `@[to_additive]` attribute and `tgt_pre` is the target of this
declaration. -/
partial def transformDeclWithPrefixFunAux
  (pre tgt_pre : Name) : Name → CoreM Unit := fun src => do
  -- if this declaration is not `pre` or an internal declaration, we do nothing.
  if not (src == pre || src.isInternal) then
    if (← runNameFn src).isSome then
      return ()
    else
      throwError "The declaration {pre} depends on the declaration {src} which is in the namespace {pre}, but does not have the `@[to_additive]` attribute. This is not supported. Workaround: move {src} to a different namespace."
  let env ← getEnv
  -- we find the additive name of `src`
  let tgt := src.mapPrefix (fun n => if n == pre then some tgt_pre else none)
  -- we skip if we already transformed this declaration before
  if env.contains tgt then
    return
  let decl ← getConstInfo src
  -- we first transform all the declarations of the form `pre._proof_i`
  for n in decl.type.listNamesWithPrefix pre do
    transformDeclWithPrefixFunAux pre tgt_pre n
  if let some value := decl.value? then
    for n in value.listNamesWithPrefix pre do
      transformDeclWithPrefixFunAux pre tgt_pre n
  -- we transform `decl` using `f` and the configuration options.
  let decl : ConstantInfo ← MetaM.run' $ updateWithFun tgt decl
  -- [todo] above line is simplified, mathlib3 version reads:
  -- decl.update_with_fun env (name.map_prefix f) (additive_test f replace_all ignore) relevant reorder tgt
  trace[to_additive] "generating\n{decl.name} :=\n  {decl.value!}"
  -- [todo] implement this error:
  -- decorate_error (format!"@[to_additive] failed. Type mismatch in additive declaration. For help, see the docstring of `to_additive.attr`, section `Troubleshooting`. Failed to add declaration\n{pp_decl}
    -- { if env.is_protected src then add_protected_decl decl else add_decl decl,
    -- -- we test that the declaration value type-checks, so that we get the decorated error message
    -- -- without this line, the type-checking might fail outside the `decorate_error`.
    -- decorate_error "proof doesn't type-check. " $ type_check decl.value }
  addAndCompile decl.toDeclaration!
  if isProtected (← getEnv) src then
    setEnv $ addProtected (← getEnv) tgt

def transformDeclWithPrefixFun (src tgt : Name) (attrs : List Name) : CoreM Unit := do
  transformDeclWithPrefixFunAux src tgt src
  let eqns? ← MetaM.run' (getEqnsFor? src true)
  -- now transform all of the equational lemmas
  if let some eqns := eqns? then
    for src_eqn in eqns do
      transformDeclWithPrefixFunAux src tgt src_eqn
      -- [todo] need to implement copyAttribute
      -- -- copy attributes for the equational lemmas so that they know if they are refl lemmas
      -- let tgt_eqn := Name.mapPrefix (fun n => if n == src then some tgt else none) src_eqn
      -- for attr in attrs do
      --   copyAttribute attr src_eqn tgt_eqn
      -- -- set the transformed equation lemmas as equation lemmas for the new declaration
      -- addEqnLemma tgt_eqn
  -- [todo] need to implement copyAttribute
  -- for attr in attrs do
  --   copyAttribute attr src tgt
  return ()

def hasAttribute' (name : Name) : MetaM Bool :=
  pure false -- [todo] implement

/--
Find the first argument of `nm` that has a multiplicative type-class on it.
Returns 1 if there are no types with a multiplicative class as arguments.
E.g. `prod.group` returns 1, and `pi.has_one` returns 2.
-/
def firstMultiplicativeArg (nm : Name) : MetaM Nat := do
  let d ← getConstInfo nm
  forallTelescopeReducing (← getConstInfo nm).type fun xs _ => do
    let l ← xs.mapIdxM fun i x => do
      forallTelescopeReducing (← inferType x) fun ys tgt => do
        let (tgt_fn, tgt_args) := tgt.getAppFnArgs
        let n_bi := ys.size
        if let some c :=  tgt.getAppFn.constName? then
          if ← hasAttribute' `to_additive then
            return none
        if tgt_args.size > 0 then
          return tgt_args[0].getAppFn.bvarIdx?.map (i + n_bi - .)
        return none
    let l := l.filterMap id
    if l.size == 0 then
      return 1
    else
      return l.foldr min l[0]

/-- `value_type` is the type of the arguments that can be provided to `to_additive`.
`to_additive.parser` parses the provided arguments:
* `replace_all`: replace all multiplicative declarations, do not use the heuristic.
* `tgt : name`: the name of the target (the additive declaration).
* `doc`: an optional doc string.
* if `allow_auto_name` is `ff` (default) then `@[to_additive]` will check whether the given name
  can be auto-generated.
-/
structure ValueType : Type where
  replaceAll : Bool := false
  tgt : Name := Name.anonymous
  doc : Option String := none
  allowAutoName : Bool := false
  deriving Repr

/-- `add_comm_prefix x s` returns `"comm_" ++ s` if `x = tt` and `s` otherwise. -/
def addCommPrefix : Bool → String → String
| true, s => "comm" ++ s -- [todo] should to-upper
| false, s => s

/-- Dictionary used by `to_additive.guess_name` to autogenerate names. -/
def tr : Bool → List String → List String
| is_comm, ("one" :: "le" :: s)        => addCommPrefix is_comm "nonneg"    :: tr false s
| is_comm, ("one" :: "lt" :: s)        => addCommPrefix is_comm "pos"       :: tr false s
| is_comm, ("le" :: "one" :: s)        => addCommPrefix is_comm "nonpos"    :: tr false s
| is_comm, ("lt" :: "one" :: s)        => addCommPrefix is_comm "neg"       :: tr false s
| is_comm, ("mul" :: "single" :: s)    => addCommPrefix is_comm "single"    :: tr false s
| is_comm, ("mul" :: "support" :: s)   => addCommPrefix is_comm "support"   :: tr false s
| is_comm, ("mul" :: "tsupport" :: s)  => addCommPrefix is_comm "tsupport"  :: tr false s
| is_comm, ("mul" :: "indicator" :: s) => addCommPrefix is_comm "indicator" :: tr false s
| is_comm, ("mul" :: s)                => addCommPrefix is_comm "add"       :: tr false s
| is_comm, ("smul" :: s)               => addCommPrefix is_comm "vadd"      :: tr false s
| is_comm, ("inv" :: s)                => addCommPrefix is_comm "neg"       :: tr false s
| is_comm, ("div" :: s)                => addCommPrefix is_comm "sub"       :: tr false s
| is_comm, ("one" :: s)                => addCommPrefix is_comm "zero"      :: tr false s
| is_comm, ("prod" :: s)               => addCommPrefix is_comm "sum"       :: tr false s
| is_comm, ("finprod" :: s)            => addCommPrefix is_comm "finsum"    :: tr false s
| is_comm, ("pow" :: s)                => addCommPrefix is_comm "nsmul"     :: tr false s
| is_comm, ("npow" :: s)               => addCommPrefix is_comm "nsmul"     :: tr false s
| is_comm, ("zpow" :: s)               => addCommPrefix is_comm "zsmul"     :: tr false s
| is_comm, ("monoid" :: s)      => ("add_" ++ addCommPrefix is_comm "monoid")    :: tr false s
| is_comm, ("submonoid" :: s)   => ("add_" ++ addCommPrefix is_comm "submonoid") :: tr false s
| is_comm, ("group" :: s)       => ("add_" ++ addCommPrefix is_comm "group")     :: tr false s
| is_comm, ("subgroup" :: s)    => ("add_" ++ addCommPrefix is_comm "subgroup")  :: tr false s
| is_comm, ("semigroup" :: s)   => ("add_" ++ addCommPrefix is_comm "semigroup") :: tr false s
| is_comm, ("magma" :: s)       => ("add_" ++ addCommPrefix is_comm "magma")     :: tr false s
| is_comm, ("haar" :: s)        => ("add_" ++ addCommPrefix is_comm "haar")      :: tr false s
| is_comm, ("prehaar" :: s)     => ("add_" ++ addCommPrefix is_comm "prehaar")   :: tr false s
| is_comm, ("unit" :: s)        => ("add_" ++ addCommPrefix is_comm "unit")      :: tr false s
| is_comm, ("units" :: s)       => ("add_" ++ addCommPrefix is_comm "units")     :: tr false s
| is_comm, ("comm" :: s)        => tr true s
| is_comm, (x :: s)             => (addCommPrefix is_comm x :: tr false s)
| true, []                        => ["comm"]
| false, []                        => []

/-- Autogenerate target name for `to_additive`. -/
def guessName : String → String :=
  String.mapTokens ''' $
  λ s => String.intercalate (String.singleton '_') $
  tr false (s.splitOn "_") -- [todo] replace with camelcase logic?

/-- Return the provided target name or autogenerate one if one was not provided. -/
def targetName (src tgt : Name) (allowAutoName : Bool) : CoreM Name := do
  let res ← do
    if tgt.getPrefix != Name.anonymous || allowAutoName then
      return tgt
    let (Name.str pre s _) := src | throwError "to_additive: can't transport {src}"
    let tgt_auto := guessName s
    if tgt.toString == tgt_auto then
      -- [todo] make this a warning?
      dbg_trace "{src}: correctly autogenerated target name {tgt_auto}, you may remove the explicit {tgt} argument."
    let pre := pre.mapPrefix <| find_translation? (← getEnv)
    if tgt == Name.anonymous then
      return Name.mkStr pre tgt_auto
    else
      return  Name.mkStr pre tgt.toString
  if res == src && tgt != src then
    throwError "to_additive: can't transport {src} to itself."
  return res

private def proceedFieldsAux (src tgt : Name) (prio : Nat) (f : Name → CoreM (List String)) : CoreM Unit :=
do
  let srcFields ← f src
  let tgtFields ← f tgt
  if srcFields.length != tgtFields.length then
    throwError "Failed to map fields of {src}, {tgt} with {srcFields} ↦ {tgtFields}"
  for (srcField, tgtField) in List.zip srcFields tgtFields do
    if srcField != tgtField then

      insert_translation (src ++ srcField) (tgt ++ tgtField)
      -- [todo] what is prio doing in mathlib3? I think it's the scoping?

/-- Add the structure fields of `src` to the translations dictionary
so that future uses of `to_additive` will map them to the corresponding `tgt` fields. -/
def proceedFields (src tgt : Name) (prio : Nat) : CoreM Unit := do
  let env : Environment ← getEnv
  let aux := proceedFieldsAux src tgt prio
  aux (fun n => do
    let fields := if isStructure env n then getStructureFields env n else #[]
    return fields |> .map Name.toString |> Array.toList
  )
  -- [todo]
  -- aux (fun n => (List.map (s!"to_{·}") <$> getTaggedAncestors n))
  -- aux (fun n => (env.constructorsOf n).mmap $
  --            fun
  --                 | (name.mk_string s pre) :=
  --                   (guard (pre = n) <|> fail "Bad constructor name") >>
  --                   pure s
  --                 | _ := fail "Bad constructor name"
  --                 )

def elab_to_additive : Syntax → CoreM ValueType
  | `(attr| to_additive $[!%$replaceAll]? $[$tgt]? $[$doc]?) => do
    return {
      replaceAll := replaceAll.isSome
      tgt := match tgt with | some tgt => tgt.getId | none => Name.anonymous
      doc := doc.bind (·.isStrLit?)
      allowAutoName := false
    }
  | _ => throwUnsupportedSyntax

initialize registerBuiltinAttribute {
    name := `to_additive
    descr :="Transport multiplicative to additive"
    add := fun src stx kind => do
      -- [todo] what is equiv of persistent in Lean 4?
      -- guard persistent <|> fail "`to_additive` can't be used as a local attribute"
      let prio := 0 -- [todo] I think this is a function of `kind`?
      let val ← elab_to_additive stx
      let ignore := ignore_args_attr.getParam (← getEnv) src
      let relevant := relevant_arg_attr.getParam (← getEnv) src
      let reorder := reorder_attr.getParam (← getEnv) src
      let tgt ← targetName src val.tgt val.allowAutoName
      if let some tgt' := find_translation? (← getEnv) src then
        throwError "{src} already has a to_additive translation {tgt'}."
      insert_translation src tgt
      let firstMultArg ← MetaM.run' <| firstMultiplicativeArg src
      if (firstMultArg != 1) then
        proceedFields src tgt prio
      if (← getEnv).contains tgt then
        proceedFields src tgt prio
      else
        let magicNames := [`reducible, `_refl_lemma, `simp, `norm_cast, `instance, `refl, `symm, `trans, `elab_as_eliminator, `no_rsimp, `continuity, `ext, `ematch, `measurability, `alias, `_ext_core, `_ext_lemma_core, `nolint, `protected]
        withOptions (fun o => o.setBool `to_additive.replaceAll val.replaceAll)
          (transformDeclWithPrefixFun src tgt magicNames)
      -- [todo] port below code
      --   if ← (hasAttribute' `simps src) then
      --     dbg_trace "Apply the simps attribute after the to_additive attribute"
      --   if ← (hasAttribute' `mono src) then
      --     dbg_trace "to_additive does not work with mono, apply the mono attribute to both versions after"
      --   match val.doc with
      --   | some doc => add_doc_string tgt doc
      --   | none => skip


      return ()
  }


end ToAdditive
