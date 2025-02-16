import Mathlib
import Lean

open Lean Meta

inductive PROP where
  | symbol (ord : Nat)
  | falsity
  | and : PROP → PROP → PROP
  | or : PROP → PROP → PROP
  | implies : PROP → PROP → PROP
  | iff : PROP → PROP → PROP
  | not : PROP → PROP

/-!
# NOTE
We define a slightly more flexible syntax set for the language given by *Definition 2.1.2*.
To be more flexible, it means that we have precedence and associativeness in place of mandatory parentheses.

What should be considered the syntax construct is the type `PROP` rather than the DSL we now introduce.
-/

declare_syntax_cat lslang

syntax ident : lslang
-- TODO: support antiquotation
syntax:105 lslang:105 " ∧ " lslang:105 : lslang
syntax:100 lslang:100 " ∨ " lslang:100 : lslang
syntax:95 lslang:95 " → " lslang:95 : lslang
syntax:90 lslang:90 " ↔ " lslang:90 : lslang -- TODO: make it non associative
syntax:max " ¬" lslang : lslang
syntax:max "⊥" : lslang
syntax "(" lslang ")" : lslang

syntax "ls[" lslang "]" : term

macro_rules
| `(ls[$name:ident]) => do
  let s := name.getId
  if s.hasMacroScopes then
    Macro.throwErrorAt name "cannot contain macro scopes"
  let s := s.toString
  let ts := s.split (· == 'p')
  unless ts.length == 2 do
    Macro.throwErrorAt name "invalid name"
  unless ts[0]! == "" do
    Macro.throwErrorAt name "invalid name"
  let some n := ts[1]!.toNat? | Macro.throwErrorAt name "invalid name"
  `($(mkIdent ``PROP.symbol) $(quote n))
| `(ls[⊥]) => `($(mkIdent ``PROP.falsity))
| `(ls[$l ∧ $r]) => `($(mkIdent ``PROP.and) ls[$l] ls[$r])
| `(ls[$l ∨ $r]) => `($(mkIdent ``PROP.or) ls[$l] ls[$r])
| `(ls[$l → $r]) => `($(mkIdent ``PROP.implies) ls[$l] ls[$r])
| `(ls[$l ↔ $r]) => `($(mkIdent ``PROP.iff) ls[$l] ls[$r])
| `(ls[¬ $p]) => `($(mkIdent ``PROP.not) ls[$p])
| `(ls[($body:lslang)]) => `((ls[$body]))

open TSyntax.Compat

@[app_unexpander PROP.symbol
, app_unexpander PROP.falsity
, app_unexpander PROP.and
, app_unexpander PROP.or
, app_unexpander PROP.implies
, app_unexpander PROP.iff
, app_unexpander PROP.not
]
partial def unexpandPROPConstruct : Lean.PrettyPrinter.Unexpander := fun s => do
  let r ← go s
  `(ls[$r:lslang])
where go
  | `(ls[$body]) => pure body
  | `(PROP.symbol $ord:num) => do
    let name := mkIdent <| Name.mkStr1 s!"p{ord.getNat}"
    `(lslang| $name:ident)
  | `(PROP.falsity) => `(lslang| ⊥)
  | `(PROP.and $l $r) => do
    let l' ← go l
    let r' ← go r
    `(lslang| $l':lslang ∧ $r':lslang)
  | `(PROP.or $l $r) => do
    let l' ← go l
    let r' ← go r
    `(lslang| $l':lslang ∨ $r':lslang)
  | `(PROP.implies $l $r) => do
    let l' ← go l
    let r' ← go r
    `(lslang| $l':lslang → $r':lslang)
  | `(PROP.iff $l $r) => do
    let l' ← go l
    let r' ← go r
    `(lslang| $l':lslang ↔ $r':lslang)
  | `(PROP.not $p) => do
    let p' ← go p
    `(lslang| ¬ $p':lslang)
  | _ => throw ()

example : PROP := ls[p7 → p0]
example : PROP := ls[(⊥ ∨ p32) ∧ (¬ p2)]

/--
# Theorem 2.1.3
Essentially another incarnation of the recursor (induction principle) of `PROP`.

To perform *proof by induction* in the book, directly use `induction` tactic on terms of `PROP`.
This example is only to show that is valid.
-/
example {A : PROP → Prop}
    : (∀ i, A (PROP.symbol i))
    → (A PROP.falsity)
    → (∀ ϕ φ : PROP, A ϕ → A φ → A (PROP.and ϕ φ))
    → (∀ ϕ φ : PROP, A ϕ → A φ → A (PROP.or ϕ φ))
    → (∀ ϕ φ : PROP, A ϕ → A φ → A (PROP.implies ϕ φ))
    → (∀ ϕ φ : PROP, A ϕ → A φ → A (PROP.iff ϕ φ))
    → (∀ ϕ : PROP, A ϕ → A (PROP.not ϕ))
    → ∀ ϕ, A ϕ
  := by
  intro h1 h2 h3 h4 h5 h6 h7 ϕ
  induction ϕ with
  | symbol i => simp [h1]
  | falsity => apply h2
  | and ϕ φ hl hr => apply h3 ϕ φ hl hr
  | or ϕ φ hl hr => apply h4 ϕ φ hl hr
  | implies ϕ φ hl hr => apply h5 ϕ φ hl hr
  | iff ϕ φ hl hr => apply h6 ϕ φ hl hr
  | not ϕ h' => apply h7 ϕ h'
