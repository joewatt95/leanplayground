import Lean.Data.Json
-- import Std.Lean.Parser
-- import Lean.Parser.Term

-- import Std.Data.Array.Basic
import Std.Lean.PersistentHashMap

macro "derive" "stuff" "for" id:ident : command
=> `(
  deriving instance
    BEq, Hashable, Repr
    -- Lean.FromJson, Lean.ToJson
  for $id
)

/-
  Set this to have a lower priority than the default so that it's automatically
  defeated by other instances, if there are any.
-/
@[default_instance 50]
instance [Repr α] : ToString α where
  toString := toString ∘ repr

declare_syntax_cat fieldDecl
syntax ident "IS" "A" term : fieldDecl

syntax
  "DECLARE" ident ("IS" "A" ident)?
  ("HAS" fieldDecl,+),*
  : command

macro_rules
  | `(DECLARE $className)
  => `(
    structure $className
    derive stuff for $className
  )
  | `(DECLARE $className IS A $superClassName) => `(
    structure $className extends $superClassName
    derive stuff for $className
  )

  | `(DECLARE $className HAS $fieldName:ident IS A $fieldType:term)
  => `(
      structure $className where
        { $fieldName : $fieldType }
      derive stuff for $className
  )

  | `(
      DECLARE $className IS A $superClassName
      HAS $fieldName:ident IS A $fieldType
    )
  => `(
    structure $className extends $superClassName where
      { $fieldName : $fieldType }
    derive stuff for $className
  )

declare_syntax_cat fieldDef
syntax term "IS" "THE" ident : fieldDef

-- syntax term "IS" "THE" Lean.Parser.Term.structInstLVal : fieldDef

-- set_option trace.Elab.command true in
syntax
  "DEFINE" ident "IS" "A" ident
  ("HAS" fieldDef,+),*
  : command

macro_rules
  | `(DEFINE $id IS A $className)
  => `(
    def $id : $className where
  )
  | `(DEFINE $id IS A $className HAS $fieldVal:term IS THE $fieldName:ident)
  => `(
    def $id : $className where
      $fieldName := $fieldVal
  )

-- open Lean.Parser.Command

-- declare_syntax_cat enums
-- syntax ident : enums
-- syntax ident "PLUS" enums : enums

syntax "DECLARE" ident "IS" sepBy(ident, "PLUS") : command

macro_rules
  | `( DECLARE $name:ident IS $[$ids:ident] PLUS* )
  => `(
    inductive $name where
      $[| $ids:ident]*
    derive stuff for $name

    deriving instance Ord for $name
  )

-- instance : ToStream (Lean.PArray T) (List T) where
--   toStream xs := xs.toList

-- instance [BEq T] : BEq (Lean.PArray T) where
--   beq xs ys := Id.run <| do
--     for x in xs, y in ys do
--       if x != y then return false
--     return true

variable [BEq α] [Hashable α]

instance [BEq β] : BEq (Lean.PHashMap α β) where
  beq m0 m1 := m0.toArray == m1.toArray

-- instance [DecidableEq α] [DecidableEq β] : DecidableEq (Lean.PHashMap α β) :=
--   λ m0 m1 => decEq m0.toArray m1.toArray 

instance [Hashable β] : Hashable (Lean.PHashMap α β) where
  hash := hash ∘ Lean.PersistentHashMap.toArray

instance [Repr α] [Repr β] : Repr (Lean.PHashMap α β) where
  reprPrec := reprPrec ∘ Lean.PersistentHashMap.toArray

-- instance [Ord (List (α × β))] : Ord (Lean.PHashMap α β) where
--   compare m0 m1 := compare m0.toList m1.toList

-- def List.toPHashMap (xs : List (α × β)) : Lean.PHashMap α β :=
--   xs.foldl (init := Lean.PersistentHashMap.empty) <|
--     λ hashMap (k, v) => hashMap.insert k v

notation "MAP" "FROM" key "TO" val => Lean.PHashMap key val
notation x "EQUALS" y => x == y

syntax
  "§" ident
  "GIVEN" ident "IS" "A" term ","
  "DECIDE" ident "IF" term
  : command

macro_rules
  | `(
    § $ruleName
    GIVEN $var IS A $type,
    DECIDE $concl IF $hypo
  )
  => `(
    section
    -- BabyL4-esq declaration of the uninterpreted predicate.
    axiom $concl : $type → Prop

    -- Rule definition.
    def $ruleName :=
      ∀ $var : $type, $hypo → $concl $var
    end
  )

-- #eval
--   "abc's"
--     |> Lean.mkIdent
--     |>.raw
--     |> toString
--     |>.drop 1
--     |>.splitOn (sep := "'s")
--     |>.head!
--     |> Lean.mkIdent

macro "THE" fieldName:ident "OF" record:term : term => `($record.$fieldName)

macro recordName:ident fieldName:ident : term =>
  match recordName |>.raw |> toString |>.drop 1 |>.splitOn "'s" with
    | [recordName, ""] =>
      let recordNameIdent := Lean.mkIdent recordName
    -- In this case, recordName is an identifier ending with 's, eg: person's
      `($recordNameIdent.$fieldName)
    | _ => `($recordName $fieldName)

set_option trace.Elab.command true
set_option trace.Elab.step true

DECLARE Agreement

DECLARE Role IS Borrower PLUS Lender

-- #eval [Role.Borrower .. Role.Lender]

DECLARE Party
HAS role IS A Role

DECLARE Loan IS A Agreement
HAS Parties IS A MAP FROM Role TO Party

DEFINE B IS A Party
HAS Role.Borrower IS THE role

DEFINE L IS A Party
HAS Role.Lender IS THE role

DEFINE SimpleLoan IS A Loan
HAS Lean.PersistentHashMap.ofArray #[(Role.Borrower, B), (Role.Lender, L)] IS THE Parties

-- #eval SimpleLoan

§ testRule
GIVEN p IS A Party,
DECIDE isLender IF p's role EQUALS Role.Lender

-- #print isLender
-- #print testRule

-- #eval Lean.Macro.expandMacro? `(0 EQUALS 0)
-- #check Lean.Macro.expandMacro? -- $ Lean.TSyntax.raw