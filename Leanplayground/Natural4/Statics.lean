import Lean.Data.Json
-- import Lean.Data.Parsec
-- import Lean.Parser.Term
import Std.Data.HashMap.Basic
import Std.Lean.PersistentHashMap

import Leanplayground.Natural4.Attrs

-- import Std.Lean.Parser

-- import Std.Data.Array.Basic
namespace Statics

macro "derive" "stuff" "for" id:ident : command
=> `(
  deriving instance
    BEq, Hashable, Repr,
    Lean.FromJson, Lean.ToJson
  for $id
)

/-
  Set this to have a lower priority than the default so that it's automatically
  defeated by other instances, if there are any.
-/
@[default_instance low]
instance [Repr α] : ToString α where
  toString := toString ∘ repr

syntax
  "DECLARE" ident ("IS" "A" ident)?
  ("HAS" many1Indent(ident "IS" "A" term ppLine))?
  : command

macro_rules
| `(DECLARE $className $[IS A $superClassName]?) =>
  match superClassName with
  | none => `(
    structure $className
    derive stuff for $className
  )
  | some superClassName => `(
    structure $className extends $superClassName
    derive stuff for $className

    -- This Coe typeclass for implicit coercions allows us to model subtyping.
    -- instance : Coe $className $superClassName where
    --   coe x := x.$(Lean.mkIdent s!"to{superClassName |> toString |>.drop 1}")
  )
| `(
  DECLARE $className $[IS A $superClassName]?
  HAS $[$fieldName:ident IS A $fieldType:term]*
) => match superClassName with
  | none => `(
    structure $className where
      $[{ $fieldName : $fieldType }]*
    derive stuff for $className
  )
  | some superClassName => `(
    structure $className extends $superClassName where
      $[{ $fieldName : $fieldType }]*
    derive stuff for $className

    -- instance : Coe $className $superClassName where
    --   coe x := x.$(Lean.mkIdent s!"to{superClassName |> toString |>.drop 1}")
  )

-- syntax term "IS" "THE" Lean.Parser.Term.structInstLVal : fieldDef

-- set_option trace.Elab.command true in

syntax
  "DEFINE" ident "IS" "A" term
  ("HAS" many1Indent(term "IS" "THE" term ppLine))?
  : command

macro_rules
| `(DEFINE $id IS A $className)
=> `(
  def $id : $className where
)
| `(DEFINE $id IS A $className HAS $[$fieldVal:term IS THE $fieldName:ident]*)
=> `(
  def $id : $className where
    $[$fieldName := $fieldVal]*
)

-- open Lean.Parser.Command

-- declare_syntax_cat enums
-- syntax ident : enums
-- syntax ident "PLUS" enums : enums

syntax "DECLARE" ident "IS" sepBy1(ident, "OR") : command

-- notation t0 "AND" t1 => t0 ∧ t1
-- notation t0 "OR" t1 => t0 ∨ t1

infixr:65 "AND" => And
infixr:65 "OR" => Or

macro_rules
| `(DECLARE $name:ident IS $[$ids:ident] OR*)
=> `(
  inductive $name where
    $[| $ids:ident]*
  derive stuff for $name

  deriving instance Ord for $name
)

syntax term "OF" sepBy1(term, ",") : term
macro_rules
| `($fn OF $[$arg:term],*) => `($fn $arg*)

-- instance : ToStream (Lean.PArray T) (List T) where
--   toStream xs := xs.toList

-- instance [BEq T] : BEq (Lean.PArray T) where
--   beq xs ys := Id.run <| do
--     for x in xs, y in ys do
--       if x != y then return false
--     return true
section
variable [BEq α] [Hashable α]

instance [BEq β] : BEq (Lean.PHashMap α β) where
  beq m0 m1 := m0.toArray == m1.toArray

instance [BEq β] : BEq (Std.HashMap α β) where
  beq m0 m1 := m0.toArray == m1.toArray

-- instance [DecidableEq α] [DecidableEq β] : DecidableEq (Lean.PHashMap α β) :=
--   λ m0 m1 => decEq m0.toArray m1.toArray

instance [Hashable β] : Hashable (Lean.PHashMap α β) where
  hash := hash ∘ Lean.PersistentHashMap.toArray

instance [Hashable β] : Hashable (Std.HashMap α β) where
  hash := hash ∘ Std.HashMap.toArray

instance [Repr α] [Repr β] : Repr (Lean.PHashMap α β) where
  reprPrec := reprPrec ∘ Lean.PersistentHashMap.toArray

instance [Repr α] [Repr β] : Repr (Std.HashMap α β) where
  reprPrec := reprPrec ∘ Std.HashMap.toArray

end

-- instance [Ord (List (α × β))] : Ord (Lean.PHashMap α β) where
--   compare m0 m1 := compare m0.toList m1.toList

-- def List.toPHashMap (xs : List (α × β)) : Lean.PHashMap α β :=
--   xs.foldl (init := Lean.PersistentHashMap.empty) <|
--     λ hashMap (k, v) => hashMap.insert k v

notation "MAP" "FROM" key "TO" val => Array (key × val)
-- Lean.PHashMap key val
infix:50 "EQUALS" => (. == .)

syntax Lean.binderIdent "FROM" term "TO" term : term

syntax "FOR EVERY" many1(ident <|> bracketedBinder) "," term : term
macro_rules
| `(FOR EVERY $binders:ident, $prop) =>
  `(∀ $binders, $prop)
| `(FOR EVERY $binders:bracketedBinder, $prop) =>
  `(∀ $binders, $prop)

syntax "THERE" "IS" "SOME" term "SUCH" "THAT" term : term
syntax "THERE" "IS" "SOME" Lean.explicitBinders "SUCH" "THAT" term : term
macro_rules
| `(THERE IS SOME $f:binderIdent FROM $α TO $β SUCH THAT $prop) =>
  `(∃ ($f : $α → $β), $prop)
| `(THERE IS SOME $var:explicitBinders SUCH THAT $prop) =>
  `(∃ $var, $prop)

syntax "RELATION" "BETWEEN" sepBy1(term, "AND") : term
macro_rules
| `(RELATION BETWEEN $t0 AND $t1) => `($t0 → $t1 → Prop)

notation relation "RELATES" t0 "TO" t1 => relation t0 t1

-- Horn claues.
syntax
  "§" ident
  ("GIVEN" manyIndent(ident "IS" "A" term ppLine))?
  "DECIDE" term "IF" term
  : command

macro_rules
| `(
  § $ruleName
  DECIDE $concl:ident IF $hypo
) => `(
  @[constitutive]
  abbrev $ruleName : Prop := $hypo → $concl
)
| `(
  § $ruleName
  GIVEN $[$var:ident IS A $type]*
  DECIDE $concl:ident OF $[$arg],* IF $hypo
) => `(
  -- Extract signature of the uninterpreted predicate.
  axiom $concl $[($var : $type)]* : Prop

  -- Rule definition.
  @[constitutive]
  abbrev $ruleName : Prop :=
    ∀ $[($var : $type)]*, $hypo → ($concl OF $[$arg],*)
)
| `(
  § $ruleName
  GIVEN $[$var:ident IS A $type]*
  DECIDE $concl:term IF $hypo
) => `(
  @[constitutive]
  abbrev $ruleName : Prop := ∀ $[($var : $type)]*, $hypo → $concl
)

macro "THE" fieldName:ident "OF" record:term : term => `($record.$fieldName)

-- macro recordName:ident fieldName:ident : term =>
--   match recordName |> toString |>.drop 1 |>.splitOn "'s" with
--   | [recordName, ""] =>
--     -- In this case, recordName is an identifier ending with 's, eg: person's
--     let recordNameIdent := Lean.mkIdent recordName
--     `($recordNameIdent.$fieldName)
--   | _ => `($recordName $fieldName)

end Statics
