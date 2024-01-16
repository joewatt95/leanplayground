import Verso.Genre.Blog

import Auto.Tactic
import Mathlib.Tactic.SlimCheck

open Verso.Genre
open Verso.Genre.Blog (Post Page label ref lean leanInit leanOutput)

-- set_option pp.rawOnError true
set_option maxRecDepth 600

#doc (Page)
  "Syntax, semantics, implementation and end user facing documentation for L4"
=>

# Overview
This (work-in-progress) document is a
[literate programming](https://en.wikipedia.org/wiki/Literate_programming)
file that contains:
- Implementation and developer-oriented documentation of the syntax and
  semantics of L4 in Lean.
- End user-oriented documentation on how to write L4.

```leanInit runningEg
```

# Implementation and documentation for syntax and semantics of L4

## L4 classes

### Syntax

Using Lean's built-in parser combinator library, we define the syntax of
L4 classes as follows.

```lean runningEg name := classSyntax
syntax
  "DECLARE" ident ("IS" "A" ident)?
  ("HAS" many1Indent(ident "IS" "A" term ppLine))?
  : command
```

Note here that `many1Indent` is an _indentation-aware_ combinator.

### Semantics and implementation

The semantics of classes is given as the following macro rewriting rule.

```lean runningEg
macro_rules
| `(DECLARE $className $[IS A $superClassName]?) =>
  match superClassName with
  | none => `(
    structure $className
  )
  | some superClassName => `(
    structure $className extends $superClassName
  )
| `(
  DECLARE $className $[IS A $superClassName]?
  HAS $[$fieldName:ident IS A $fieldType:term]*
) => match superClassName with
  | none => `(
    structure $className where
      $[{ $fieldName : $fieldType }]*
  )
  | some superClassName => `(
    structure $className extends $superClassName where
      $[{ $fieldName : $fieldType }]*
  )
```

#### Future work on subtyping and other RDF features
See [this](https://arxiv.org/pdf/2003.03785.pdf) paper, which is part of the
[main author](https://zunction.github.io/)'s PHD thesis on embedding knowledge
graphs into dependent type theories (primarily Coq) and using its proof
automation facilities to reason about SPARQL.

A similar technique may work here since this implements L4 as an embedded DSL
in Lean and Lean's type theory is similar to Coq.
With such an encoding, explainability can be obtained in the form of traces
output by the backward chaining proof search tactic
[Aesop](https://github.com/leanprover-community/aesop).

However, the key concern is that their construction leverages Coq's
_proof-relevance_ but I (Joe) believe Lean's type theory is _proof-irrelevant_.
This needs more investigation.

## Other types
TODO: enums

## Constitutive Rules

### Auxiliary syntax and semantics

#### Syntax for boolean conditionals
```lean runningEg
infixr:65 "AND" => And
infixr:65 "OR" => Or
```

#### Syntax and semantics of function application

```lean runningEg
syntax term "OF" sepBy1(term, ",") : term
macro_rules
| `($fn OF $[$arg:term],*) => `($fn $arg*)
```

### Syntax

```lean runningEg
syntax
  "§" ident
  ("GIVEN" manyIndent(ident "IS" "A" term ppLine))?
  "DECIDE" term "IF" term
  : command
```

### Semantics and implementation

Semantically, we interpret constitutive rules using the type/category
`Prop`, that is `〚ConstitutiveRule 〛= Prop`.
This is performed by the following macro rewriting rules.

```lean runningEg
macro_rules
| `(
  § $ruleName
  DECIDE $concl:ident IF $hypo
) => `(
  def $ruleName : Prop := $hypo → $concl
)
| `(
  § $ruleName
  GIVEN $[$var:ident IS A $type]*
  DECIDE $concl:ident OF $[$arg],* IF $hypo
) => `(
  -- Extract signature of the uninterpreted predicate.
  axiom $concl $[($var : $type)]* : Prop

  -- Rule definition.
  def $ruleName : Prop :=
    ∀ $[($var : $type)]*, $hypo → ($concl OF $[$arg],*)
)
| `(
  § $ruleName
  GIVEN $[$var:ident IS A $type]*
  DECIDE $concl:term IF $hypo
) => `(
  def $ruleName : Prop := ∀ $[($var : $type)]*, $hypo → $concl
)
```

### Property-based testing

#### Syntax and semantics

```lean runningEg
macro "#TEST" ruleName:ident : command =>
  `(example : $ruleName := by unfold $ruleName; slim_check)
```

### SMT solver integration

#### Syntax and semantics

```lean runningEg
set_option auto.smt true
set_option auto.smt.trust true
set_option auto.smt.solver.name "z3"

set_option trace.auto.smt.printCommands true
set_option trace.auto.smt.result true

macro "#SMT" ruleName:ident : command =>
  `(example : $ruleName := by unfold $ruleName; auto)
```

# End-user documentation

L4 is a strongly typed language where one can define objects in the style of
OOP and write business rules with them.

For example, we can first declare a `Person` clas as follows.

TODO: Find out why using the word "class" breaks syntax highlighting.

```lean runningEg
DECLARE Person
HAS age IS A Int
    bankBalance IS A Int
```

TODO: How to get syntax highlighting working? Maybe need to define custom
elaborator for L4 code blocks.

Next, we can define the following rule,
which says that given `Person`s `p1` and `p2`,
`p1` can only transfer money to `p2` if all of the following hold:
- `p1`'s bank balance exceeds that of `p2`
- both of them have a _non-negative_ bank balance.

```lean runningEg
-- def increaseBankBalance : Person → Int → Person
-- | p, n => { p with bankBalance := p.bankBalance + n }

§ canTransferMoney
GIVEN
  p1 IS A Person
  p2 IS A Person
DECIDE hasMoreMoneyInBankThan OF p1, p2
IF (p1.bankBalance ≥ p2.bankBalance)
AND (p2.bankBalance ≥ 0)
```

TODO:
- Fix the parser so the above parens aren't needed.
- Maybe try implementing `'s` syntax.
  - Note that this can be tricky due to:
    - Potential ambiguous parsing issues.
    - Meta-programming level transformations needed to pattern match on the
      string of the identifier `t's` as in `t's x` to desugar it into `t.x`.

## Namespaces and sections

Namespaces can be declared and nested as follows.


```lean runningEg
namespace outer_section

  namespace inner_section

    DECLARE InnerClass
    HAS var IS A Int

  end inner_section

end outer_section
```

Note that things declared and defined in namespaces are not visible in the
outer scope, so that the following is errorneous:

```lean runningEg error := true
§ badRule
GIVEN x IS A InnerClass
DECIDE x = x IF True
```

## Functional programming, OOP dot notation, property-based testing

Here is an example of the `#TEST ⟪ruleName⟫` command for property-based
testing.

Note in the example below that L4 supports _functional programming_ constructs,
as well as _object-oriented_ inspired dot notation.

```lean runningEg error := true
§ badRule
GIVEN xs IS A List OF Int
DECIDE xs.sum = xs.foldl (λ x y ↦ x * y) 0
IF True

#TEST badRule
```

## SMT solver integration

```lean runningEg error := true
§ badRule
GIVEN xs IS A List OF Int
DECIDE xs.sum = 0
IF True

#SMT badRule
```
