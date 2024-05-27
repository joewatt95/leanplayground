import Lean
import Batteries.Data.HashMap.Basic

-- See: https://github.com/arthurpaulino/lean4-metaprogramming-book/blob/d381cba5681582407b46fe554b0e1504d9f28132/lean/extra/attrs/tag.lean

open Lean Meta System Std Elab Command

initialize constitutive : TagAttribute ←
  registerTagAttribute `constitutive "Tag for constitutive rules."

initialize regulative : TagAttribute ←
  registerTagAttribute `regulative "Tag for regulative rules."

namespace Attrs

def listAll (tagAttr : TagAttribute) :
  MetaM <| Batteries.HashMap Name Expr := do
  let env ← getEnv
  let mut result := .empty
  for declName in tagAttr.ext.getState env do
    -- Lookup declName in the environment, then compute (full) head normal form
    -- and pretty print.
    -- Note that we need to fully normalize under binders and constructors when
    -- transpiling to other outputs.
    try
      let some <| .defnInfo {value, ..} := env.find? declName
        | throwError "
          Internal error: {declName} is not a constant defn.
          Double check the macro-expansion for constitutive rules!"

      let reduced ← reduce value

      result := result.insert declName reduced

      logInfo m!"
        Found rule: {declName}
        Defn: {← ppExpr reduced}"

    catch e =>
      logError m!"
        Error occured while listing rules:
        {e.toMessageData}"

  trace[Meta.debug] "
    Log:
    {(← Core.getMessageLog).toList.map BaseMessage.data}"

  return result

end Attrs
