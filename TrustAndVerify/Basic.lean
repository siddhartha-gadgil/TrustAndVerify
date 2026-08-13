import Lean
open Lean Meta Elab Term Command Tactic

def hello := "world"

syntax commandSeq := sepBy1IndentSemicolon(command)

namespace TrustAndVerify

variable [Monad m] [MonadQuotation m]

def toCommandSeq : Array (TSyntax `command) → m (TSyntax `commandSeq)
  | cs => `(commandSeq| $cs*)

def commands : TSyntax `commandSeq → Array (TSyntax `command)
  | `(commandSeq| $cs*) => cs
  | _ => #[]

def delabDetailed (e: Expr) : MetaM Syntax.Term := withOptions (fun o₁ =>
                    let o₂ := pp.motives.pi.set o₁ true
                    let o₃ := pp.numericTypes.set o₂ true
                    let o₅ := pp.deepTerms.set o₃ true
                    let o₆ := pp.funBinderTypes.set o₅ true
                    let o₇ := pp.piBinderTypes.set o₆ true
                    let o₈ := pp.letVarTypes.set o₇ true
                    let o₉ := pp.coercions.types.set o₈ true
                    let o' := pp.motives.nonConst.set o₉ true
                    let o'' := pp.fullNames.set o' true
                    pp.unicode.fun.set o'' true) do
              PrettyPrinter.delab e

end TrustAndVerify
