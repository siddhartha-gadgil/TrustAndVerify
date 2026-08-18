import Lean
import TrustAndVerify.TrustExt
import TrustAndVerify.Trust
open Std
open Lean Meta Elab Term Command Tactic


namespace TrustAndVerify

def transformTerms (transforms: HashMap Expr Expr) (e: Expr) : MetaM Expr := do
  Meta.transform e (post := fun subExpr => do
    match transforms.get? subExpr with
    | some newExpr => return .done newExpr
    | none => return .continue
  )

def transformTerms' (transforms: HashMap Expr Expr) (e: Expr) : MetaM Expr := do
  Meta.transform e (pre := fun subExpr => do
    match transforms.get? subExpr with
    | some newExpr => return .done newExpr
    | none => return .continue
  )


def transformDef (name newName: Name) : MetaM Syntax.Command := do
  let ident := mkIdent name
  let fullName ← resolveGlobalConstNoOverload <| ← `($ident)
  let decl := ← getConstInfo fullName
  let typeExpr := decl.type
  let .some valueExpr  := decl.value? | throwError "The declaration {name} is not a definition."
  let m ← TrustState.getTransforms
  let newTypeExpr ← transformTerms' m typeExpr
  let newValueExpr ← transformTerms' m valueExpr
  let newId := mkIdent newName
  let newTypeSyntax ← delabDetailed newTypeExpr
  let newValueSyntax ← delabDetailed newValueExpr
  let cmd ← `(command| noncomputable def $newId : $newTypeSyntax := $newValueSyntax)
  return cmd

syntax (name := mkTransforms) "abstract" ident "as" ident : command

@[command_elab mkTransforms]
def elabmkTransforms : CommandElab :=
  fun stx =>
    match stx with
    | `(abstract $name:ident as $newName:ident) => do
        let command ← liftTermElabM  do
            let cmd ← transformDef name.getId newName.getId
            TryThis.addSuggestion stx cmd
            pure cmd
        elabCommand command
    | _ => throwUnsupportedSyntax

syntax (name := facadeCmd) "facade" ident ":"  term "=:" term  : command

@[command_elab facadeCmd]
def elabFacade : CommandElab := fun stx => match stx with
  | `(facade $n:ident : $p:term =: $_:term) => do
    let cmd ← `(command| noncomputable opaque $n:ident : $p)
    liftTermElabM do
     TryThis.addSuggestion stx cmd
     TrustState.addTrust n.getId p
    elabCommand cmd
  | _ => throwUnsupportedSyntax
