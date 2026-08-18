import Lean
import TrustAndVerify.TrustExt
import TrustAndVerify.Trust
open Std
open Lean Meta Elab Term Command Tactic


namespace TrustAndVerify

def transformMappedTerms (transforms: HashMap Expr Expr) (e: Expr) : MetaM Expr := do
  Meta.transform e (post := fun subExpr => do
    match transforms.get? subExpr with
    | some newExpr => return .done newExpr
    | none => return .continue
  )

def transformTerm (e : Expr) : MetaM Expr := do
  let m ← TrustState.getTransforms
  transformMappedTerms m e

def transformDef (name newName: Name) : MetaM Syntax.Command := do
  let ident := mkIdent name
  let fullName ← resolveGlobalConstNoOverload <| ← `($ident)
  let decl := ← getConstInfo fullName
  let typeExpr := decl.type
  let .some valueExpr  := decl.value? | throwError "The declaration {name} is not a definition."
  let m ← TrustState.getTransforms
  let newTypeExpr ← transformMappedTerms m typeExpr
  let newValueExpr ← transformMappedTerms m valueExpr
  let newId := mkIdent newName
  let newTypeSyntax ← delabDetailed newTypeExpr
  let newValueSyntax ← delabDetailed newValueExpr
  let cmd ← `(command| noncomputable def $newId : $newTypeSyntax := $newValueSyntax)
  return cmd

def transformTerms' (transforms: HashMap Expr Expr) (e: Expr) : MetaM Expr := do
  Meta.transform e (pre := fun subExpr => do
    match transforms.get? subExpr with
    | some newExpr => return .done newExpr
    | none => return .continue
  )


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

open Lean Meta Elab Term Command Tactic
def mkFacadeExpr (name : Ident) (type : Expr) : MetaM (TSyntax `command) := do
  let type ← transformTerm type
  let typeStx ← delabDetailed type
  let cmd ← `(command| noncomputable opaque $name:ident : $typeStx)
  return cmd

def mkFacadeStx (name: Ident) (value: Term) : TermElabM (TSyntax `command) := do
  let valueExpr ← elabTerm value none
  let type ← inferType valueExpr
  mkFacadeExpr name type

syntax (name := facadeCmd) "facade" ident "of"  term : command
@[command_elab facadeCmd]
def elabFacadeOf : CommandElab := fun stx => match stx with
  | `(facade $n:ident of $p:term) => do
    let cmd ← liftTermElabM do
      mkFacadeStx n p
    liftTermElabM do
     TryThis.addSuggestion stx cmd
    elabCommand cmd
  | _ => throwUnsupportedSyntax

syntax (name := facadeAttr) "facade" ident : attr

def facadeKeyM : Syntax → CoreM Ident
  | `(attr| facade $id) => return id
  | _ => throwError "invalid facade attribute"

initialize registerBuiltinAttribute {
  name := `facadeAttr
  descr := "Lean facade attribute"
  add := fun decl stx kind => MetaM.run' do
    let declTy := (← getConstInfo decl).type
    let name ← facadeKeyM stx
    let cmd ← mkFacadeExpr name declTy
    liftCommandElabM do
     elabCommand cmd
}
