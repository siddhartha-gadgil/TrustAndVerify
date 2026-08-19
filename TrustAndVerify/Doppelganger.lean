import Lean
import TrustAndVerify.TrustExt
import TrustAndVerify.Trust
open Std
open Lean Meta Elab Term Command Tactic


namespace TrustAndVerify

def transformMappedTerms (transforms: Array (Expr × Expr)) (e: Expr) : MetaM Expr := do
  Meta.transform e (post := fun subExpr => do
    match transforms.find? (fun (source, _) => source == subExpr) with
    | some (_, newExpr) => return .done newExpr
    | none => return .continue
  )

def transformTerm (e : Expr) (flip: Bool) : MetaM Expr := do
  let m ← if flip then TrustState.getFlippedTransforms else TrustState.getTransforms
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
  let cmd ← `(command| @[grind .] noncomputable def $newId : $newTypeSyntax := $newValueSyntax)
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
            if ← tryThisEnabled then
              TryThis.addSuggestion stx cmd
            pure cmd
        elabCommand command
    | _ => throwUnsupportedSyntax

open Lean Meta Elab Term Command Tactic
def mkFacadeExpr (name : Ident) (type : Expr) : MetaM (TSyntax `command) := do
  let type ← transformTerm type false
  let typeStx ← delabDetailed type
  let cmd ← `(command| noncomputable opaque $name:ident : $typeStx)
  return cmd

def mkFacadeStx (name: Ident) (value: Ident) : TermElabM (TSyntax `command) := do
  let valueExpr ← elabTerm value none
  let type ← inferType valueExpr
  mkFacadeExpr name type

syntax (name := facadeCmd) "facade" ident "of"  ident : command
@[command_elab facadeCmd]
def elabFacadeOf : CommandElab := fun stx => match stx with
  | `(facade $n:ident of $p:ident) => do
    let cmd ← liftTermElabM do
      mkFacadeStx n p
    liftTermElabM do
     TryThis.addSuggestion stx cmd
    elabCommand cmd
    liftTermElabM do
     TrustState.addNameTransform p.getId n.getId
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
    TrustState.addNameTransform decl name.getId
}

syntax (name := abstractAttr) "abstract_as" ident : attr

def abstractKeyM : Syntax → CoreM Ident
  | `(attr| abstract_as $id) => return id
  | _ => throwError "invalid abstract attribute"

initialize registerBuiltinAttribute {
  name := `abstractAttr
  descr := "Lean abstract attribute"
  add := fun decl stx kind => MetaM.run' do
    let newName ← abstractKeyM stx
    let newName := newName.getId
    let cmd ← transformDef decl newName
    liftCommandElabM do
     elabCommand cmd
    TrustState.addNameTransform decl newName
}

syntax (name := referenceAttr) "reference_for" ident : attr

def referenceKeyM : Syntax → CoreM Ident
  | `(attr| reference_for $id) => return id
  | _ => throwError "invalid reference attribute"

initialize registerBuiltinAttribute {
  name := `referenceAttr
  descr := "Lean reference attribute"
  add := fun decl stx kind => MetaM.run' do
    let name ← referenceKeyM stx
    TrustState.addNameTransform name.getId decl
}
