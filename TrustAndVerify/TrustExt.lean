import Lean

open Lean Meta Elab Term Std

namespace TrustAndVerify

structure TrustState where
  transforms : HashMap Expr Expr := HashMap.ofList [(mkConst ``IO, mkConst ``Id)]
  trusts :Array (Name × Syntax.Term) := #[]
  deriving Inhabited

inductive AddToTrustState where
  | addExprs (source target : Expr) : AddToTrustState
  | addTrust (name : Name) (stx : Syntax.Term) : AddToTrustState
  deriving Inhabited

def TrustState.add (s : TrustState) (e : AddToTrustState) : TrustState :=
  match e with
  | AddToTrustState.addExprs source target =>
    { s with transforms := s.transforms.insert source target }
  | AddToTrustState.addTrust name stx =>
        { s with trusts := s.trusts.push (name, stx) }

initialize TrustExt :
    SimpleScopedEnvExtension AddToTrustState TrustState ←
        registerSimpleScopedEnvExtension {
            initial := {}, addEntry := TrustState.add }

namespace TrustState

def addTransform (source target : Expr) : MetaM Unit := do
  let entry := AddToTrustState.addExprs source target
  TrustExt.add entry

def addNameTransform (sourceName targetName : Name) : MetaM Unit := do
  let sourceId := mkIdent sourceName
  let sourceFullName ← resolveGlobalConstNoOverload sourceId
  let targetId := mkIdent targetName
  let targetFullName ← resolveGlobalConstNoOverload targetId
  addTransform (mkConst sourceFullName) (mkConst targetFullName)

def addTrust (name : Name) (stx : Syntax.Term) : MetaM Unit := do
  TrustExt.add (AddToTrustState.addTrust name stx)

def get : MetaM TrustState := do
  let env ← getEnv
  return TrustExt.getState env

def getTransforms : MetaM (HashMap Expr Expr) := do
  let s ← get
  return s.transforms

def getTrusts : MetaM (Array (Name × Syntax.Term)) := do
  let s ← get
  return s.trusts

def viewTrusts : MetaM (Array (Name × Format)) := do
  let trusts ← getTrusts
  trusts.mapM fun (name, stx) => do
    let fmt ← ppTerm {env := ← getEnv} stx
    return (name, fmt)

end TrustState

end TrustAndVerify
