import Lean

open Lean Meta Elab Term Std

namespace TrustAndVerify

structure TrustState where
  transforms : HashMap Expr Expr := HashMap.ofList [(mkConst ``IO, mkConst ``Id)]
  trusts :Array (Name × Expr) := #[]
  deriving Inhabited

inductive AddToTrustState where
  | addExprs (source target : Expr) : AddToTrustState
  | addTrust (name : Name) (expr : Expr) : AddToTrustState
  deriving Inhabited

def TrustState.add (s : TrustState) (e : AddToTrustState) : TrustState :=
  match e with
  | AddToTrustState.addExprs source target =>
    { s with transforms := s.transforms.insert source target }
  | AddToTrustState.addTrust name expr =>
        { s with trusts := s.trusts.push (name, expr) }

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

def addTrust (name : Name) (expr : Expr) : MetaM Unit := do
  TrustExt.add (AddToTrustState.addTrust name expr)

def get : MetaM TrustState := do
  let env ← getEnv
  return TrustExt.getState env

def getTransforms : MetaM (HashMap Expr Expr) := do
  let s ← get
  return s.transforms

def getTrusts : MetaM (Array (Name × Expr)) := do
  let s ← get
  return s.trusts

end TrustState

end TrustAndVerify
