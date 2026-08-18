import Lean

open Lean

namespace TrustAndVerify

/--
A connection to a LeanAide server, which can be used to query for responses.
-/
class Pipe (X Y : Type) where
  queryResponse : X → IO Y

class LeanAideUrl where
  url : String

/-- Create a `Pipe` from a URL, using `curl` to send requests. -/
@[instance_reducible]
def fromURL (url: String) : Pipe Json Json := {
  queryResponse (data: Json) := do
    let output ← IO.Process.run {cmd := "curl", args := #[url, "-X", "POST", "-H", "Content-Type: application/json", "--data", data.compress]}
    let .ok response :=
      Json.parse output | IO.throwServerError s!"Failed to parse response: \n{output}"
    return response
}

@[instance_reducible]
def pythonCli : Pipe String String := {
  queryResponse (data: String) := do
    let output ← IO.Process.run {cmd := "python3", args := #["-c", data]}
    return output.trimAscii.toString
}

macro (name := pipe) "#pipe" url:str : command => do
  let jsonId := mkIdent ``Json
  let pipeId := mkIdent ``Pipe
  `(command| instance : $pipeId $jsonId $jsonId := $url)

macro (name := pipePython) "#pipe_python" : command => do
  let stringId := mkIdent ``String
  let pipeId := mkIdent ``Pipe
  `(command| instance : $pipeId $stringId $stringId := pythonCli)

def fetch {X Y α β: Type} [pipe: Pipe X Y][Inhabited β] (encode : α → X) (decode : Y → β) (input : α) : β  :=
  let x := encode input
  let y? := unsafe unsafeIO <| pipe.queryResponse x
  match y? with
    | .ok y => decode y
    | .error e => panic! s!"Error in fetch: {e}"

end TrustAndVerify
