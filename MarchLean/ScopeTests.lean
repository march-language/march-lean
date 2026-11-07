import MarchLean.Elab
import MarchLean.CapCheck

namespace MarchLean.ScopeTests
open Lean MarchLean.Syntax MarchLean.CapScope

private def parse (raw : String) : Except String Json :=
  let span := r#"{"file":"f","start_line":1,"start_col":1,"end_line":1,"end_col":2}"#
  let raw := ["Main", "Inner", "IO", "FileRead", "file_exists", "file_copy"].foldl
    (fun raw name => raw.replace ("\"txt\":\"" ++ name ++ "\"")
      ("\"txt\":\"" ++ name ++ "\",\"span\":" ++ span)) raw
  Json.parse raw

private def decode (decl : String) : Except String Syntax.Module := do
  let j ← parse ("{\"module\":{\"name\":{\"txt\":\"Main\"},\"decls\":[" ++ decl ++
    "]},\"schemes\":[],\"instantiations\":[],\"module_caps\":[]}")
  Elab.decodeModule j

private def needs (scopes : String) :=
  "{\"kind\":\"DNeeds\",\"paths\":[[{\"txt\":\"IO\"},{\"txt\":\"FileRead\"}]],\"scopes\":" ++ scopes ++ "}"

example : (decode (needs "[\"/etc\"]")).toOption.map (fun m =>
    m.scopeFacts.map (·.declared)) = some [[{ cap := "IO.FileRead", scope := .path true ["etc"] }]] := by native_decide
example : (decode (needs "[\"\"]")).toOption.map (fun m =>
    m.scopeFacts.map (·.declared)) = some [[{ cap := "IO.FileRead", scope := .unbounded }]] := by native_decide
example : (decode (needs "[]")).toOption.isNone = true := by native_decide
example : (decode (needs "[null]")).toOption.isNone = true := by native_decide
example : (decode (needs "[\"/etc\",\"/srv\"]")).toOption.isNone = true := by native_decide
example : (decode (needs "[\"etc\"]")).toOption.map (fun m => (CapCheck.checkCaps m).isViolation) = some true := by native_decide

private def literal := r#"{"kind":"ELit","literal":{"kind":"LitString","value":"/elsewhere"}}"#
private def app (arg : String) :=
  "{\"kind\":\"EApp\",\"fn\":{\"kind\":\"EVar\",\"name\":{\"txt\":\"file_exists\"}},\"args\":[" ++ arg ++ "]}"
private def paths (raw : String) : Except String (List (String × String)) := do
  Elab.literalPathUses (← parse raw)
example : (paths (app literal)).toOption = some [("file_exists", "/elsewhere")] := by native_decide
-- An annotated literal is not a literal call argument in March's scope pass.
example : (paths (app ("{\"kind\":\"EAnnot\",\"expr\":" ++ literal ++ "}"))).toOption = some [] := by native_decide
-- Both copy arguments are checked, in source order.
example : (paths ("{\"kind\":\"EApp\",\"fn\":{\"kind\":\"EVar\",\"name\":{\"txt\":\"file_copy\"}},\"args\":[" ++ literal ++ "," ++ literal ++ "]}")).toOption =
    some [("file_copy", "/elsewhere"), ("file_copy", "/elsewhere")] := by native_decide
private def nestedScopeVerdict (path : String) : Option Bool := do
  let outer ← (parse (needs "[\"/etc\"]")).toOption
  let inner ← (parse ("{\"kind\":\"DMod\",\"name\":{\"txt\":\"Inner\"},\"decls\":[" ++
    needs "[\"/srv\"]" ++ ",{\"kind\":\"DFn\",\"fn\":{\"clauses\":[{\"body\":" ++
    app (literal.replace "/elsewhere" path) ++ "}]}}]}" )).toOption
  let facts ← (Elab.decodeScopeFacts "Main" [outer, inner]).toOption
  pure (CapCheck.checkScopeFacts facts).isViolation

-- March checks nested literals against the preceding outer scope environment.
example : nestedScopeVerdict "/etc/a" = some false := by native_decide
example : nestedScopeVerdict "/srv/a" = some true := by native_decide
end MarchLean.ScopeTests
