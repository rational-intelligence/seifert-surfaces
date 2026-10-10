import Lean
open Lean
namespace ExactPaidSource
partial def nameJson : Name → Json
  | .anonymous => Json.arr #[toJson "anonymous"]
  | .str p s => Json.arr #[toJson "str",nameJson p,toJson s]
  | .num p n => Json.arr #[toJson "num",nameJson p,toJson n]
partial def levelJson : Level → Json
  | .zero => Json.arr #[toJson "zero"]
  | .succ l => Json.arr #[toJson "succ",levelJson l]
  | .max a b => Json.arr #[toJson "max",levelJson a,levelJson b]
  | .imax a b => Json.arr #[toJson "imax",levelJson a,levelJson b]
  | .param n => Json.arr #[toJson "param",nameJson n]
  | .mvar n => Json.arr #[toJson "mvar",nameJson n.name]
def binderJson : BinderInfo → Json
  | .default => toJson "default"
  | .implicit => toJson "implicit"
  | .strictImplicit => toJson "strictImplicit"
  | .instImplicit => toJson "instImplicit"
def dataJson : DataValue → Json
 | .ofString s => Json.arr #[toJson "string", toJson s]
 | .ofBool b => Json.arr #[toJson "bool", toJson b]
 | .ofName n => Json.arr #[toJson "name", nameJson n]
 | .ofNat n => Json.arr #[toJson "nat", toJson n]
 | .ofInt n => Json.arr #[toJson "int", toJson n]
 | .ofSyntax _ => Json.arr #[toJson "UNSUPPORTED_SYNTAX_METADATA"]
def metadataJson (m : MData) : Json := toJson (m.entries.map (fun (n,v) => Json.arr #[nameJson n,dataJson v]))
partial def exprJsonNode (e : Expr) : StateM (Std.HashMap ExprStructEq Nat × Array Json) Nat := do
  if let some n := (← get).1[ExprStructEq.mk e]? then return n
  let node ← match e with
    | .mdata m b => pure <| Json.arr #[toJson "mdata",metadataJson m,toJson (← exprJsonNode b)]
    | .bvar n => pure <| Json.arr #[toJson "bvar",toJson n]
    | .fvar n => pure <| Json.arr #[toJson "fvar",nameJson n.name]
    | .mvar n => pure <| Json.arr #[toJson "mvar",nameJson n.name]
    | .sort l => pure <| Json.arr #[toJson "sort",levelJson l]
    | .const n ls => pure <| Json.arr #[toJson "const",nameJson n,toJson (ls.map levelJson)]
    | .app f a => pure <| Json.arr #[toJson "app",toJson (← exprJsonNode f),toJson (← exprJsonNode a)]
    | .lam n t b bi => pure <| Json.arr #[toJson "lam",nameJson n,toJson (← exprJsonNode t),toJson (← exprJsonNode b),binderJson bi]
    | .forallE n t b bi => pure <| Json.arr #[toJson "forall",nameJson n,toJson (← exprJsonNode t),toJson (← exprJsonNode b),binderJson bi]
    | .letE n t v b nd => pure <| Json.arr #[toJson "let",nameJson n,toJson (← exprJsonNode t),toJson (← exprJsonNode v),toJson (← exprJsonNode b),toJson nd]
    | .lit (.natVal n) => pure <| Json.arr #[toJson "nat",toJson n]
    | .lit (.strVal s) => pure <| Json.arr #[toJson "string",toJson s]
    | .proj n i b => pure <| Json.arr #[toJson "proj",nameJson n,toJson i,toJson (← exprJsonNode b)]
  let (cache,nodes) ← get
  let idx := nodes.size
  set (cache.insert ⟨e⟩ idx,nodes.push node)
  return idx

def exprJson (e : Expr) : Json :=
  let (root,(_,nodes)) := (exprJsonNode e).run ({},#[])
  Json.mkObj [("root",toJson root),("nodes",toJson nodes)]

partial def nameFromJson (j : Json) : Except String Name := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "anonymous" => return .anonymous
  | "str" => return .str (← nameFromJson a[1]!) (← a[2]!.getStr?)
  | "num" => return .num (← nameFromJson a[1]!) (← fromJson? a[2]!)
  | _ => throw "invalid name"
partial def levelFromJson (j : Json) : Except String Level := do
  let a ← j.getArr?
  match ← a[0]!.getStr? with
  | "zero" => return .zero
  | "succ" => return .succ (← levelFromJson a[1]!)
  | "max" => return .max (← levelFromJson a[1]!) (← levelFromJson a[2]!)
  | "imax" => return .imax (← levelFromJson a[1]!) (← levelFromJson a[2]!)
  | "param" => return .param (← nameFromJson a[1]!)
  | _ => throw "invalid level or metavariable"
def binderFromJson (j : Json) : Except String BinderInfo := do
  match ← j.getStr? with
  | "default" => return .default
  | "implicit" => return .implicit
  | "strictImplicit" => return .strictImplicit
  | "instImplicit" => return .instImplicit
  | _ => throw "invalid binder"

def dataFromJson (j : Json) : Except String DataValue := do
 let a ← j.getArr?
 match ← a[0]!.getStr? with
 | "string" => return .ofString (← a[1]!.getStr?)
 | "bool" => return .ofBool (← fromJson? a[1]!)
 | "name" => return .ofName (← nameFromJson a[1]!)
 | "nat" => return .ofNat (← fromJson? a[1]!)
 | "int" => return .ofInt (← fromJson? a[1]!)
 | _ => throw "unsupported metadata (preservation required)"
def metadataFromJson (j : Json) : Except String MData := do
 let entries ← (← j.getArr?).toList.mapM fun j => do
  let a ← j.getArr?
  return ((← nameFromJson a[0]!), (← dataFromJson a[1]!))
 return ⟨entries⟩
def exprFromJson (j : Json) : Except String Expr := do
  let nodes ← (← j.getObjVal? "nodes").getArr?
  let mut decoded : Array Expr := #[]
  for n in nodes do
    let a ← n.getArr?
    let get (i : Nat) : Except String Expr := do
      let k ← fromJson? (α := Nat) a[i]!
      if k < decoded.size then return decoded[k]! else throw "forward or invalid node reference"
    let e ← match ← a[0]!.getStr? with
      | "mdata" => pure (.mdata (← metadataFromJson a[1]!) (← get 2))
      | "bvar" => pure (.bvar (← fromJson? a[1]!))
      | "sort" => pure (.sort (← levelFromJson a[1]!))
      | "const" => pure (.const (← nameFromJson a[1]!) (← ((← a[2]!.getArr?).toList.mapM levelFromJson)))
      | "app" => pure (.app (← get 1) (← get 2))
      | "lam" => pure (.lam (← nameFromJson a[1]!) (← get 2) (← get 3) (← binderFromJson a[4]!))
      | "forall" => pure (.forallE (← nameFromJson a[1]!) (← get 2) (← get 3) (← binderFromJson a[4]!))
      | "let" => pure (.letE (← nameFromJson a[1]!) (← get 2) (← get 3) (← get 4) (← fromJson? a[5]!))
      | "nat" => pure (.lit (.natVal (← fromJson? a[1]!)))
      | "string" => pure (.lit (.strVal (← a[1]!.getStr?)))
      | "proj" => pure (.proj (← nameFromJson a[1]!) (← fromJson? a[2]!) (← get 3))
      | _ => throw "invalid expression or open metavariable/free variable"
    decoded := decoded.push e
  let root ← j.getObjValAs? (α := Nat) "root"
  if root < decoded.size then return decoded[root]! else throw "invalid root"
end ExactPaidSource
