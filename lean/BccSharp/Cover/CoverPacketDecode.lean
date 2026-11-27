import BccSharp.Cover.CoverAssembly
import Lean.Data.Json.Parser

set_option autoImplicit false

/-! Decoder for normalized JSON rows. Decoded rows
are inputs to the exact geometry and arithmetic checks. Importing a row
does not assert any geometric or analytic conclusion. -/

namespace BccSharp.Coulomb.CompactCover.PacketDecode
open Lean LatePackets

abbrev Parse := Except String

def rat (j : Json) : Parse ℚ := do
  match (← j.getStr?).splitOn "/" with
  | [a] =>
      let x ← a.toInt?.getDM (throw "invalid integer text")
      pure (x : ℚ)
  | [a,b] =>
      let x ← a.toInt?.getDM (throw "invalid numerator")
      let y ← b.toNat?.getDM (throw "invalid denominator")
      if y=0 then throw "zero denominator" else pure ((x : ℚ)/(y : ℚ))
  | _ => throw "invalid rational text"

def vector {α : Type} (n : Nat) (parse : Json → Parse α) (j : Json) : Parse (Fin n → α) := do
  let values ← (← j.getArr?).mapM parse
  if h : values.size=n then pure (fun i => values[i.val]'(by simpa only [h] using i.isLt))
  else throw "wrong vector dimension"

private def optional {α : Type} (parse : Json → Parse α) : Json → Parse (Option α)
  | .null => pure none
  | j => some <$> parse j

def get {α : Type} (j : Json) (k : String) (parse : Json → Parse α) : Parse α :=
  j.getObjVal? k >>= parse

def position {α : Type} (j : Json) (i : Nat) (parse : Json → Parse α) : Parse α :=
  j.getArrVal? i >>= parse

private def labelled (j : Json) : Parse InputClass := do
  match ← j.getStr? with
  | "H" => pure .other
  | "S" => pure .saturated
  | _ => throw "unknown Cover input class"

def box (j : Json) : Parse Cell := do
  if (← j.getArr?).size≠2 then throw "expected two box sides"
  pure ⟨← position j 0 (vector 8 rat),← position j 1 (vector 8 rat)⟩

private def key (j : Json) : Parse Key := do
  if (← j.getArr?).size≠4 then throw "wrong exact key arity"
  let seed ← position j 1 Json.getStr?
  let _ ← (decodeSeed seed).getDM (throw "invalid key seed")
  let address ← position j 3 (fun a => do (← a.getArr?).toList.mapM Json.getNat?)
  if !address.all (fun i => decide (i<16)) then throw "invalid key suffix"
  pure ⟨← position j 0 Json.getNat?,seed,← position j 2 Json.getNat?,address⟩

def atom (j : Json) : Parse Atom := do
  pure ⟨← get j "key" key,← get j "class" labelled,← get j "box" box,← get j "owner_hull" box⟩

private def path (j : Json) : Parse Path := do
  (← j.getArr?).toList.mapM fun node => do
    let code ← node.getNat?
    (decodeStep code).getDM (throw "invalid midpoint path digit")

private def comparison (j : Json) : Parse Comparison := do
  match ← j.getStr? with
  | "F" => pure .fcc
  | "D" => pure .deficit
  | _ => throw "unknown strict comparison"

private def mixtures (j : Json) : Parse (List (Nat × Nat)) := do
  (← j.getArr?).toList.mapM fun entry => do
    if (← entry.getArr?).size≠2 then throw "invalid corner mixture arity"
    let i ← position entry 0 Json.getNat?
    let weight ← position entry 1 Json.getNat?
    if i<256 ∧ 0<weight ∧ weight≤4096 then pure (i,weight) else throw "corner mixture outside grid"

private def half (j : Json) : Parse HalfWitness := do
  let tags ← get j "bits" Json.getStr?
  let bits ← tags.toList.toArray.mapM fun c =>
    if c='1' then pure true else if c='0' then pure false else throw "invalid half bit"
  if h : bits.size=3 then
    pure ⟨fun i => bits[i.val]'(by simpa only [h] using i.isLt),← get j "wrap" (vector 3 Json.getInt?)⟩
  else throw "wrong half-bit count"

private def jointParameters (j : Json) : Parse JointParameters := do
  pure ⟨← get j "catalogue" Json.getNat?,← get j "wrap" (vector 3 Json.getInt?),
    ← get j "quaternion" (vector 4 Json.getInt?),← get j "weight" Json.getNat?⟩

private def opticalMethod (j : Json) : Parse OpticalMethod := do
  match ← get j "method" Json.getStr? with
  | "transport" => .transport <$> get j "screen" Json.getNat?
  | "layered" => pure .layered
  | _ => throw "unknown optical method"

private def opticalResult (j : Json) : Parse OpticalResult := do
  match ← j.getStr? with
  | "fcc" => pure .fcc
  | "basin" => pure .basin
  | "directional" => pure .directional
  | "projective" => pure .projective
  | _ => throw "unknown optical result"

private def centeredMethod (j : Json) : Parse CenteredMethod := do
  match ← j.getStr? with
  | "absolute_defect" => pure .absoluteDefect
  | "anchor_slack" => pure .anchorSlack
  | _ => throw "unknown centered method"

private def payload (j : Json) : Parse Proposal := do
  match ← get j "tag" Json.getStr? with
  | "corner" => pure (.corner (← get j "compare" comparison) (← get j "steps" mixtures)
                       (← get j "hint" (optional rat)))
  | "joint" => pure (.joint (← get j "steps" mixtures) (← get j "parameters" jointParameters) (← get j "hint" rat))
  | "optical" => pure (.optical (← opticalMethod j) (← get j "result" opticalResult) (← get j "half" half) (← get j "hint" rat))
  | "triangular" => pure (.triangular (← get j "radius" rat) (← get j "hint" rat))
  | "centered" => pure (.centered (← get j "method" centeredMethod) (← get j "wrap" (vector 3 Json.getInt?))
                        (← get j "hint" rat) (← get j "slack" rat))
  | _ => throw "unknown Cover payload"

private def leaf (j : Json) : Parse LeafProposal := do
  pure ⟨← get j "ancestor" path,← get j "payload" payload⟩

def axis (j : Json) : Parse Axis := do
  let i ← j.getNat?
  if h : i<8 then pure ⟨i,h⟩ else throw "axis outside compact chart"

private def tree : Nat → Json → Parse LatePackets.Tree
  | 0,_ => throw "Cover tree exceeds decode limit"
  | fuel+1,j => do
      match ← get j "tag" Json.getStr? with
      | "hold" => pure .hold
      | "close" => .close <$> get j "leaf" leaf
      | "split" => pure (.split (← get j "axis" axis) (← get j "low" (tree fuel)) (← get j "high" (tree fuel)))
      | _ => throw "unrecognized tree node"

private def join (j : Json) : Parse Join := do
  pure ⟨← get j "corner" (optional leaf),← get j "optical" (optional leaf)⟩

private def overlay (depth : Nat) (j : Json) : Parse WholeOverlay := do
  pure ⟨← get j "primary" (tree depth),← get j "fiber" (optional (tree depth))⟩

private def stage6 (j : Json) : Parse (Row Stage6Trace) := do
  let input ← get j "input" atom
  match ← j.getObjVal? "trace" with
  | .null => pure ⟨input,.keep (← get j "held_class" labelled)⟩
  | witness =>
      let target ← witness.getObjVal? "target"
      let support ← witness.getObjVal? "support"
      let profile ← position support 2 Json.getNat?
      if h : profile<3 then
        pure ⟨input,.close ⟨← get witness "verdict" comparison,
          ← position target 0 Json.getStr?,← position target 1 Json.getNat?,
          ← position support 0 Json.getStr?,← position support 1 Json.getNat?,⟨profile,h⟩,
          ← get witness "target_box" box,← get witness "support_box" box⟩⟩
      else throw "unknown Stage6 profile"

private def row {α : Type} (parse : Json → Parse α) (j : Json) : Parse (Row α) := do
  pure ⟨← get j "input" atom,← get j "trace" parse⟩

inductive DecodedRow where
  | stage6 (value : Row Stage6Trace)
  | joint (value : Row Join)
  | adaptive (value : Row WholeOverlay)
  | round1 (value : Row LatePackets.Tree)
  | terminal (value : Row LeafProposal)

def decodeLine (line : String) (depth : Nat := 64) : Parse DecodedRow := do
  let obj ← Json.parse line
  let data ← obj.getObjVal? "record"
  match ← get obj "stage" Json.getStr? with
  | "stage6" => .stage6 <$> stage6 data
  | "joint" => .joint <$> row join data
  | "adaptive" => .adaptive <$> row (overlay depth) data
  | "round1" => .round1 <$> row (tree depth) data
  | "terminal" => .terminal <$> row leaf data
  | _ => throw "unknown Cover packet stage"

end BccSharp.Coulomb.CompactCover.PacketDecode
