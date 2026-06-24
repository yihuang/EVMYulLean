/-
CFG Analysis — Control-Flow Graph for Venom IR

Port of vyper-hol/venom/analysis/cfg/defs/cfgDefsScript.sml

Computes successor/predecessor maps and DFS traversal order for
a Venom IR function.
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Semantics
import EvmYul.Venom.Exec

namespace EvmYul.Venom.Codegen

/-- Extract label from an Operand, if it is a Label. -/
def getLabel : Operand → Option String
  | Operand.Label l => some l
  | _ => none

/-- Get successor labels of a terminator instruction. -/
def getSuccessors (inst : Instruction) : List String :=
  if !isTerminator inst.opcode then []
  else inst.operands.filterMap getLabel

/-- Successor labels of a basic block: the unique labels targeted
    by its terminator, deduplicated. -/
def bbSuccs (bb : BasicBlock) : List String :=
  match bb.instructions.reverse with
  | [] => []
  | last :: _ => (getSuccessors last).dedup

/- ===== Helpers ===== -/

/-- Cons x onto xs if x is not already a member (list-backed set insert). -/
def setInsert {α : Type} [BEq α] (x : α) (xs : List α) : List α :=
  if xs.contains x then xs else x :: xs

/-- Look up a key in an AssocList, returning [] if absent. -/
def alistGetList (al : AssocList String (List String)) (k : String) : List String :=
  match AssocList.lookup String (List String) al k with
  | none => []
  | some v => v

/- ===== CFG Analysis Record ===== -/

structure CfgAnalysis where
  succs      : AssocList String (List String)  -- label → successor labels
  preds      : AssocList String (List String)  -- label → predecessor labels
  reachable  : AssocList String Bool            -- label → whether reachable from entry
  dfsPost    : List String                       -- DFS postorder
  dfsPre     : List String                       -- DFS preorder
  deriving Inhabited

/-- Successor labels of lbl in the CFG ([] if lbl is absent). -/
def cfgSuccsOf (cfg : CfgAnalysis) (lbl : String) : List String :=
  alistGetList cfg.succs lbl

/-- Predecessor labels of lbl in the CFG ([] if lbl is absent). -/
def cfgPredsOf (cfg : CfgAnalysis) (lbl : String) : List String :=
  alistGetList cfg.preds lbl

/-- Whether lbl was reached during DFS from the entry block. -/
def cfgReachableOf (cfg : CfgAnalysis) (lbl : String) : Bool :=
  match AssocList.lookup String Bool cfg.reachable lbl with
  | none => false
  | some b => b

/-- No critical edges: every block either has at most one predecessor,
    or all its predecessors have at most one successor. -/
def cfgIsNormalized (cfg : CfgAnalysis) (fn : IrFunction) : Prop :=
  ∀ bb, bb ∈ fn.blocks →
    (cfgPredsOf cfg bb.label).length ≤ 1 ∨
    (∀ pred, pred ∈ cfgPredsOf cfg bb.label →
      (cfgSuccsOf cfg pred).length ≤ 1)

/- ===== CFG Construction ===== -/

/-- Initialize succs/preds maps with all block labels mapped to []. -/
def initLabelMap (bbs : List BasicBlock) : AssocList String (List String) :=
  bbs.foldl (λ m bb => AssocList.insert String (List String) m bb.label []) []

/-- Build succs map: each block label → bb_succs(bb). -/
def buildSuccs (bbs : List BasicBlock) : AssocList String (List String) :=
  let init := initLabelMap bbs
  bbs.foldl (λ m bb =>
    AssocList.insert String (List String) m bb.label (bbSuccs bb))
    init

/-- Build preds map: for each block, add it as predecessor of its successors. -/
def buildPreds (bbs : List BasicBlock) (succs : AssocList String (List String))
    : AssocList String (List String) :=
  let init := initLabelMap bbs
  bbs.foldl (λ m bb =>
    let succLbls := alistGetList succs bb.label
    succLbls.foldl (λ m' succ =>
      let oldPreds := alistGetList m' succ
      AssocList.insert String (List String) m' succ (setInsert bb.label oldPreds))
      m)
    init

/- ===== DFS Traversal ===== -/

/-- DFS postorder walk from a label, with visited set.
    Returns (visited, postorder). -/
partial def dfsPostWalk (succs : AssocList String (List String))
    (visited : List String) (lbl : String) : List String × List String :=
  if visited.contains lbl then (visited, [])
  else
    let visited' := lbl :: visited
    let succsLbl := alistGetList succs lbl
    let (visited'', post) :=
      succsLbl.foldl (λ (vs, acc) s =>
        let (vs', sub) := dfsPostWalk succs vs s
        (vs', acc ++ sub))
      (visited', [])
    (visited'', post ++ [lbl])

/-- DFS preorder walk from a label, with visited set.
    Returns (visited, preorder). -/
partial def dfsPreWalk (succs : AssocList String (List String))
    (visited : List String) (lbl : String) : List String × List String :=
  if visited.contains lbl then (visited, [])
  else
    let visited' := lbl :: visited
    let succsLbl := alistGetList succs lbl
    let (visited'', pre) :=
      succsLbl.foldl (λ (vs, acc) s =>
        let (vs', sub) := dfsPreWalk succs vs s
        (vs', acc ++ sub))
      (visited', [])
    (visited'', [lbl] ++ pre)

/-- Compute reachable labels from the entry point. -/
def computeReachable (bbs : List BasicBlock) (entry : String) : AssocList String Bool :=
  let succs := buildSuccs bbs
  let (visited, _) := dfsPostWalk succs [] entry
  visited.foldl (λ m v => AssocList.insert String Bool m v true) []

/-- Top-level CFG analysis. -/
def cfgAnalyze (fn : IrFunction) : CfgAnalysis :=
  let succs := buildSuccs fn.blocks
  let preds := buildPreds fn.blocks succs
  match fnEntryLabel fn with
  | none =>
    { succs := succs, preds := preds, reachable := [],
      dfsPost := [], dfsPre := [] }
  | some entry =>
    let reachable := computeReachable fn.blocks entry
    let (_, post) := dfsPostWalk succs [] entry
    let (_, pre) := dfsPreWalk succs [] entry
    { succs := succs, preds := preds, reachable := reachable,
      dfsPost := post, dfsPre := pre }

end EvmYul.Venom.Codegen
