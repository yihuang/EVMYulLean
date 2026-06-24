/-
Liveness Analysis — Backward Dataflow for Venom IR

Port of vyper-hol/venom/analysis/liveness/defs/livenessDefsScript.sml

Key functions:
  - liveness_analyze      — run full liveness analysis on a function
  - live_vars_at          — query live variables before instruction idx
  - input_vars_from       — live vars entering target from source (PHI-aware)
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Exec
import EvmYul.Venom.Codegen.CfgAnalysis
open EvmYul.Venom

namespace EvmYul.Venom.Codegen

/- ===== Instruction Helpers ===== -/

/-- Variables used (read) by an instruction. -/
def instUses (inst : Instruction) : List String :=
  inst.operands.filterMap (λ op =>
    match op with
    | Operand.Var v => some v
    | _ => none)

/-- Variables defined (written) by an instruction. -/
def instDefs (inst : Instruction) : List String :=
  inst.outputs

/- ===== Set Helpers (list-backed) ===== -/

/-- List union: xs ∪ ys (no dups if xs has no dups). -/
def listUnion (xs ys : List String) : List String :=
  xs ++ ys.filter (λ v => !xs.contains v)

/-- Transfer function: (live \ defs) ∪ uses -/
def liveUpdate (defs uses live : List String) : List String :=
  let live' := live.filter (λ v => !defs.contains v)
  live' ++ uses.filter (λ v => !live'.contains v)

/- ===== PHI Handling ===== -/

/-- Collect PHI instructions from the start of a block. -/
def collectPhis (insts : List Instruction) : List Instruction :=
  insts.takeWhile (λ inst => inst.opcode = Opcode.PHI)

/-- Extract (label, var) pairs from PHI operands. -/
def phiPairs (ops : List Operand) : List (String × String) :=
  let rec go : List Operand → List (String × String) := λ ops =>
    match ops with
    | [] => []
    | Operand.Label l :: Operand.Var v :: rest => (l, v) :: go rest
    | _ :: rest => go rest
  go ops

/-- Build phi maps for a list of PHI instructions. -/
def buildPhiMaps (srcLabel : String) (phis : List Instruction)
    : AssocList String Nat × AssocList Nat String :=
  let indexed := List.enum phis
  indexed.foldl (λ (opMap, matching) (i_phi : Nat × Instruction) =>
    let i := i_phi.1
    let phi := i_phi.2
    let pairs := phiPairs phi.operands
    let outVars := phi.outputs
    let opMap' := outVars.foldl (λ m v =>
      AssocList.insert String Nat m v i) opMap
    let srcVar := pairs.find? (λ (l, _) => l = srcLabel)
    let matching' := match srcVar with
      | some (_, v) => AssocList.insert Nat String matching i v
      | none => matching
    (opMap', matching'))
    (([], []) : AssocList String Nat × AssocList Nat String)

/-- Input vars from source label: PHI-aware positional substitution.
    Matches HOL4 `input_vars_from`. -/
def inputVarsFrom (srcLabel : String) (targetInsts : List Instruction)
    (baseLiveness : List String) : List String :=
  let phis := collectPhis targetInsts
  if phis.isEmpty then baseLiveness
  else
    let (opMap, matching) := buildPhiMaps srcLabel phis
    let init : List String × List Nat := ([], [])
    let (result, _) := baseLiveness.foldl (λ ((acc, placed) : List String × List Nat) v =>
      match AssocList.lookup String Nat opMap v with
      | some phiIdx =>
        if placed.contains phiIdx then (acc, placed)
        else
          match AssocList.lookup Nat String matching phiIdx with
          | some srcV => (acc ++ [srcV], phiIdx :: placed)
          | none => (acc, placed)
      | none => (acc ++ [v], placed))
      init
    result

/- ===== Liveness Analysis State ===== -/

/-- Liveness state: maps (block_label, inst_idx) → live variables before inst.
    Also stores boundary (live-out / live-in at block edges). -/
structure LivenessState where
  instMap  : AssocList (String × Nat) (List String)  -- (lbl, idx) → live vars
  boundary : AssocList String (List String)             -- lbl → live at boundary
  deriving Inhabited

/-- Query live variables before instruction idx in block lbl.
    idx = number of instructions gives the exit liveness (live-out). -/
def liveVarsAt (st : LivenessState) (lbl : String) (idx : Nat) : List String :=
  match AssocList.lookup (String × Nat) (List String) st.instMap (lbl, idx) with
  | none => []
  | some vs => vs

/-- Get boundary live set for a block (live-out for backward analysis). -/
def boundaryLive (st : LivenessState) (lbl : String) : List String :=
  match AssocList.lookup String (List String) st.boundary lbl with
  | none => []
  | some vs => vs

/- ===== Fold Transfer Across Block Instructions ===== -/

/-- Fold liveness backward through a block's instructions.
    Starts from `live` (the live-out of the block),
    applies live_update for each instruction in reverse,
    storing each intermediate live set at the instruction's index.
    Returns (live_at_entry, updated_inst_map). -/
def foldLivenessBlock (insts : List Instruction) (lbl : String)
    (live : List String) (startIdx : Nat)
    (instMap : AssocList (String × Nat) (List String))
    : List String × AssocList (String × Nat) (List String) :=
  let n := insts.length
  let rec go (idx : Nat) (liveAcc : List String) (accMap : AssocList (String × Nat) (List String)) :=
    if idx = 0 then
      (liveAcc, AssocList.insert (String × Nat) (List String) accMap (lbl, 0) liveAcc)
    else
      let i := idx - 1
      let inst := insts.get! i
      let liveBefore := liveUpdate (instDefs inst) (instUses inst) liveAcc
      let accMap' := AssocList.insert (String × Nat) (List String) accMap (lbl, i) liveBefore
      go i liveBefore accMap'
  go n live instMap

/- ===== Worklist Iteration ===== -/

/-- Single process iteration: for a given block, recompute its liveness
    by joining successors' entry values, folding through the block,
    and checking if the boundary changed. -/
def processBlock (cfg : CfgAnalysis) (bbs : List BasicBlock)
    (st : LivenessState) (lbl : String) : LivenessState :=
  let succsLbls := cfgSuccsOf cfg lbl
  let succEntries := succsLbls.map (λ s =>
    inputVarsFrom lbl
      (match lookupBlock s bbs with
       | some bb => bb.instructions
       | none => [])
      (boundaryLive st s))
  let joined := succEntries.foldl (λ acc vs => listUnion acc vs) []
  let insts := match lookupBlock lbl bbs with
    | some bb => bb.instructions
    | none => []
  let (entryLive, instMap) := foldLivenessBlock insts lbl joined 0 st.instMap
  let oldBoundary := boundaryLive st lbl
  let newBoundary := listUnion oldBoundary entryLive
  if newBoundary = oldBoundary then st
  else { st with boundary := AssocList.insert String (List String) st.boundary lbl newBoundary }

/-- Initialize liveness state: all boundaries set to []. -/
def initLivenessState (lbls : List String) : LivenessState :=
  { instMap := [], boundary := lbls.foldl (λ m l => AssocList.insert String (List String) m l []) [] }

/- ===== Top-level Liveness Analysis ===== -/

/-- Fuel-bounded liveness analysis (for termination guarantee). -/
def livenessAnalyzeFuel (fuel : Nat) (fn : IrFunction) : LivenessState :=
  let cfg := cfgAnalyze fn
  let lbls := fn.blocks.map (λ bb => bb.label)
  let st0 := initLivenessState lbls
  let worklist0 := cfg.dfsPost
  let rec iterate (fuel : Nat) (wl : List String) (st : LivenessState) : LivenessState :=
    match fuel, wl with
    | 0, _ => st
    | n+1, [] => st
    | n+1, lbl :: rest =>
      let st' := processBlock cfg fn.blocks st lbl
      if boundaryLive st' lbl ≠ boundaryLive st lbl then
        let preds := cfgPredsOf cfg lbl
        iterate n (rest ++ preds) st'
      else
        iterate n rest st'
  iterate fuel worklist0 st0

/-- Backward liveness analysis using worklist iteration.
    Uses the CFG's DFS postorder as the initial worklist (backward direction).
    Bounded to 1000 iterations for termination. -/
def livenessAnalyze (fn : IrFunction) : LivenessState :=
  livenessAnalyzeFuel 1000 fn

end EvmYul.Venom.Codegen
