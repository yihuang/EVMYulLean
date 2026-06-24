/-
Stack Plan Generation — Per-Instruction/Block/Function/Context

Port of vyper-hol/venom/codegen/defs/stackPlanGenScript.sml

TOP-LEVEL:
  generateContextPlan — plan for entire venom_context
  generateFnPlan      — plan for a single function
  generateBlockPlan   — plan for a single basic block
-/

import EvmYul.Venom.Types
import EvmYul.UInt256
import EvmYul.Venom.Exec
import EvmYul.Venom.Codegen.AsmIR
import EvmYul.Venom.Codegen.StackModel
import EvmYul.Venom.Codegen.PlanTypes
import EvmYul.Venom.Codegen.PlanOps
import EvmYul.Venom.Codegen.CfgAnalysis
import EvmYul.Venom.Codegen.DfgAnalysis
import EvmYul.Venom.Codegen.LivenessAnalysis
open EvmYul.Venom

namespace EvmYul.Venom.Codegen

/-- Opcodes that should never appear at codegen time. -/
def isPreCodegenOpcode : Opcode → Bool
  | Opcode.ALLOCA | Opcode.SINK | Opcode.DLOAD | Opcode.DLOADBYTES => true
  | _ => false

/-- Opcodes that terminate execution (no control flow successor). -/
def isHaltingOpcode : Opcode → Bool
  | Opcode.RETURN | Opcode.REVERT | Opcode.STOP
  | Opcode.INVALID | Opcode.SELFDESTRUCT => true
  | _ => false

/-- Block ends with a halting instruction. -/
def bbIsHalting (bb : BasicBlock) : Bool :=
  match bb.instructions.reverse with
  | [] => false
  | last :: _ => isHaltingOpcode last.opcode

/-- Extract string from an operand (returns "" for non-Var). -/
def operandToString : Operand → String
  | Operand.Var s => s
  | _ => ""

/-- Count swap/spill/restore ops in a plan (for dry-run comparison). -/
def reorderCost (ops : List StackOp) : Nat :=
  ops.filter (λ op => match op with
    | StackOp.SOSwap _ | StackOp.SOSpill _ | StackOp.SORestore _ => true
    | _ => false) |>.length

/-- Generate a fresh label from a prefix. -/
def freshLabel (pref : String) (ps : PlanState) : String × PlanState :=
  let n := ps.labelCounter + 1
  (pref ++ "_" ++ toString n, { ps with labelCounter := n })

/-- Emit one input operand (restore if spilled, push/dup if needed). -/
def emitOneInput (opc : Opcode) (nextLiveness : List String) (op : Operand) (ps : PlanState)
    : List StackOp × PlanState :=
  let (restoreOps, ps1) :=
    if isVarOperand op then
      match alookup' ps.spilled op with
      | some _ => doRestore op ps
      | none => ([], ps)
    else ([], ps)
  match op with
  | Operand.Label l =>
    let ps2 := { ps1 with stack := stackPush op ps1.stack }
    if opc ≠ Opcode.INVOKE then
      (restoreOps ++ [StackOp.SOPushLabel l], ps2)
    else (restoreOps, ps2)
  | Operand.Lit v =>
    (restoreOps ++ [StackOp.SOPush (Operand.Lit v)],
     { ps1 with stack := stackPush op ps1.stack })
  | Operand.Var v =>
    if nextLiveness.contains v then
      match stackGetDepth op ps1.stack with
      | some dist =>
        let (dupOps, ps2) := doDup dist ps1
        (restoreOps ++ dupOps, ps2)
      | none => (restoreOps, ps1)
    else (restoreOps, ps1)

/-- Emit input plan for a list of operands. -/
def emitInputPlan (opc : Opcode) (ops : List Operand) (nextLiveness : List String) (ps : PlanState)
    : List StackOp × PlanState :=
  ops.foldl (λ (accOps, ps') op =>
    let (stepOps, ps'') := emitOneInput opc nextLiveness op ps'
    (accOps ++ stepOps, ps''))
    ([], ps)

/-- Simplified optimistic swap (skipped for now). -/
def optimisticSwapPlan (_dfg : DfgAnalysis) (_inst : Instruction) (_nextLiveness : List String)
    (_nextIsTerminator : Bool) (ps : PlanState) : List StackOp × PlanState :=
  ([], ps)

/-- Which operands go to the stack (excludes labels for control flow ops). -/
def computeOperands (inst : Instruction) : List Operand :=
  let opc := inst.opcode
  if (opc == Opcode.JMP) || (opc == Opcode.DJMP) || (opc == Opcode.JNZ) || (opc == Opcode.INVOKE) then
    getNonLabelOperands inst
  else if opc == Opcode.LOG then
    inst.operands.tail
  else
    inst.operands

/-- Generate EVM opcode emission for an instruction. -/
def generateEmitOps (inst : Instruction) (logTopicCount : Nat) (ps : PlanState)
    : List StackOp × PlanState :=
  let opc := inst.opcode
  match opcodeToEvmName opc with
  | some name => ([StackOp.SOEmit name], ps)
  | none =>
    if opc == Opcode.JNZ then
      let labels := inst.operands.filter isLabelOperand
      match labels with
      | [Operand.Label ifNz, Operand.Label ifZ] =>
        ([StackOp.SOPushLabel ifNz, StackOp.SOEmit "JUMPI",
          StackOp.SOPushLabel ifZ, StackOp.SOEmit "JUMP"], ps)
      | _ => ([], ps)
    else if opc == Opcode.JMP then
      match inst.operands with
      | [Operand.Label target] => ([StackOp.SOPushLabel target, StackOp.SOEmit "JUMP"], ps)
      | _ => ([], ps)
    else if opc == Opcode.DJMP then ([StackOp.SOEmit "JUMP"], ps)
    else if opc == Opcode.INVOKE then
      match inst.operands with
      | Operand.Label l :: _ =>
        let (retLbl, ps') := freshLabel "return_label" ps
        ([StackOp.SOPushLabel retLbl, StackOp.SOPushLabel l,
          StackOp.SOEmit "JUMP", StackOp.SOLabel retLbl], ps')
      | _ => ([], ps)
    else if opc == Opcode.RET then ([StackOp.SOEmit "JUMP"], ps)
    else if opc == Opcode.ASSERT then
      ([StackOp.SOEmit "ISZERO", StackOp.SOPushLabel "revert", StackOp.SOEmit "JUMPI"], ps)
    else if opc == Opcode.ASSERT_UNREACHABLE then
      let (endLbl, ps') := freshLabel "reachable" ps
      ([StackOp.SOPushLabel endLbl, StackOp.SOEmit "JUMPI",
        StackOp.SOEmit "INVALID", StackOp.SOLabel endLbl], ps')
    else if opc == Opcode.LOG then
      ([StackOp.SOEmit ("LOG" ++ toString logTopicCount)], ps)
    else if opc == Opcode.ISTORE then
      ([StackOp.SOEmit "SWAP1", StackOp.SOEmit "MSTORE"], ps)
    else ([], ps)

/-- Generate plan for a PHI instruction. -/
def generatePhiPlan (inst : Instruction) (nextLiveness : List String) (ps : PlanState)
    : List StackOp × PlanState :=
  let phiVars := inst.operands.filter isVarOperand
  match stackGetPhiDepth phiVars ps.stack with
  | none => ([], ps)
  | some dist =>
    let atDepth := stackPeek dist ps.stack
    let ret := Operand.Var (inst.outputs.get! 0)
    if nextLiveness.contains (operandToString atDepth) then
      let (dupOps, ps') := doDup dist ps
      let ps'' := { ps' with stack := stackPoke 0 ret ps'.stack }
      (dupOps ++ [StackOp.SOPoke 0 ret], ps'')
    else
      let ps' := { ps with stack := stackPoke dist ret ps.stack }
      ([StackOp.SOPoke dist ret], ps')

/-- Generate plan for an OFFSET instruction. -/
def generateOffsetPlan (inst : Instruction) (ps : PlanState) : List StackOp × PlanState :=
  let ofstVal := inst.operands.get! 0
  let labelOp := inst.operands.get! 1
  let n := match ofstVal with
    | Operand.Lit v => v.toNat
    | _ => 0
  let ret := Operand.Var (inst.outputs.get! 0)
  match labelOp with
  | Operand.Label l =>
    ([StackOp.SOPushOfst l n],
     { ps with stack := stackPush ret ps.stack })
  | _ => ([], ps)

/-- Generate plan for a regular (non-phi, non-offset) instruction. -/
def generateRegularInstPlan (liveness : LivenessState) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
    (fn : IrFunction) (inst : Instruction) (nextLiveness : List String) (isHalting : Bool)
    (nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    : List StackOp × PlanState :=
  let opc := inst.opcode
  let operands := computeOperands inst
  let logTopicCount :=
    match opc with
    | Opcode.LOG =>
      match inst.operands with
      | Operand.Lit v :: _ => v.toNat
      | _ => 0
    | _ => 0
  let (inputOps, ps1) := emitInputPlan opc operands nextLiveness ps
  let (joinOps, ps2) :=
    if opc == Opcode.JMP then
      match inst.operands with
      | [Operand.Label target] =>
        let targetLiveness := liveVarsAt liveness target 0
        match lookupBlock target fn.blocks with
        | none => ([], ps1)
        | some targetBb =>
          let targetStack := inputVarsFrom curBbLabel targetBb.instructions targetLiveness
          reorderPlan (targetStack.map Operand.Var) ps1
      | _ => ([], ps1)
    else ([], ps1)
  let (operands', ps3) :=
    if isCommutative opc && operands.length ≥ 2 then
      let (opsA, _) := reorderPlan operands ps2
      let costA := reorderCost opsA
      let n := operands.length
      let swapped := operands.take (n - 2) ++
        [operands.get! (n - 1), operands.get! (n - 2)]
      let (opsB, _) := reorderPlan swapped ps2
      let costB := reorderCost opsB
      if costA < costB then (operands, ps2) else (swapped, ps2)
    else (operands, ps2)
  let (reorderOps, ps4) := reorderPlan operands' ps3
  let ps5 := { ps4 with stack := stackPop operands'.length ps4.stack }
  let ps6 := inst.outputs.foldl (λ ps' out =>
    { ps' with stack := stackPush (Operand.Var out) ps'.stack }) ps5
  let (emitOps, ps7) := generateEmitOps inst logTopicCount ps6
  if inst.outputs.isEmpty then
    let ps8 := releaseDeadSpills nextLiveness ps7
    (inputOps ++ joinOps ++ reorderOps ++ emitOps, ps8)
  else
    let (popOps, ps8) :=
      if !isHalting then
        let dead := inst.outputs.filter (λ out => !nextLiveness.contains out)
        popmanyPlan (dead.map Operand.Var) ps7
      else ([], ps7)
    let liveOuts := inst.outputs.filter (λ out => nextLiveness.contains out)
    let (optOps, ps9) :=
      if liveOuts.isEmpty then ([], ps8)
      else ([], ps8)  -- simplified: skip optimistic swap
    let ps10 := releaseDeadSpills nextLiveness ps9
    (inputOps ++ joinOps ++ reorderOps ++ emitOps ++ popOps ++ optOps, ps10)

/-- Generate plan for a single instruction.
    Returns NONE if a pre-codegen opcode is encountered. -/
def generateInstPlan (liveness : LivenessState) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
    (fn : IrFunction) (inst : Instruction) (nextLiveness : List String) (isHalting : Bool)
    (nextIsTerminator : Bool) (curBbLabel : String) (ps : PlanState)
    : Option (List StackOp × PlanState) :=
  if isPreCodegenOpcode inst.opcode then none
  else if inst.opcode == Opcode.PHI then
    some (generatePhiPlan inst nextLiveness ps)
  else if inst.opcode == Opcode.OFFSET then
    some (generateOffsetPlan inst ps)
  else if inst.opcode == Opcode.PARAM then
    some ([], ps)
  else if inst.opcode == Opcode.NOP then
    some ([], ps)
  else
    some (generateRegularInstPlan liveness dfg cfg fn inst nextLiveness isHalting
           nextIsTerminator curBbLabel ps)

/-- Get PARAM instructions from the start of a block. -/
def getParams (insts : List Instruction) : List Instruction :=
  insts.takeWhile (λ inst => inst.opcode == Opcode.PARAM)

/-- Generate plan for function parameters. -/
def prepareParamsPlan (liveness : LivenessState) (fn : IrFunction) (ps : PlanState)
    : List StackOp × PlanState :=
  let entry := fn.blocks.get! 0
  let params := getParams entry.instructions
  if params.isEmpty then ([], ps)
  else
    let ps' := params.foldl (λ ps'' inst =>
      { ps'' with stack := stackPush (Operand.Var (inst.outputs.get! 0)) ps''.stack }) ps
    let nextLive := liveVarsAt liveness entry.label params.length
    let toPop := ps'.stack.filter (λ op =>
      match op with
      | Operand.Var v => !nextLive.contains v
      | _ => true)
    let toPopVars := toPop.filter isVarOperand
    let (popOps, ps'') := popmanyPlan toPopVars ps'
    (popOps, ps'')

/-- Clean stack from predecessor: pop variables not live on entry. -/
def cleanStackPlan (liveness : LivenessState) (cfg : CfgAnalysis) (fn : IrFunction)
    (bb : BasicBlock) (ps : PlanState) : List StackOp × PlanState :=
  let preds := cfgPredsOf cfg bb.label
  match preds with
  | [predLbl] =>
    if (cfgSuccsOf cfg predLbl).length ≤ 1 then
      ([], ps)
    else
      match lookupBlock predLbl fn.blocks with
      | none => ([], ps)
      | some predBb =>
        let inputs := inputVarsFrom predLbl bb.instructions
          (liveVarsAt liveness bb.label 0)
        let layout := liveVarsAt liveness predLbl predBb.instructions.length
        let toPop := layout.filter (λ v => !inputs.contains v)
        popmanyPlan (toPop.map Operand.Var) ps
  | _ => ([], ps)

/-- Filter out PARAM instructions from a block. -/
def nonParamInsts (bb : BasicBlock) : List Instruction :=
  bb.instructions.filter (λ inst => inst.opcode ≠ Opcode.PARAM)

/-- Generate plan for a single basic block. -/
def generateBlockPlan (liveness : LivenessState) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
    (fn : IrFunction) (bb : BasicBlock) (ps : PlanState) : Option (List StackOp × PlanState) :=
  let labelOp := [StackOp.SOLabel bb.label]
  let entryLbl := fn.blocks.get! 0 |>.label
  let (paramOps, ps1) :=
    if bb.label == entryLbl then prepareParamsPlan liveness fn ps
    else ([], ps)
  let (cleanOps, ps2) :=
    if (cfgPredsOf cfg bb.label).length = 1 then
      cleanStackPlan liveness cfg fn bb ps1
    else ([], ps1)
  let insts := nonParamInsts bb
  let isHalting := bbIsHalting bb
  let nParams := (getParams bb.instructions).length
  let init : Option (List StackOp × PlanState) := some ([], ps2)
  let result := insts.enum.foldl (λ acc (i, inst) =>
    match acc with
    | none => none
    | some (ops, psState) =>
      let nextLive :=
        if i + 1 < insts.length then
          liveVarsAt liveness bb.label (i + nParams + 1)
        else
          liveVarsAt liveness bb.label bb.instructions.length
      let nextIsTerm :=
        if i + 1 < insts.length then
          isTerminator (insts.get! (i + 1)).opcode
        else false
      match generateInstPlan liveness dfg cfg fn inst nextLive isHalting nextIsTerm bb.label psState with
      | none => none
      | some (stepOps, ps') => some (ops ++ stepOps, ps'))
    init
  match result with
  | none => none
  | some (instOps, ps3) =>
    some (labelOp ++ paramOps ++ cleanOps ++ instOps, ps3)

/-- Generate plan for a function via DFS traversal.
    Bounded by fuel for termination.
    `succsPlanHelper` is a helper for processing successor blocks. -/
partial def generateFnPlanAux (fuel : Nat) (liveness : LivenessState) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
    (fn : IrFunction) (worklist : List String) (visited : List String) (ps : PlanState)
    : Option (List StackOp × List String × PlanState) :=

  let rec succsPlanHelper (liveness : LivenessState) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
      (fn : IrFunction) (savedStack : List Operand) (savedSpilled : SpilledMap)
      (succs : List String) (visited : List String) (ps_g : PlanState)
      : Option (List StackOp × List String × PlanState) :=
    if fuel = 0 then none else
    match succs with
    | [] => some ([], visited, ps_g)
    | succ :: rest =>
      let psBranch : PlanState := { stack := savedStack, spilled := savedSpilled, alloc := ps_g.alloc, labelCounter := ps_g.labelCounter }
      match generateFnPlanAux (fuel - 1) liveness dfg cfg fn [succ] visited psBranch with
      | none => none
      | some (sOps, visitedAfter, psAfter) =>
        let ps_g' : PlanState := { stack := ps_g.stack, spilled := ps_g.spilled, alloc := psAfter.alloc, labelCounter := psAfter.labelCounter }
        match succsPlanHelper liveness dfg cfg fn savedStack savedSpilled rest visitedAfter ps_g' with
        | none => none
        | some (restOps, visitedFinal, psFinal) =>
          some (sOps ++ restOps, visitedFinal, psFinal)

  if fuel = 0 then none else
  match worklist with
  | [] => some ([], visited, ps)
  | lbl :: rest =>
    if visited.contains lbl then
      generateFnPlanAux fuel liveness dfg cfg fn rest visited ps
    else
      let visited' := lbl :: visited
      match lookupBlock lbl fn.blocks with
      | none => generateFnPlanAux fuel liveness dfg cfg fn rest visited' ps
      | some bb =>
        match generateBlockPlan liveness dfg cfg fn bb ps with
        | none => none
        | some (blockOps, ps') =>
          let succs := cfgSuccsOf cfg lbl
          match succsPlanHelper liveness dfg cfg fn ps'.stack ps'.spilled succs visited' ps' with
          | none => none
          | some (succOps, visited'', ps'') =>
            match generateFnPlanAux fuel liveness dfg cfg fn rest visited'' ps'' with
            | none => none
            | some (restOps, visitedFinal, psFinal) =>
              some (blockOps ++ succOps ++ restOps, visitedFinal, psFinal)


/-- Generate plan for a function. -/
def generateFnPlan (fn : IrFunction) (fnEom : Nat) (lblCtr : Nat) : Option (List StackOp × PlanState) :=
  let liveness := livenessAnalyze fn
  let dfg := dfgBuildFunction fn
  let cfg := cfgAnalyze fn
  let ps := { initPlanState fnEom with labelCounter := lblCtr }
  match fnEntryLabel fn with
  | none => some ([], ps)
  | some lbl =>
    match generateFnPlanAux 10000 liveness dfg cfg fn [lbl] [] ps with
    | none => none
    | some (ops, _, ps') => some (ops, ps')

/-- Revert postamble (standard EVM revert handler). -/
def revertPostamble : List StackOp :=
  [StackOp.SOLabel "revert", StackOp.SOPush (Operand.Lit (UInt256.ofNat 0)),
   StackOp.SOEmit "DUP1", StackOp.SOEmit "REVERT"]

/-- Generate plan for the entire context (all functions).
    Returns the stack ops list on success, NONE on failure. -/
def generateContextPlan (ctx : VenomContext) (fnEomMap : AssocList String Nat)
    : Option (List StackOp) :=
  let init : Option (List StackOp × Nat) := some ([], 0)
  let result := ctx.functions.foldl (λ acc fn =>
    match acc with
    | none => none
    | some (ops, lblCtr) =>
      let eom := match AssocList.lookup String Nat fnEomMap fn.name with
        | some v => v
        | none => 0
      match generateFnPlan fn eom lblCtr with
      | none => none
      | some (fnOps, ps) =>
        some (ops ++ fnOps, ps.labelCounter))
    init
  match result with
  | none => none
  | some (allOps, _) => some (allOps ++ revertPostamble)

end EvmYul.Venom.Codegen
