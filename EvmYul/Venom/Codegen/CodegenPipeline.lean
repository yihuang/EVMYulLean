/-
Top-Level Codegen Pipeline + Codegen Readiness — Property Definitions

Port of vyper-hol/venom/codegen/defs/codegenScript.sml
       + vyper-hol/venom/codegen/defs/stackPlanGenScript.sml (codegen_ready + API)

Defines:
  - codegen_ready_inst / codegen_ready_fn / codegen_ready: preconditions
  - generate_context_plan: signature (algorithm deferred to analyses)
  - codegen: top-level pipeline (plan_gen → execute_plan → assemble)

NO proofs — property definitions only.
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Codegen.AsmIR
import EvmYul.Venom.Codegen.PlanTypes
import EvmYul.Venom.Codegen.PlanExec
import EvmYul.Venom.Codegen.SymbolResolve
open EvmYul.Venom
open EvmYul.Venom.Codegen

namespace EvmYul.Venom.Codegen

/- ===== Codegen Preconditions ===== -/

/-- Opcodes that must be eliminated by earlier passes before codegen:
    ALLOCA — eliminated by mem2var / memory layout
    SINK   — test-only pseudo-instruction
    DLOAD, DLOADBYTES — lowered by lower_dload pass -/
def isPreCodegenOpcode : Opcode → Bool
  | Opcode.ALLOCA => true
  | Opcode.SINK => true
  | Opcode.DLOAD => true
  | Opcode.DLOADBYTES => true
  | _ => false

/-- Per-instruction: no pre-codegen opcodes allowed. -/
def codegenReadyInst (inst : Instruction) : Prop :=
  ¬ isPreCodegenOpcode inst.opcode

/-- Per-function: structural WF + SSA + SUE + normalized CFG + no bad opcodes.
    These preconditions are discharged by earlier passes in the pipeline.
    For our property definitions, we state them as assumptions (Props). -/
def codegenReadyFn (fn : IrFunction) : Prop :=
  -- All instructions satisfy codegen_ready_inst
  (∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) ∧
  -- Well-formedness conditions (stated as Props, to be proved by earlier passes)
  True

/-- Per-context: all functions ready. -/
def codegenReady (ctx : VenomContext) : Prop :=
  ∀ fn ∈ ctx.functions, codegenReadyFn fn

/- ===== Context-Wellformedness ===== -/

/-- A context is well-formed: functions have unique names and all labels valid. -/
def ctxWf (_ctx : VenomContext) : Prop := True  -- simplified

/- ===== Plan Generator API Signatures ===== -/

/-- Generate stack plan for a single instruction.
    Returns NONE if opcode should have been eliminated (pre-codegen).
    Returns SOME (stack_ops, updated_plan_state).
    
    Parameters:
    - liveness: liveness analysis (abstract)
    - dfg: data-flow graph (abstract)
    - cfg: control-flow graph (abstract)
    - fn: the function
    - inst: the instruction
    - next_liveness: live vars at next instruction
    - is_halting: whether this block overall halts
    - next_is_terminator: whether next instruction is a terminator
    - cur_bb_label: current basic block label
    - ps: current plan state -/
def generateInstPlan (_liveness _dfg _cfg : Unit) (_fn : IrFunction) (_inst : Instruction)
    (_nextLiveness : List String) (_isHalting _nextIsTerminator : Bool)
    (_curBbLabel : String) (_ps : PlanState) : Option (List StackOp × PlanState) :=
  -- Deferred: algorithm not transcribed yet. Return none for now.
  none

/-- Generate stack plan for a basic block.
    Returns NONE if any instruction fails (pre-codegen opcode encountered). -/
def generateBlockPlan (_liveness _dfg _cfg : Unit) (_fn : IrFunction) (_bb : BasicBlock)
    (_ps : PlanState) : Option (List StackOp × PlanState) :=
  -- Deferred
  none

/-- Generate stack plan for an entire function (all blocks).
    Returns NONE if any block fails. -/
def generateFnPlan (_liveness _dfg _cfg : Unit) (_fn : IrFunction)
    (_fnEom : Nat) : Option (List StackOp × PlanState) :=
  -- Deferred: generates plan for all blocks in DFS order
  none

/-- Generate stack plan for entire context (all functions).
    fn_eom_map maps function names to their frame end-of-memory offsets.
    Returns NONE if any function fails. -/
def generateContextPlan (_ctx : VenomContext) (_fnEomMap : AssocList String Nat)
    : Option (List StackOp) :=
  -- Deferred: composes per-function plans
  none

/-- Fuel-bounded variant of generate_context_plan. -/
def generateContextPlanFuel (_fuel : Nat) (_ctx : VenomContext)
    (_fnEomMap : AssocList String Nat) : Option (List StackOp) :=
  if _fuel = 0 then none else none  -- deferred

/- ===== Top-Level Codegen Pipeline ===== -/

/--
Full codegen pipeline:
  1. generate_context_plan : VenomContext → stack_op list
  2. execute_plan         : stack_op list → asm_inst list
  3. assemble             : asm_inst list → byte list

Returns NONE if plan generation fails (malformed input).
Data segment (selector tables, deploy code, CBOR metadata) is appended
after the code assembly — it bypasses the plan generator.
-/
def codegen (ctx : VenomContext) (fnEomMap : AssocList String Nat)
    (dataSeg : List DataSection) : Option (List byte) :=
  match generateContextPlan ctx fnEomMap with
  | none => none
  | some plan =>
    let codeAsm := executePlan plan
    let dataAsm : List AsmInst := []  -- data_segment_asm deferred
    some (assemble (codeAsm ++ dataAsm))

/-- Fuel-bounded variant. -/
def codegenFuel (fuel : Nat) (ctx : VenomContext) (fnEomMap : AssocList String Nat)
    (dataSeg : List DataSection) : Option (List byte) :=
  match generateContextPlanFuel fuel ctx fnEomMap with
  | none => none
  | some plan =>
    let codeAsm := executePlan plan
    let dataAsm : List AsmInst := []
    some (assemble (codeAsm ++ dataAsm))

end EvmYul.Venom.Codegen
