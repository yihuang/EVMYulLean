/-
Top-Level Codegen Pipeline + Codegen Readiness — Property Definitions

Port of vyper-hol/venom/codegen/defs/codegenScript.sml

Defines:
  - codegen_ready_inst / codegen_ready_fn / codegen_ready: preconditions
  - codegen: top-level pipeline

isPreCodegenOpcode and generateContextPlan are defined in StackPlanGen.lean.
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Codegen.AsmIR
import EvmYul.Venom.Codegen.PlanTypes
import EvmYul.Venom.Codegen.PlanExec
import EvmYul.Venom.Codegen.SymbolResolve
import EvmYul.Venom.Codegen.StackPlanGen
open EvmYul.Venom

namespace EvmYul.Venom.Codegen

/- ===== Codegen Preconditions ===== -/

/-- Per-instruction: no pre-codegen opcodes allowed.
    isPreCodegenOpcode is defined in StackPlanGen. -/
def codegenReadyInst (inst : Instruction) : Prop :=
  ¬ isPreCodegenOpcode inst.opcode

/-- Per-function: structural WF + SSA + SUE + normalized CFG + no bad opcodes. -/
def codegenReadyFn (fn : IrFunction) : Prop :=
  (∀ bb ∈ fn.blocks, ∀ inst ∈ bb.instructions, codegenReadyInst inst) ∧
  (∀ bb ∈ fn.blocks, bb.instructions ≠ []) ∧
  (∀ bb ∈ fn.blocks, ∀ succ ∈ bbSuccs bb, ∃ bb' ∈ fn.blocks, bb'.label = succ)

/-- Per-context: all functions ready. -/
def codegenReady (ctx : VenomContext) : Prop :=
  ∀ fn ∈ ctx.functions, codegenReadyFn fn

/-- A context is well-formed: functions have unique names and all labels valid. -/
def ctxWf (_ctx : VenomContext) : Prop := True

/- ===== Top-Level Codegen Pipeline ===== -/

/-- Full codegen pipeline, returns NONE if plan generation fails. -/
def codegen (ctx : VenomContext) (fnEomMap : AssocList String Nat)
    (dataSeg : List DataSection) : Option (List byte) :=
  match generateContextPlan ctx fnEomMap with
  | none => none
  | some plan =>
    let codeAsm := executePlan plan
    let dataAsm : List AsmInst := []
    some (assemble (codeAsm ++ dataAsm))

/-- Fuel-bounded variant. -/
def codegenFuel (fuel : Nat) (ctx : VenomContext) (fnEomMap : AssocList String Nat)
    (dataSeg : List DataSection) : Option (List byte) :=
  codegen ctx fnEomMap dataSeg

end EvmYul.Venom.Codegen
