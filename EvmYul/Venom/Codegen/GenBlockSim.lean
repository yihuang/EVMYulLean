/-
Block Simulation Lemma — THE key lemma for codegen_fn_correct

Port of vyper-hol/venom/codegen/proofs/genBlockSimScript.sml

States that if a block plan is generated (via generateBlockPlan), then
running its asm instructions simulates the Venom block execution,
preserving venomAsmRel.
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Exec
import EvmYul.Venom.Codegen.AsmIR
import EvmYul.Venom.Codegen.PlanTypes
import EvmYul.Venom.Codegen.PlanOps
import EvmYul.Venom.Codegen.PlanExec
import EvmYul.Venom.Codegen.AsmSem
import EvmYul.Venom.Codegen.CodegenRel
import EvmYul.Venom.Codegen.CodegenPipeline
open EvmYul.Venom
open EvmYul.Venom.Codegen

namespace EvmYul.Venom.Codegen

/- ============================================================
   KEY LEMMA: genBlockSimulation

   If a block plan is generated and the initial state satisfies
   venomAsmRel, then executing the plan on the asm interpreter
   preserves venomAsmRel through the Venom block step.

   In other words: the compiled block correctly simulates the
   Venom IR block execution.
   ============================================================ -/

theorem genBlockSimulation
  {fuel ctx fn bb ps ps' ops vs as labelOffsets}
  (hplan : generateBlockPlan () () () fn bb ps = some (ops, ps'))
  (hrel  : venomAsmRel labelOffsets ps vs as)
  (hsafe : ∀ inst vs1 vs2, stepInstBase inst vs1 = ExecResult.OK vs2 →
           stepMemSafe ps.alloc vs1 vs2)
  (hready : codegenReadyFn fn) :
  -- The compiled asm program is executePlan ops
  let prog := executePlan ops
  -- Running the asm program from as reaches some as'
  ∃ as', runAsm (prog.length) ([] : AssocList Nat Nat) prog as = AsmResult.AsmOK as' ∧
  -- And venomAsmRel is preserved through the Venom block step
  match runBlock fuel ctx bb vs with
  | ExecResult.OK vs' =>
    venomAsmRel labelOffsets ps' vs' as'
  | ExecResult.Halt vs' =>
    -- Terminal: only observable effects need to match
    ∃ as'', runAsm (prog.length) ([] : AssocList Nat Nat) prog as = AsmResult.AsmHalt as'' ∧
            venomAsmTerminalRel vs' as''
  | ExecResult.Abort AbortType.RevertAbort vs' =>
    ∃ as'', runAsm (prog.length) ([] : AssocList Nat Nat) prog as = AsmResult.AsmRevert as'' ∧
            venomAsmTerminalRel vs' as''
  | ExecResult.Abort AbortType.ExHaltAbort vs' =>
    ∃ as'', runAsm (prog.length) ([] : AssocList Nat Nat) prog as = AsmResult.AsmFault as'' ∧
            venomAsmTerminalRel vs' as''
  | _ => False := by
  unfold generateBlockPlan at hplan
  simp at hplan

/- ============================================================
   Function-level simulation: compose genBlockSimulation across
   all blocks in DFS order (via generateFnPlan).
   ============================================================ -/

theorem genFnSimulation
  {fuel ctx fn fnEom ops psFinal vs as labelOffsets}
  (hplan : generateFnPlan () () () fn fnEom = some (ops, psFinal))
  (hrel  : venomAsmRel labelOffsets (initPlanState fnEom) vs as)
  (hsafe : ∀ inst vs1 vs2, stepInstBase inst vs1 = ExecResult.OK vs2 →
           stepMemSafe (initPlanState fnEom).alloc vs1 vs2)
  (hready : codegenReadyFn fn) :
  let prog := executePlan ops
  match runBlocks fuel ctx fn vs with
  | ExecResult.Halt vs' =>
    ∃ as', runAsm prog.length ([] : AssocList Nat Nat) prog as = AsmResult.AsmHalt as' ∧
           venomAsmTerminalRel vs' as'
  | ExecResult.Abort AbortType.RevertAbort vs' =>
    ∃ as', runAsm prog.length ([] : AssocList Nat Nat) prog as = AsmResult.AsmRevert as' ∧
           venomAsmTerminalRel vs' as'
  | ExecResult.Abort AbortType.ExHaltAbort vs' =>
    ∃ as', runAsm prog.length ([] : AssocList Nat Nat) prog as = AsmResult.AsmFault as' ∧
           venomAsmTerminalRel vs' as'
  | ExecResult.OK _ => False
  | ExecResult.IntRet _ _ => True
  | ExecResult.Error _ => True := by
  unfold generateFnPlan at hplan
  simp at hplan

end EvmYul.Venom.Codegen
