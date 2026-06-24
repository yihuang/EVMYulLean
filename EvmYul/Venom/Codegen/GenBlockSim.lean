/-
Block Simulation Lemma — THE key lemma for codegen_fn_correct

Port of vyper-hol/venom/codegen/proofs/genBlockSimScript.sml

The actual proofs are deferred — they require the plan simulation lemmas
(doSwap_sim, doRestore_sim, etc.) to be re-proven and wired through.
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Exec
import EvmYul.Venom.Codegen.PlanTypes
import EvmYul.Venom.Codegen.PlanExec
import EvmYul.Venom.Codegen.PlanOps
import EvmYul.Venom.Codegen.StackPlanGen
import EvmYul.Venom.Codegen.AsmSem
import EvmYul.Venom.Codegen.CodegenRel
import EvmYul.Venom.Codegen.CodegenPipeline
import EvmYul.Venom.Codegen.LivenessAnalysis
import EvmYul.Venom.Codegen.DfgAnalysis
import EvmYul.Venom.Codegen.CfgAnalysis
open EvmYul.Venom

namespace EvmYul.Venom.Codegen

theorem genBlockSimulation
  {fuel ctx fn bb ps ps' ops vs as labelOffsets}
  (liveness : LivenessState) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
  (hplan : generateBlockPlan liveness dfg cfg fn bb ps = some (ops, ps'))
  (hrel  : venomAsmRel labelOffsets ps vs as)
  (hsafe : ∀ inst vs1 vs2, stepInstBase inst vs1 = ExecResult.OK vs2 →
           stepMemSafe ps.alloc vs1 vs2)
  (hready : codegenReadyFn fn) :
  let prog := executePlan ops
  ∃ as', runAsm (prog.length) ([] : AssocList Nat Nat) prog as = AsmResult.AsmOK as' ∧
  match runBlock fuel ctx bb vs with
  | ExecResult.OK vs' =>
    venomAsmRel labelOffsets ps' vs' as'
  | ExecResult.Halt vs' =>
    ∃ as'', runAsm (prog.length) ([] : AssocList Nat Nat) prog as = AsmResult.AsmHalt as'' ∧
            venomAsmTerminalRel vs' as''
  | ExecResult.Abort AbortType.RevertAbort vs' =>
    ∃ as'', runAsm (prog.length) ([] : AssocList Nat Nat) prog as = AsmResult.AsmRevert as'' ∧
            venomAsmTerminalRel vs' as''
  | ExecResult.Abort AbortType.ExHaltAbort vs' =>
    ∃ as'', runAsm (prog.length) ([] : AssocList Nat Nat) prog as = AsmResult.AsmFault as'' ∧
            venomAsmTerminalRel vs' as''
  | _ => False := by
  sorry

theorem genFnSimulation
  {fuel ctx fn fnEom ops psFinal vs as labelOffsets}
  (liveness : LivenessState) (dfg : DfgAnalysis) (cfg : CfgAnalysis)
  (hplan : generateFnPlan fn fnEom 0 = some (ops, psFinal))
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
  sorry

end EvmYul.Venom.Codegen
