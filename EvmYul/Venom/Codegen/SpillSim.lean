/-
Spill/Restore Simulation — Layer 2
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Codegen.AsmSem
import EvmYul.Venom.Codegen.PlanExec
import EvmYul.Venom.Codegen.CodegenRel
import EvmYul.Venom.Codegen.AsmOpSim
import EvmYul.Venom.Codegen.StackRelSim
open EvmYul.Venom

namespace EvmYul.Venom.Codegen

lemma asmMload_read_correct {s : AsmState} {offset : bytes32} {stk : List bytes32}
    (hstack : s.stack = offset :: stk) :
    ∃ s', asmMload s = AsmResult.AsmOK s' ∧
          s'.stack = wordOfBytes ((asmExpandMemory (offset.toNat + 32) s.memory).readWithPadding offset.toNat 32) :: stk := by
  unfold asmMload; rw [hstack]; simp

theorem spill_asm_steps {offsetToPc prog as off}
    (hoff : off < 2 ^ 256)
    (hstk : as.stack ≠ [])
    (hblock : asmBlockAt prog as.pc
      [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MSTORE"]) :
    ∃ as', runAsm 2 offsetToPc prog as = AsmResult.AsmOK as' ∧
           as'.pc = as.pc + 2 ∧
           as'.stack = as.stack.tail := by
  sorry

theorem restore_asm_steps {offsetToPc prog as off}
    (hoff : off < 2 ^ 256)
    (hblock : asmBlockAt prog as.pc
      [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MLOAD"]) :
    ∃ as', runAsm 2 offsetToPc prog as = AsmResult.AsmOK as' ∧
           as'.pc = as.pc + 2 ∧
           as'.stack = wordOfBytes (as.memory.readWithPadding off 32) :: as.stack := by
  sorry

theorem asmRestoreStep {prog : List AsmInst} {as : AsmState} {off : Nat}
    {ps ps' : PlanState} {ops : List StackOp} {op : Operand} {labelOffsets vs}
    (hrestore : doRestore op ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length ([] : AssocList Nat Nat) prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' := by
  sorry

theorem asmSpillStep {prog : List AsmInst} {as : AsmState} {off : Nat}
    {ps ps' : PlanState} {ops : List StackOp} {labelOffsets vs}
    (hspill : doSpillTos ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length ([] : AssocList Nat Nat) prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' := by
  sorry

end EvmYul.Venom.Codegen
