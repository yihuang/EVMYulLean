/-
Spill/Restore Simulation — SOSpill and SORestore preserve venom_asm_rel

SOSpill off: 2 asm steps (PUSH off + MSTORE) — write TOS value to memory at off
SORestore off: 2 asm steps (PUSH off + MLOAD) — read memory at off to TOS

Proofs deferred — they require:
  - wordOfBytes / wordToBytes roundtrip lemmas
  - encodeNumBytes / wordOfBytes roundtrip
  - memory readWithPadding / write properties
  - planSpillRel and memoryRel invariant maintenance
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Codegen.AsmSem
import EvmYul.Venom.Codegen.PlanExec
import EvmYul.Venom.Codegen.CodegenRel
import EvmYul.Venom.Codegen.AsmOpSim
open EvmYul.Venom

namespace EvmYul.Venom.Codegen

/-- SOSpill off executes as 2 asm steps: push offset, then MSTORE. -/
theorem spill_asm_steps {offsetToPc prog as off}
    (hoff : off < 2 ^ 256)
    (hstk : as.stack ≠ [])
    (hblock : asmBlockAt prog as.pc
      [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MSTORE"]) :
    ∃ as', runAsm 2 offsetToPc prog as = AsmResult.AsmOK as' ∧
           as'.pc = as.pc + 2 ∧
           as'.stack = as.stack.tail := by
  sorry

/-- SORestore off executes as 2 asm steps: push offset, then MLOAD. -/
theorem restore_asm_steps {offsetToPc prog as off}
    (hoff : off < 2 ^ 256)
    (hblock : asmBlockAt prog as.pc
      [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MLOAD"]) :
    ∃ as', runAsm 2 offsetToPc prog as = AsmResult.AsmOK as' ∧
           as'.pc = as.pc + 2 ∧
           as'.stack = wordOfBytes (as.memory.readWithPadding off 32) :: as.stack := by
  sorry

/-- Single SOSpill step preserves venomAsmRel. -/
theorem asmSpillStep {prog : List AsmInst} {as : AsmState} {off : Nat}
    {ps ps' : PlanState} {ops : List StackOp} {labelOffsets vs}
    (hspill : doSpillTos ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length ([] : AssocList Nat Nat) prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' := by
  sorry

/-- Single SORestore step preserves venomAsmRel. -/
theorem asmRestoreStep {prog : List AsmInst} {as : AsmState} {off : Nat}
    {ps ps' : PlanState} {ops : List StackOp} {op : Operand} {labelOffsets vs}
    (hrestore : doRestore op ps = (ops, ps'))
    (hrel : venomAsmRel labelOffsets ps vs as)
    (hblock : asmBlockAt prog as.pc (executePlan ops)) :
    ∃ as', runAsm (executePlan ops).length ([] : AssocList Nat Nat) prog as = AsmResult.AsmOK as' ∧
           venomAsmRel labelOffsets ps' vs as' := by
  sorry

end EvmYul.Venom.Codegen
