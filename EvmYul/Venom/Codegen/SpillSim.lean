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

/- ===== Layer 2a: Asm-level lemmas ===== -/

/-- `asmMstore` with a 2+ element stack: stack → rest, PC → pc+1. -/
lemma asmMstore_pop2 {s : AsmState} {offset value : bytes32} {rest : List bytes32}
    (hstack : s.stack = offset :: value :: rest) :
    ∃ s', asmMstore s = AsmResult.AsmOK s' ∧ s'.stack = rest ∧ s'.pc = s.pc + 1 := by
  unfold asmMstore
  rw [hstack]
  dsimp
  let mem' : ByteArray := (wordToBytes value).write 0 (asmExpandMemory (offset.toNat + 32) s.memory) offset.toNat 32
  let witness : AsmState := { asmNext s with stack := rest, memory := mem' }
  refine ⟨witness, ?_, ?_, ?_⟩
  · rfl
  · dsimp [witness]
  · dsimp [witness]; rfl
/-- PUSH+MSTORE: spill a value to memory at offset `off`.
    After 2 steps: PC += 2, stack = original stack tail. -/
theorem spill_asm_steps {offsetToPc prog as off}
    (hoff : off < 2 ^ 256)
    (hstk : as.stack ≠ [])
    (hblock : asmBlockAt prog as.pc
      [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MSTORE"]) :
    ∃ as', runAsm 2 offsetToPc prog as = AsmResult.AsmOK as' ∧
           as'.pc = as.pc + 2 ∧
           as'.stack = as.stack.tail := by
  rcases hblock with ⟨hlen, hget⟩
  have hpc0 : as.pc < prog.length := by
    have hne : 0 < [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MSTORE"].length := by simp
    exact asmBlockAt_pc_lt ⟨hlen, hget⟩ hne
  have hinst0 : prog.get ⟨as.pc, hpc0⟩ = AsmInst.AsmPush (encodeNumBytes off) :=
    asmBlockAt_get ⟨hlen, hget⟩ (by decide : 0 < 2)
  have hpc1 : as.pc + 1 < prog.length :=
    calc
      as.pc + 1 < as.pc + 2 := Nat.lt_succ_self (as.pc + 1)
      _ ≤ prog.length := hlen
  have hinst1 : prog.get ⟨as.pc + 1, hpc1⟩ = AsmInst.AsmOp "MSTORE" :=
    asmBlockAt_get ⟨hlen, hget⟩ (by decide : 1 < 2)
  -- Step 1: PUSH
  let pushed_val : bytes32 := wordOfBytes (List.toByteArray
    (List.replicate (32 - (encodeNumBytes off).length) (0 : byte) ++ encodeNumBytes off))
  have h1_asm : asmStep offsetToPc prog as = AsmResult.AsmOK
    ({ asmNext as with stack := pushed_val :: as.stack }) := by
    rw [asmStep_push_ok hpc0 hinst0]; rfl
  let as1 : AsmState := { asmNext as with stack := pushed_val :: as.stack }
  have hpc1_as1 : as1.pc < prog.length := by
    dsimp [as1]; simpa using hpc1
  have hinst1_as1 : prog.get ⟨as1.pc, hpc1_as1⟩ = AsmInst.AsmOp "MSTORE" := by
    dsimp [as1]; simpa using hinst1
  -- Step 2: MSTORE
  have h2_asm_eq : asmStep offsetToPc prog as1 = asmMstore as1 :=
    asmStep_mstore_ok hpc1_as1 hinst1_as1
  have h2_mstore : ∃ s', asmMstore as1 = AsmResult.AsmOK s' ∧ s'.stack = as.stack.tail ∧ s'.pc = as.pc + 2 := by
    cases hcase : as.stack
    · exact (hstk hcase).elim
    · rename_i v rest
      have has1stk : as1.stack = pushed_val :: v :: rest := by
        dsimp [as1]; simp [hcase]
      have hm : ∃ s', asmMstore as1 = AsmResult.AsmOK s' ∧ s'.stack = rest ∧ s'.pc = as1.pc + 1 :=
        asmMstore_pop2 has1stk
      rcases hm with ⟨s', hmok, hstk', hpc'⟩
      refine ⟨s', hmok, ?_, ?_⟩
      · simpa [hcase] using hstk'
      · dsimp [as1] at hpc'; dsimp [as1]; rw [hpc']; rfl
  rcases h2_mstore with ⟨as2, hm2, hstk2, hpc2⟩
  have h2_asm : asmStep offsetToPc prog as1 = AsmResult.AsmOK as2 := by
    calc
      asmStep offsetToPc prog as1 = asmMstore as1 := h2_asm_eq
      _ = AsmResult.AsmOK as2 := hm2
  have h_compose : runAsm 2 offsetToPc prog as = AsmResult.AsmOK as2 := by
    unfold runAsm
    rw [h1_asm]
    unfold runAsm
    dsimp [as1]
    rw [h2_asm]
    rfl
  refine ⟨as2, h_compose, hpc2, hstk2⟩

/-- `asmMload` with a 1+ element stack: stack → loaded_val :: rest, PC → pc+1. -/
lemma asmMload_push {s : AsmState} {offset : bytes32} {rest : List bytes32}
    (hstack : s.stack = offset :: rest) :
    ∃ s', asmMload s = AsmResult.AsmOK s' ∧
          s'.stack = wordOfBytes ((asmExpandMemory (offset.toNat + 32) s.memory).readWithPadding offset.toNat 32) :: rest ∧
          s'.pc = s.pc + 1 := by
  unfold asmMload
  rw [hstack]
  dsimp
  let mem' : ByteArray := asmExpandMemory (offset.toNat + 32) s.memory
  let bytes : ByteArray := mem'.readWithPadding offset.toNat 32
  let witness : AsmState := { asmNext s with stack := wordOfBytes bytes :: rest, memory := mem' }
  refine ⟨witness, ?_, ?_, ?_⟩
  · rfl
  · dsimp [witness]
  · dsimp [witness]; rfl
/-- PUSH+MLOAD: restore a spilled value from memory at offset `off`.
    After 2 steps: PC += 2, stack = loaded_val :: original stack. -/
theorem restore_asm_steps {offsetToPc prog as off}
    (hoff : off < 2 ^ 256)
    (hblock : asmBlockAt prog as.pc
      [AsmInst.AsmPush (encodeNumBytes off), AsmInst.AsmOp "MLOAD"]) :
    ∃ as', runAsm 2 offsetToPc prog as = AsmResult.AsmOK as' ∧
           as'.pc = as.pc + 2 ∧
           as'.stack = wordOfBytes (as.memory.readWithPadding off 32) :: as.stack := by
  sorry

/- ===== Layer 2b-2c: Deferred ===== -/

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
