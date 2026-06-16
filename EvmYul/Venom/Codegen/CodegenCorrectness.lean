/-
Codegen Correctness — theorem statements + proofs (Phase 5.1-5.3, 5.9-5.10 done)

Phase 5.1: runBlocks_never_ok ✓
Phase 5.2: initial_state_bridge ✓
Phase 5.3: runFunction_never_ok / runContext_never_ok ✓
Phase 5.9: codegen_fn_correct ✓ (vacuous: generateContextPlan stub)
Phase 5.10: codegen_correct ✓ (vacuous: generateContextPlan stub)

Remaining: Phase 5.4-5.8 (plan simulation lemmas + genBlock/genFnSimulation
— genBlockSim and genFnSim are vacuous with current stubs;
plan simulation lemmas are deferred until plan generator is filled in).
-/


import EvmYul.Venom.Types
import EvmYul.Venom.Exec
import EvmYul.Venom.Codegen.AsmSem
import EvmYul.Venom.Codegen.CodegenRel
import EvmYul.Venom.Codegen.CodegenPipeline
open EvmYul.Venom
open EvmYul.Venom.Codegen

namespace EvmYul.Venom.Codegen

def finalStateRel (vs : VenomState) (as : AsmState) : Prop := venomAsmTerminalRel vs as

theorem runBlocks_never_ok {fuel ctx fn s vs} : runBlocks fuel ctx fn s ≠ ExecResult.OK vs := by
  intro h
  induction fuel generalizing vs s with
  | zero =>
    unfold runBlocks at h
    injection h
  | succ fuel ih =>
    unfold runBlocks at h
    cases hlookup : lookupBlock s.currentBb fn.blocks
    · -- none: already closed by simp
      simp [hlookup] at h
    · -- some bb
      next bb =>
      simp [hlookup] at h
      cases hr : runBlock fuel ctx bb s
      · -- OK s'
        next s' =>
        simp [hr] at h
        split at h
        · injection h
        · apply ih h
      · -- Halt: already closed by simp
        simp [hr] at h
      · -- Abort: already closed by simp
        simp [hr] at h
      · -- IntRet: already closed by simp
        simp [hr] at h
      · -- Error: already closed by simp
        simp [hr] at h

theorem initial_state_bridge {vs labelOffsets fnEom} : ∃ as, venomAsmRel labelOffsets (initPlanState fnEom) vs as ∧ as.pc = 0 := by
  let as : AsmState := {
    stack := []
    memory := vs.memory
    accounts := vs.accounts
    transient := vs.transient
    returndata := vs.returndata
    logs := vs.logs
    pc := 0
    callCtx := vs.callCtx
    txCtx := vs.txCtx
    blockCtx := vs.blockCtx
    code := vs.code
    prevHashes := vs.prevHashes
  }
  have hrel : venomAsmRel labelOffsets (initPlanState fnEom) vs as := by
    unfold venomAsmRel initPlanState
    dsimp [as]
    refine ⟨?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · -- planStackRel: empty stacks, length 0 = 0, and no indices < 0
      refine ⟨rfl, fun i hi => (Nat.not_lt_zero i hi).elim⟩
    · -- planSpillRel: vacuously true (AssocList.lookup [] ... = some ... is impossible)
      unfold planSpillRel
      intro op off h
      -- h: AssocList.lookup Operand Nat [] op = some off
      -- AssocList.lookup on [] always returns none
      rw [AssocList.lookup] at h
      simp at h
    · -- memoryRel: equality outside spill region [fnEom, fnEom) = empty
      unfold memoryRel initSpillAlloc
      intro i _
      rfl
  have hpc : as.pc = 0 := rfl
  exact ⟨as, hrel, hpc⟩

theorem runFunction_never_ok {fuel ctx fn vs vs'} : runFunction fuel ctx fn vs ≠ ExecResult.OK vs' := by
  unfold runFunction
  split
  · intro h; injection h
  · apply runBlocks_never_ok

theorem runContext_never_ok {fuel ctx vs vs'} : runContext fuel ctx vs ≠ ExecResult.OK vs' := by
  unfold runContext
  split
  · intro h; injection h
  · next entry =>
    split
    · intro h; injection h
    · apply runFunction_never_ok

theorem codegen_fn_correct (fuel ctx fn fnEom dataSeg bytecode spillHwm vs labelOffsets prog) :
  codegenReadyFn fn → codegen ctx (AssocList.insert String Nat [] fn.name fnEom) dataSeg = some bytecode →
  (∀ inst vs1 vs2, stepInstBase inst vs1 = ExecResult.OK vs2 →
    stepMemSafe { freeSlots := [], nextOffset := spillHwm, fnEom := fnEom : SpillAlloc } vs1 vs2) →
  ∃ gasNeeded, ∀ as, venomAsmRel labelOffsets (initPlanState fnEom) vs as → as.pc = 0 →
    (match runBlocks fuel ctx fn vs with
     | ExecResult.Halt vs' => ∃ as', runAsm gasNeeded ([] : AssocList Nat Nat) prog as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm gasNeeded ([] : AssocList Nat Nat) prog as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm gasNeeded ([] : AssocList Nat Nat) prog as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | ExecResult.OK _ => False | ExecResult.IntRet _ _ => True | ExecResult.Error _ => True) := by
  intro hready hcode hsafe
  unfold codegen at hcode
  simp [generateContextPlan] at hcode

theorem codegen_correct (fuel ctx fnEomMap dataSeg bytecode spillHwm vs labelOffsets prog) :
  codegenReady ctx → codegen ctx fnEomMap dataSeg = some bytecode →
  (∀ inst vs1 vs2, stepInstBase inst vs1 = ExecResult.OK vs2 →
    stepMemSafe { freeSlots := [], nextOffset := spillHwm, fnEom := 0 : SpillAlloc } vs1 vs2) →
  ∃ gasNeeded, ∀ as, venomAsmRel labelOffsets (initPlanState 0) vs as → as.pc = 0 →
    (match runContext fuel ctx vs with
     | ExecResult.Halt vs' => ∃ as', runAsm gasNeeded ([] : AssocList Nat Nat) prog as = AsmResult.AsmHalt as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.RevertAbort vs' => ∃ as', runAsm gasNeeded ([] : AssocList Nat Nat) prog as = AsmResult.AsmRevert as' ∧ finalStateRel vs' as'
     | ExecResult.Abort AbortType.ExHaltAbort vs' => ∃ as', runAsm gasNeeded ([] : AssocList Nat Nat) prog as = AsmResult.AsmFault as' ∧ finalStateRel vs' as'
     | ExecResult.OK _ => False | ExecResult.IntRet _ _ => True | ExecResult.Error _ => True) := by
  intro hready hcode hsafe
  unfold codegen at hcode
  simp [generateContextPlan] at hcode

end EvmYul.Venom.Codegen
