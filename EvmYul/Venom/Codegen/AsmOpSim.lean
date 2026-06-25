/-
Asm Operation Simulation Lemmas — Group A
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Codegen.PlanExec
import EvmYul.Venom.Codegen.AsmSem
import EvmYul.Venom.Codegen.CodegenRel
import EvmYul.Venom.Codegen.StackModel
open EvmYul.Venom

namespace EvmYul.Venom.Codegen


/-- `@[simp]` lemma: expands `runAsm (Nat.succ n)` to the `match` expression. -/
@[simp] theorem runAsm_succ_eq (n : Nat) (offsetToPc : AssocList Nat Nat) (prog : List AsmInst) (s : AsmState) :
    runAsm (Nat.succ n) offsetToPc prog s =
    (match asmStep offsetToPc prog s with
     | AsmResult.AsmOK s' => runAsm n offsetToPc prog s'
     | other => other) := rfl

@[simp] theorem assocLookup_swapTable_SWAP1 : assocLookup swapTable "SWAP1" = some 1 := by
  native_decide

@[simp] theorem assocLookup_dupTable_SWAP1 : assocLookup dupTable "SWAP1" = none := by
  native_decide

@[simp] theorem assocLookup_swapTable_SWAP2 : assocLookup swapTable "SWAP2" = some 2 := by
  native_decide

@[simp] theorem assocLookup_dupTable_SWAP2 : assocLookup dupTable "SWAP2" = none := by
  native_decide

@[simp] theorem assocLookup_swapTable_SWAP3 : assocLookup swapTable "SWAP3" = some 3 := by
  native_decide

@[simp] theorem assocLookup_dupTable_SWAP3 : assocLookup dupTable "SWAP3" = none := by
  native_decide

@[simp] theorem assocLookup_swapTable_SWAP4 : assocLookup swapTable "SWAP4" = some 4 := by
  native_decide

@[simp] theorem assocLookup_dupTable_SWAP4 : assocLookup dupTable "SWAP4" = none := by
  native_decide

@[simp] theorem assocLookup_swapTable_SWAP5 : assocLookup swapTable "SWAP5" = some 5 := by
  native_decide

@[simp] theorem assocLookup_dupTable_SWAP5 : assocLookup dupTable "SWAP5" = none := by
  native_decide

@[simp] theorem assocLookup_swapTable_SWAP6 : assocLookup swapTable "SWAP6" = some 6 := by
  native_decide

@[simp] theorem assocLookup_dupTable_SWAP6 : assocLookup dupTable "SWAP6" = none := by
  native_decide

@[simp] theorem assocLookup_swapTable_SWAP7 : assocLookup swapTable "SWAP7" = some 7 := by
  native_decide

@[simp] theorem assocLookup_dupTable_SWAP7 : assocLookup dupTable "SWAP7" = none := by
  native_decide

@[simp] theorem assocLookup_swapTable_SWAP8 : assocLookup swapTable "SWAP8" = some 8 := by
  native_decide

@[simp] theorem assocLookup_dupTable_SWAP8 : assocLookup dupTable "SWAP8" = none := by
  native_decide

@[simp] theorem assocLookup_swapTable_SWAP9 : assocLookup swapTable "SWAP9" = some 9 := by
  native_decide

@[simp] theorem assocLookup_dupTable_SWAP9 : assocLookup dupTable "SWAP9" = none := by
  native_decide



theorem asmStep_push_ok {offsetToPc prog s bytes}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmPush bytes) :
    asmStep offsetToPc prog s =
      asmPushVal (wordOfBytes (List.toByteArray
        (List.replicate (32 - bytes.length) (0 : byte) ++ bytes))) s := by
  unfold asmStep; rw [dif_pos hpc, hprog]

theorem asmStep_pop_ok {offsetToPc prog s}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "POP")
    (hne : s.stack ≠ []) :
    ∃ stk, asmStep offsetToPc prog s = AsmResult.AsmOK ({ asmNext s with stack := stk }) ∧
           stk.length + 1 = s.stack.length := by
  cases hstk : s.stack with
  | nil => exfalso; exact hne hstk
  | cons h stk =>
    refine ⟨stk, ?_, by simp⟩
    unfold asmStep; rw [dif_pos hpc, hprog, asmPop, hstk]; rfl

theorem asmStep_swap_ok {offsetToPc prog s n}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp (swapName n))
    (hn0 : 0 < n) (hn16 : n ≤ 16) (hnlen : n < s.stack.length) :
    asmStep offsetToPc prog s = asmSwap n s := by
  have hn_range : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨
                 n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 ∨ n = 16 := by
    omega
  rcases hn_range with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl
  · unfold asmStep; rw [dif_pos hpc, hprog]; dsimp; rfl

theorem asmStep_mstore_ok {offsetToPc prog s}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "MSTORE") :
    asmStep offsetToPc prog s = asmMstore s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

theorem asmStep_mload_ok {offsetToPc prog s}
    (hpc : s.pc < prog.length)
    (hprog : prog.get ⟨s.pc, hpc⟩ = AsmInst.AsmOp "MLOAD") :
    asmStep offsetToPc prog s = asmMload s := by
  unfold asmStep; rw [dif_pos hpc, hprog]; rfl

theorem runAsm_succ_ok {offsetToPc prog s1 s2 n}
    (hpc : s1.pc < prog.length)
    (hstep : asmStep offsetToPc prog s1 = AsmResult.AsmOK s2) :
    runAsm (n + 1) offsetToPc prog s1 = runAsm n offsetToPc prog s2 := by
  have hn : n + 1 = Nat.succ n := by omega
  rw [hn]
  simp [runAsm_succ_eq, hstep]

theorem runAsm_compose {n m offsetToPc prog as s1 s2}
    (h1 : runAsm n offsetToPc prog as = AsmResult.AsmOK s1)
    (h2 : runAsm m offsetToPc prog s1 = AsmResult.AsmOK s2) :
    runAsm (n + m) offsetToPc prog as = AsmResult.AsmOK s2 := by
  induction n generalizing as with
  | zero =>
    have has : as = s1 := by
      unfold runAsm at h1; simp at h1; exact h1
    subst as; simpa using h2
  | succ n ih =>
    have hn_succ : Nat.succ n + m = Nat.succ (n + m) := by omega
    rw [hn_succ]
    have h1_expanded : (match asmStep offsetToPc prog as with
                        | AsmResult.AsmOK s' => runAsm n offsetToPc prog s'
                        | other => other) = AsmResult.AsmOK s1 := by
      simpa [runAsm_succ_eq] using h1
    cases h_asm : asmStep offsetToPc prog as with
    | AsmOK s' =>
      rw [h_asm] at h1_expanded
      simp at h1_expanded
      simp [runAsm_succ_eq] at *
      rw [h_asm]
      simp
      exact ih h1_expanded
    | _ =>
      rw [h_asm] at h1_expanded
      simp at h1_expanded

end EvmYul.Venom.Codegen
