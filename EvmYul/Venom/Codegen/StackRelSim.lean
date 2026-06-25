/-
Stack Relation Simulation Lemmas — Layer 2
-/

import EvmYul.Venom.Types
import Mathlib.Tactic
import EvmYul.Venom.Codegen.StackModel
import EvmYul.Venom.Codegen.CodegenRel
open EvmYul.Venom

namespace EvmYul.Venom.Codegen

lemma getI_drop_add {α : Type} [Inhabited α] (l : List α) (n i : Nat) : (l.drop n).get! i = l.get! (i + n) := by
  rw [List_get!_eq_getElem?_getD, List_get!_eq_getElem?_getD, List.getElem?_drop, add_comm]

theorem planStackRel_push {labelOffsets vs psStack asmStack op w}
    (hrel : planStackRel labelOffsets vs psStack asmStack)
    (hop : operandVal vs labelOffsets op = some w) :
    planStackRel labelOffsets vs (stackPush op psStack) (w :: asmStack) := by
  rcases hrel with ⟨hlen, hget⟩
  have hlen' : (stackPush op psStack).length = (w :: asmStack).length := by
    simp [stackPush, hlen]
  refine ⟨hlen', λ i hi => ?_⟩
  rw [stackPush] at hi ⊢
  simp at hi
  rcases i with (rfl | i)
  · simp [hop]
  · have hi' : i < psStack.length := by omega
    have h_val : (psStack ++ [op]).reverse.get! (i + 1) = psStack.reverse.get! i := by
      simp
    have h_asm : (w :: asmStack).get! (i + 1) = asmStack.get! i := by
      simp
    rw [h_val, h_asm]
    exact hget i hi'

theorem planStackRel_pop {labelOffsets vs psStack asmStack n}
    (hrel : planStackRel labelOffsets vs psStack asmStack)
    (hn : n ≤ psStack.length) :
    planStackRel labelOffsets vs (stackPop n psStack) (asmStack.drop n) := by
  rcases hrel with ⟨hlen, hget⟩
  have hlen' : (stackPop n psStack).length = (asmStack.drop n).length := by
    simp [stackPop, hlen]
  refine ⟨hlen', λ i hi => ?_⟩
  have h_rev : (psStack.take (psStack.length - n)).reverse = psStack.reverse.drop n := by
    rw [List.reverse_take]
    have : psStack.length - (psStack.length - n) = n := by omega
    rw [this]
  have hi_ps : i + n < psStack.length := by
    rw [stackPop] at hi
    have hi_len : i < (psStack.take (psStack.length - n)).length := hi
    rw [List.length_take] at hi_len; omega
  rw [stackPop]
  rw [h_rev]
  have h_drop_get : (psStack.reverse.drop n).get! i = psStack.reverse.get! (i + n) :=
    getI_drop_add (psStack.reverse) n i
  have h_asm_drop_get : (asmStack.drop n).get! i = asmStack.get! (i + n) :=
    getI_drop_add asmStack n i
  calc
    operandVal vs labelOffsets ((psStack.reverse.drop n).get! i)
        = operandVal vs labelOffsets (psStack.reverse.get! (i + n)) := by rw [h_drop_get]
    _ = some (asmStack.get! (i + n)) := hget (i + n) hi_ps
    _ = some ((asmStack.drop n).get! i) := by rw [h_asm_drop_get]

theorem planStackRel_dup {labelOffsets vs psStack asmStack dist}
    (hrel : planStackRel labelOffsets vs psStack asmStack)
    (hdist : dist < psStack.length) :
    planStackRel labelOffsets vs (stackDup dist psStack)
      (asmStack.get! dist :: asmStack) := by
  have hpeek : operandVal vs labelOffsets (stackPeek dist psStack) = some (asmStack.get! dist) :=
    planStackRel_peek hrel hdist
  have h_push := planStackRel_push hrel hpeek
  simpa [stackDup, stackPush] using h_push

end EvmYul.Venom.Codegen
