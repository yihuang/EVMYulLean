/-
Stack Plan Operations — Venom Codegen Layer 4

Port of vyper-hol/venom/codegen/defs/stackPlanOpsScript.sml

Operations:
  do_spill_at, do_restore — spill/restore with spill slot management
  do_swap, do_dup — swap/dup with deep-stack spill handling
  reorder_plan — arrange operands on stack
  popmany_plan — pop a set of variables
  release_dead_spills — clean up dead spill slots
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Codegen.AsmIR
import EvmYul.Venom.Codegen.StackModel
import EvmYul.Venom.Codegen.PlanTypes
open EvmYul.Venom
open EvmYul.Venom.Codegen

namespace EvmYul.Venom.Codegen

/- ===== Helpers ===== -/

def alookup' {α β : Type} [BEq α] (al : AssocList α β) (k : α) : Option β := AssocList.lookup α β al k
def ainsert' {α β : Type} [BEq α] (al : AssocList α β) (k : α) (v : β) : AssocList α β := AssocList.insert α β al k v
def aremove {α β : Type} [BEq α] (al : AssocList α β) (k : α) : AssocList α β :=
  al.filter (λ (k', _) => k' != k)

/- ===== Basic Spill/Restore ===== -/

/-- Spill TOS to a fresh memory slot. -/
def doSpillTos (ps : PlanState) : List StackOp × PlanState :=
  let (off, alloc') := allocSpillSlot ps.alloc
  let op := stackPeek 0 ps.stack
  ([StackOp.SOSpill off],
   { ps with
     stack := stackPop 1 ps.stack
     spilled := ainsert' ps.spilled op off
     alloc := alloc' })

/-- Spill operand at distance dist from TOS. -/
def doSpillAt (dist : Nat) (ps : PlanState) : List StackOp × PlanState :=
  if dist = 0 then doSpillTos ps
  else
    let ps' := { ps with stack := stackSwap dist ps.stack }
    let (spillOps, ps'') := doSpillTos ps'
    (StackOp.SOSwap dist :: spillOps, ps'')

/-- Restore a spilled operand from memory. -/
def doRestore (op : Operand) (ps : PlanState) : List StackOp × PlanState :=
  match alookup' ps.spilled op with
  | none => ([], ps)
  | some off =>
    let alloc' := freeSpillSlot off ps.alloc
    ([StackOp.SORestore off],
     { ps with
       stack := stackPush op ps.stack
       spilled := aremove ps.spilled op
       alloc := alloc' })

/- ===== Swap/Dup with Deep Stack Support ===== -/

/-- Get top n items from stack (TOS first). -/
def topN (n : Nat) (stk : List Operand) : List Operand :=
  (stk.reverse.take n).reverse

/-- Swap at distance from TOS (0-based).
    dist=0 → noop. dist 1..16 → SWAP{dist}. dist>16 → bulk spill/restore. -/
def doSwap (dist : Nat) (ps : PlanState) : List StackOp × PlanState :=
  if dist = 0 then ([], ps)
  else if dist ≤ 16 then
    ([StackOp.SOSwap dist],
     { ps with stack := stackSwap dist ps.stack })
  else
    let chunk := dist + 1
    let items := topN chunk ps.stack
    -- Spill chunk items to fresh slots
    let init : List StackOp × List Nat × SpillAlloc := ([], [], ps.alloc)
    let (spillOps, offsets, alloc') :=
      items.foldl (λ (ops, offs, al) item =>
        let (off, al') := allocSpillSlot al
        (ops ++ [StackOp.SOSpill off], offs ++ [off], al'))
        init
    let baseStack := ps.stack.take (ps.stack.length - chunk)
    -- Desired order: swap first and last, keep middle
    let desired := [chunk - 1] ++ (List.range (chunk - 2)).map (· + 1) ++ [0]
    -- Restore in reverse desired order (last pushed = TOS)
    let restoreOps := desired.reverse.map (λ idx => StackOp.SORestore (offsets.get! idx))
    let alloc'' := offsets.foldl (λ al off => freeSpillSlot off al) alloc'
    let restored := desired.map (λ idx => items.get! idx)
    (spillOps ++ restoreOps,
     { ps with stack := baseStack ++ restored, alloc := alloc'' })

/-- Dup at distance from TOS (0-based).
    dist≤15 → DUP{dist+1}. dist>15 → bulk spill/restore with dup. -/
def doDup (dist : Nat) (ps : PlanState) : List StackOp × PlanState :=
  if dist ≤ 15 then
    ([StackOp.SODup (dist + 1)],
     { ps with stack := stackDup dist ps.stack })
  else
    let chunk := dist + 1
    let items := topN chunk ps.stack
    let init : List StackOp × List Nat × SpillAlloc := ([], [], ps.alloc)
    let (spillOps, offsets, alloc') :=
      items.foldl (λ (ops, offs, al) item =>
        let (off, al') := allocSpillSlot al
        (ops ++ [StackOp.SOSpill off], offs ++ [off], al'))
        init
    let baseStack := ps.stack.take (ps.stack.length - chunk)
    -- Desired: all original ++ duplicate first (deepest)
    let desired := List.range chunk ++ [0]
    let restoreOps := desired.reverse.map (λ idx => StackOp.SORestore (offsets.get! idx))
    let alloc'' := offsets.foldl (λ al off => freeSpillSlot off al) alloc'
    let restored := desired.map (λ idx => items.get! idx)
    (spillOps ++ restoreOps,
     { ps with stack := baseStack ++ restored, alloc := alloc'' })

/- ===== Reorder ===== -/

/-- Reorder one operand to its target position. -/
def reorderOne (dfg : Unit) (targetOps : List Operand) (targetIdx : Nat) (op : Operand) (ps : PlanState) : List StackOp × PlanState :=
  let numOps := targetOps.length
  let finalDist := numOps - 1 - targetIdx
  -- Find or restore operand
  let (restoreOps, ps1) :=
    match stackGetDepth op ps.stack with
    | some _ => ([], ps)
    | none =>
      match alookup' ps.spilled op with
      | some _ => doRestore op ps
      | none => ([], ps)
  match stackGetDepth op ps1.stack with
  | none => (restoreOps, ps1)
  | some dist =>
    -- Swap to final position
    if dist = finalDist then (restoreOps, ps1)
    else
      let (swapOps, ps2) := doSwap dist ps1
      let (swapOps2, ps3) := doSwap finalDist ps2
      (restoreOps ++ swapOps ++ swapOps2, ps3)

/-- Reorder stack to match target_ops layout. -/
def reorderPlan (targetOps : List Operand) (ps : PlanState) : List StackOp × PlanState :=
  targetOps.enum.foldl (λ (ops, ps) (idx, op) =>
    let (stepOps, ps') := reorderOne () targetOps idx op ps
    (ops ++ stepOps, ps'))
    ([], ps)

/- ===== Simple Sort Helpers ===== -/

/-- Insert an element into a sorted list. -/
def insertSorted {α : Type} (le : α → α → Bool) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if le x y then x :: y :: ys else y :: insertSorted le x ys

/-- Insertion sort. -/
def sortBy {α : Type} (le : α → α → Bool) (l : List α) : List α :=
  l.foldl (λ acc x => insertSorted le x acc) []

/- ===== Popmany ===== -/

/-- Check if depths form {1, 2, ..., n} (not including TOS=0). -/
def isContiguousTop (depths : List Nat) : Bool :=
  let n := depths.length
  let sorted := sortBy (· ≤ ·) depths
  sorted = List.range n && n ≤ 16

/-- Popmany: pop the given operands from stack. -/
def popmanyPlan (toPop : List Operand) (ps : PlanState) : List StackOp × PlanState :=
  if toPop.isEmpty then ([], ps)
  else
    let depthsOpt := toPop.map (λ v => stackGetDepth v ps.stack)
    if depthsOpt.all Option.isSome then
      let depths := depthsOpt.map Option.get!
      let n := toPop.length
      if isContiguousTop depths then
        let (swapOps, ps') := doSwap n ps
        (swapOps ++ [StackOp.SOPop n],
         { ps' with stack := stackPop n ps'.stack })
      else
        -- Individual swap+pop per item
        let sorted := sortBy (λ a b =>
          match stackGetDepth a ps.stack, stackGetDepth b ps.stack with
          | some da, some db => da ≤ db
          | _, _ => true) toPop
        sorted.foldl (λ (ops, ps) v =>
          match stackGetDepth v ps.stack with
          | none => (ops, ps)
          | some dist =>
            let (swapOps, ps') :=
              if dist = 0 then ([], ps)
              else doSwap dist ps
            (ops ++ swapOps ++ [StackOp.SOPop 1],
             { ps' with stack := stackPop 1 ps'.stack }))
          ([], ps)
    else
      -- Fallback: individual
      let sorted := sortBy (λ a b =>
        match stackGetDepth a ps.stack, stackGetDepth b ps.stack with
        | some da, some db => da ≤ db
        | _, _ => true) toPop
      sorted.foldl (λ (ops, ps) v =>
        match stackGetDepth v ps.stack with
        | none => (ops, ps)
        | some dist =>
          let (swapOps, ps') :=
            if dist = 0 then ([], ps)
            else doSwap dist ps
          (ops ++ swapOps ++ [StackOp.SOPop 1],
           { ps' with stack := stackPop 1 ps'.stack }))
        ([], ps)

/- ===== Release Dead Spills ===== -/

/-- Free spill slots for operands not in next_liveness. -/
def releaseDeadSpills (nextLiveness : List String) (ps : PlanState) : PlanState :=
  ps.spilled.foldl (λ ps' (op, off) =>
    match op with
    | Operand.Var v =>
      if nextLiveness.contains v then ps'
      else { ps' with spilled := aremove ps'.spilled op, alloc := freeSpillSlot off ps'.alloc }
    | _ =>
      { ps' with spilled := aremove ps'.spilled op, alloc := freeSpillSlot off ps'.alloc })
    ps

end EvmYul.Venom.Codegen
