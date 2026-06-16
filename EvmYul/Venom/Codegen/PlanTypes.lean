/-
Stack Plan Types — Venom Codegen Layer 3

Port of vyper-hol/venom/codegen/defs/stackPlanTypesScript.sml

Plan state types and spill slot allocation.
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Codegen.AsmIR
open EvmYul.Venom
open EvmYul.Venom.Codegen

namespace EvmYul.Venom.Codegen

/- ===== Spill Allocator State ===== -/

structure SpillAlloc where
  freeSlots   : List Nat
  nextOffset  : Nat
  fnEom       : Nat
  deriving Inhabited

/- ===== Plan Generator State ===== -/

-- AssocList-based spilled operands map (operand → memory offset)
abbrev SpilledMap := AssocList Operand Nat

structure PlanState where
  stack         : List Operand
  spilled       : SpilledMap
  alloc         : SpillAlloc
  labelCounter  : Nat
  deriving Inhabited

/- ===== Spill Slot Management ===== -/

/-- Allocate a new spill slot. Returns (offset, updated allocator). -/
def allocSpillSlot (alloc : SpillAlloc) : Nat × SpillAlloc :=
  match alloc.freeSlots with
  | [] => (alloc.nextOffset, { alloc with nextOffset := alloc.nextOffset + 32 })
  | slots =>
    (slots.getLastD 0, { alloc with freeSlots := slots.dropLast })

/-- Free a spill slot. -/
def freeSpillSlot (off : Nat) (alloc : SpillAlloc) : SpillAlloc :=
  { alloc with freeSlots := alloc.freeSlots ++ [off] }

/-- Initialize spill allocator. -/
def initSpillAlloc (fnEom : Nat) : SpillAlloc :=
  { freeSlots := [], nextOffset := fnEom, fnEom := fnEom }

/-- Initialize plan state. -/
def initPlanState (fnEom : Nat) : PlanState :=
  { stack := [], spilled := [], alloc := initSpillAlloc fnEom, labelCounter := 0 }

end EvmYul.Venom.Codegen
