/-
DFG Analysis — Data-Flow Graph for Venom IR

Port of vyper-hol/venom/analysis/dfg/defs/dfgDefsScript.sml

Tracks:
 - Uses: variable → instructions that read it
 - Defs: variable → producing instruction
 - IDs: instruction id → instruction

Key functions:
 - dfg_build_function — build DFG from a function
 - normalize_operand — follow ASSIGN chain to root operand
 - operand_equiv — two operands are equivalent after normalization
-/

import EvmYul.Venom.Types
open EvmYul.Venom

namespace EvmYul.Venom.Codegen

/- ===== DFG Analysis Record ===== -/

structure DfgAnalysis where
  dfgUses : AssocList String (List Instruction)  -- variable → instructions that use it
  dfgDefs : AssocList String Instruction          -- variable → producing instruction
  dfgIds  : AssocList Nat Instruction             -- instruction id → instruction
  deriving Inhabited

def dfgEmpty : DfgAnalysis :=
  { dfgUses := [], dfgDefs := [], dfgIds := [] }

/-- Get uses of a variable (instructions that read it). -/
def dfgGetUses (dfg : DfgAnalysis) (v : String) : List Instruction :=
  match AssocList.lookup String (List Instruction) dfg.dfgUses v with
  | none => []
  | some uses => uses

/-- Get the defining instruction for a variable. -/
def dfgGetDef (dfg : DfgAnalysis) (v : String) : Option Instruction :=
  AssocList.lookup String Instruction dfg.dfgDefs v

/-- Get instruction by id. -/
def dfgGetInstById (dfg : DfgAnalysis) (id : Nat) : Option Instruction :=
  AssocList.lookup Nat Instruction dfg.dfgIds id

/- ===== Operand Helpers ===== -/

/-- Extract variable name from an Operand, if it is a Var. -/
def operandVar : Operand → Option String
  | Operand.Var v => some v
  | _ => none

/-- Extract all variable names from a list of operands. -/
def operandVars : List Operand → List String
  | [] => []
  | op :: ops =>
    match operandVar op with
    | none => operandVars ops
    | some v => v :: operandVars ops

/-- Check if an instruction is commutative (order of top two operands doesn't matter). -/
def isCommutative (opc : Opcode) : Bool :=
  match opc with
  | Opcode.ADD | Opcode.MUL | Opcode.AND | Opcode.OR | Opcode.XOR
  | Opcode.EQ | Opcode.ADDMOD | Opcode.MULMOD => true
  | _ => false

/- ===== DFG Construction Helpers ===== -/

/-- Add a use of variable v by instruction inst to the DFG. -/
def dfgAddUse (dfg : DfgAnalysis) (v : String) (inst : Instruction) : DfgAnalysis :=
  let uses := dfgGetUses dfg v
  if uses.any (λ u => u.id = inst.id) then dfg
  else { dfg with dfgUses := AssocList.insert String (List Instruction) dfg.dfgUses v (inst :: uses) }

/-- Add uses of multiple variables by an instruction. -/
def dfgAddUses (dfg : DfgAnalysis) (vars : List String) (inst : Instruction) : DfgAnalysis :=
  vars.foldl (λ d v => dfgAddUse d v inst) dfg

/-- Add a defining instruction for a variable. -/
def dfgAddDef (dfg : DfgAnalysis) (v : String) (inst : Instruction) : DfgAnalysis :=
  { dfg with dfgDefs := AssocList.insert String Instruction dfg.dfgDefs v inst }

/-- Add a full instruction to the DFG (uses + defs + id). -/
def dfgAddInst (dfg : DfgAnalysis) (inst : Instruction) : DfgAnalysis :=
  let inVars := operandVars inst.operands
  let dfg1 := dfgAddUses dfg inVars inst
  let dfg2 := inst.outputs.foldl (λ d v => dfgAddDef d v inst) dfg1
  { dfg2 with dfgIds := AssocList.insert Nat Instruction dfg2.dfgIds inst.id inst }

/-- Build DFG from an instruction list (reversed for correct use/def order). -/
def dfgBuildInsts (insts : List Instruction) : DfgAnalysis :=
  insts.foldl (λ dfg inst => dfgAddInst dfg inst) dfgEmpty

/-- Build DFG for a function. -/
def dfgBuildFunction (fn : IrFunction) : DfgAnalysis :=
  dfgBuildInsts (fn.blocks.foldl (λ acc bb => acc ++ bb.instructions) [])

/- ===== Assign Chain Traversal ===== -/

/-- Follow ASSIGN chain to root operand.
    Matches Python's dfg._traverse_assign_chain.
    Uses a visited set for termination (each step adds current var to visited). -/
partial def normalizeOperand (dfg : DfgAnalysis) (visited : List String) (op : Operand) : Operand :=
  match op with
  | Operand.Var v =>
    if visited.contains v then Operand.Var v
    else
      match dfgGetDef dfg v with
      | some inst =>
        if inst.opcode = Opcode.ASSIGN then
          match inst.operands with
          | [arg] => normalizeOperand dfg (v :: visited) arg
          | _ => Operand.Var v
        else Operand.Var v
      | none => Operand.Var v
  | op => op

/-- Two operands are equivalent if they normalize to the same root
    through ASSIGN chain traversal. -/
def operandEquiv (dfg : DfgAnalysis) (op1 op2 : Operand) : Bool :=
  normalizeOperand dfg [] op1 = normalizeOperand dfg [] op2

end EvmYul.Venom.Codegen
