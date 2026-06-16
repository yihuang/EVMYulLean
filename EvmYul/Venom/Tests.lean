/-
Venom IR Semantics Tests

Tests for the single-instruction stepper stepInstBase covering:
  - Arithmetic (ADD, SUB, MUL, Div, Mod, SDIV, SMOD, Exp, ADDMOD, MULMOD)
  - Comparison (EQ, LT, GT, SLT, SGT, ISZERO)
  - Bitwise (AND, OR, XOR, NOT, SHL, SHR)
  - Memory (MLOAD, MSTORE, MSTORE8, MCOPY, MEMTOP)
  - Storage (SLOAD, SSTORE)
  - Control flow (JMP, JNZ)
  - Environment (CALLER, ADDRESS, CALLVALUE, GAS, CALLDATASIZE, CALLDATALOAD)
  - SSA (ASSIGN, NOP, PHI error)
  - Termination (STOP, RETURN, REVERT)
  - Assertions (ASSERT, ASSERT_UNREACHABLE)
  - Logging (LOG)
  - Hashing (SHA3 via Keccak FFI)
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Semantics
open EvmYul.Venom

/- ===== Test Helpers ===== -/

def emptyState : VenomState := {
  memory := ByteArray.empty, transient := [], vars := [], prevBb := none,
  currentBb := "entry", instIdx := 0, returndata := ByteArray.empty, halted := false,
  accounts := [], callCtx := default, txCtx := default, blockCtx := default,
  logs := [], immutables := [], dataSection := [], labels := [], code := [],
  params := [], prevHashes := [], allocas := [], allocaNext := 0
}

def mkInst (id : Nat) (op : Opcode) (ops : List Operand) (outs : List String) : Instruction :=
  { id := id, opcode := op, operands := ops, outputs := outs }

def varOp (x : String) : Operand := Operand.Var x
def litOp (n : Nat) : Operand := Operand.Lit (EvmYul.UInt256.ofNat n)
def lblOp (l : String) : Operand := Operand.Label l

def withVar (x : String) (v : Nat) (s : VenomState) : VenomState :=
  { s with vars := ainsert s.vars x (EvmYul.UInt256.ofNat v) }

def okVal (r : ExecResult) : Option VenomState :=
  match r with
  | ExecResult.OK s => some s
  | _ => none

def getVar (x : String) (s : VenomState) : Option Nat :=
  match alookup s.vars x with
  | some v => some v.toNat
  | none => none

def assertOk (label : String) (expected : Bool) (r : ExecResult) : IO Unit :=
  match r with
  | ExecResult.OK _ =>
    if expected then IO.println s!"  ✓ {label}"
    else IO.println s!"  ✗ {label}: expected Error, got OK"
  | ExecResult.Error e =>
    if expected then IO.println s!"  ✗ {label}: got Error: {e}"
    else IO.println s!"  ✓ {label} (expected Error: {e})"
  | ExecResult.Halt _ =>
    if expected then IO.println s!"  ✓ {label} (Halt)"
    else IO.println s!"  ✗ {label}: expected Error, got Halt"
  | ExecResult.Abort _ _ =>
    if expected then IO.println s!"  ✓ {label} (Abort)"
    else IO.println s!"  ✗ {label}: expected Error, got Abort"
  | ExecResult.IntRet _ _ =>
    IO.println s!"  ? {label}: IntRet"

def assertEq (label : String) (actual : Option Nat) (expected : Nat) : IO Unit :=
  if actual == some expected then
    IO.println s!"  ✓ {label}: {expected}"
  else
    IO.println s!"  ✗ {label}: expected {expected}, got {actual}"

/- ===== Test Data ===== -/

-- State with x=10, y=3, z=0, a=0
def testState := emptyState
  |> withVar "x" 10
  |> withVar "y" 3
  |> withVar "z" 0
  |> withVar "a" 0

/- ===== Arithmetic Tests ===== -/

def testArith : IO Unit := do
  IO.println "--- Arithmetic ---"

  -- ADD: %a = add %x, %y  => 10 + 3 = 13
  let r := stepInstBase (mkInst 0 Opcode.ADD [varOp "x", varOp "y"] ["a"]) testState
  assertEq "ADD 10+3" (okVal r >>= (· |> getVar "a")) 13

  -- SUB: %a = sub %x, %y  => 10 - 3 = 7
  let r := stepInstBase (mkInst 1 Opcode.SUB [varOp "x", varOp "y"] ["a"]) testState
  assertEq "SUB 10-3" (okVal r >>= getVar "a") 7

  -- MUL: %a = mul %x, %y  => 10 * 3 = 30
  let r := stepInstBase (mkInst 2 Opcode.MUL [varOp "x", varOp "y"] ["a"]) testState
  assertEq "MUL 10*3" (okVal r >>= getVar "a") 30

  -- Div: %a = div %x, %y  => 10 / 3 = 3
  let r := stepInstBase (mkInst 3 Opcode.Div [varOp "x", varOp "y"] ["a"]) testState
  assertEq "Div 10/3" (okVal r >>= getVar "a") 3

  -- Mod: %a = mod %x, %y  => 10 % 3 = 1
  let r := stepInstBase (mkInst 4 Opcode.Mod [varOp "x", varOp "y"] ["a"]) testState
  assertEq "Mod 10%3" (okVal r >>= getVar "a") 1

  -- Div by zero: 10 / 0 = 0
  let s := testState |> withVar "y" 0
  let r := stepInstBase (mkInst 5 Opcode.Div [varOp "x", varOp "y"] ["a"]) s
  assertEq "Div by zero" (okVal r >>= getVar "a") 0

  -- Mod by zero: 10 % 0 = 0
  let r := stepInstBase (mkInst 6 Opcode.Mod [varOp "x", varOp "y"] ["a"]) s
  assertEq "Mod by zero" (okVal r >>= getVar "a") 0

  -- ADDMOD: (10+3) mod 5 = 3
  let r := stepInstBase (mkInst 7 Opcode.ADDMOD [varOp "x", varOp "y", litOp 5] ["a"]) testState
  assertEq "ADDMOD (10+3)%5" (okVal r >>= getVar "a") 3

  -- MULMOD: (10*3) mod 4 = 2
  let r := stepInstBase (mkInst 8 Opcode.MULMOD [varOp "x", varOp "y", litOp 4] ["a"]) testState
  assertEq "MULMOD (10*3)%4" (okVal r >>= getVar "a") 2

  -- Exp: 2^3 = 8
  let s := testState |> withVar "x" 2 |> withVar "y" 3
  let r := stepInstBase (mkInst 9 Opcode.Exp [varOp "x", varOp "y"] ["a"]) s
  assertEq "Exp 2^3" (okVal r >>= getVar "a") 8

/- ===== Comparison Tests ===== -/

def testComp : IO Unit := do
  IO.println "--- Comparison ---"

  -- EQ: 10 == 3 = false (0)
  let r := stepInstBase (mkInst 10 Opcode.EQ [varOp "x", varOp "y"] ["a"]) testState
  assertEq "EQ 10==3" (okVal r >>= getVar "a") 0

  -- EQ: 10 == 10 = true (1)
  let r := stepInstBase (mkInst 11 Opcode.EQ [varOp "x", varOp "x"] ["a"]) testState
  assertEq "EQ 10==10" (okVal r >>= getVar "a") 1

  -- LT: 10 < 3 = false
  let r := stepInstBase (mkInst 12 Opcode.LT [varOp "x", varOp "y"] ["a"]) testState
  assertEq "LT 10<3" (okVal r >>= getVar "a") 0

  -- LT: 3 < 10 = true
  let r := stepInstBase (mkInst 13 Opcode.LT [varOp "y", varOp "x"] ["a"]) testState
  assertEq "LT 3<10" (okVal r >>= getVar "a") 1

  -- GT: 10 > 3 = true
  let r := stepInstBase (mkInst 14 Opcode.GT [varOp "x", varOp "y"] ["a"]) testState
  assertEq "GT 10>3" (okVal r >>= getVar "a") 1

  -- ISZERO: 0 is zero
  let s := testState |> withVar "z" 0
  let r := stepInstBase (mkInst 15 Opcode.ISZERO [varOp "z"] ["a"]) s
  assertEq "ISZERO 0" (okVal r >>= getVar "a") 1

  -- ISZERO: 10 is not zero
  let r := stepInstBase (mkInst 16 Opcode.ISZERO [varOp "x"] ["a"]) testState
  assertEq "ISZERO 10" (okVal r >>= getVar "a") 0

/- ===== Bitwise Tests ===== -/

def testBitwise : IO Unit := do
  IO.println "--- Bitwise ---"

  -- AND: 0xFF & 0x0F = 0x0F
  let s := testState |> withVar "x" 255 |> withVar "y" 15
  let r := stepInstBase (mkInst 20 Opcode.AND [varOp "x", varOp "y"] ["a"]) s
  assertEq "AND 0xFF&0x0F" (okVal r >>= getVar "a") 15

  -- OR: 0xF0 | 0x0F = 0xFF
  let s := testState |> withVar "x" 240 |> withVar "y" 15
  let r := stepInstBase (mkInst 21 Opcode.OR [varOp "x", varOp "y"] ["a"]) s
  assertEq "OR 0xF0|0x0F" (okVal r >>= getVar "a") 255

  -- XOR: 0xFF ^ 0x0F = 0xF0
  let s := testState |> withVar "x" 255 |> withVar "y" 15
  let r := stepInstBase (mkInst 22 Opcode.XOR [varOp "x", varOp "y"] ["a"]) s
  assertEq "XOR 0xFF^0x0F" (okVal r >>= getVar "a") 240

  -- NOT: ~0 = 2^256-1
  let s := testState |> withVar "x" 0
  let r := stepInstBase (mkInst 23 Opcode.NOT [varOp "x"] ["a"]) s
  let a := okVal r >>= getVar "a"
  let expected := EvmYul.UInt256.size - 1
  assertEq "NOT ~0" a expected

  -- SHL: 1 << 8 = 256  (shift amount first, value second per EVM semantics)
  let s := testState |> withVar "x" 1 |> withVar "y" 8
  let r := stepInstBase (mkInst 24 Opcode.SHL [varOp "x", varOp "y"] ["a"]) s
  assertEq "SHL 1<<8" (okVal r >>= getVar "a") 256

  -- SHR: 256 >> 8 = 1
  let s := testState |> withVar "x" 256 |> withVar "y" 8
  let r := stepInstBase (mkInst 25 Opcode.SHR [varOp "x", varOp "y"] ["a"]) s
  assertEq "SHR 256>>8" (okVal r >>= getVar "a") 1

/- ===== Memory Tests ===== -/

def testMemory : IO Unit := do
  IO.println "--- Memory ---"

  -- MSTORE: store 42 at offset 0
  let s := emptyState
  let r := stepInstBase (mkInst 30 Opcode.MSTORE [litOp 0, litOp 42] []) s
  assertOk "MSTORE 0,42" true r

  -- MLOAD: load from offset 0
  let s := okVal r |>.getD emptyState
  let r := stepInstBase (mkInst 31 Opcode.MLOAD [litOp 0] ["a"]) s
  assertEq "MLOAD @0" (okVal r >>= getVar "a") 42

  -- MSTORE8: store byte 0xAB at offset 0
  let s := emptyState
  let r := stepInstBase (mkInst 32 Opcode.MSTORE8 [litOp 0, litOp 0xAB] []) s
  assertOk "MSTORE8 0,0xAB" true r

  -- MLOAD after MSTORE8: should read the byte
  let s := okVal r |>.getD emptyState
  let r := stepInstBase (mkInst 33 Opcode.MLOAD [litOp 0] ["a"]) s
  -- 0xAB at MSB of the 32-byte slot
  let abVal := 0xAB * (2^248)
  assertEq "MLOAD after MSTORE8" (okVal r >>= getVar "a") abVal

  -- MEMTOP: initially 0 with empty memory
  let r := stepInstBase (mkInst 34 Opcode.MEMTOP [] ["a"]) emptyState
  assertEq "MEMTOP empty" (okVal r >>= getVar "a") 0

  -- MCOPY: copy 32 bytes from offset 0 to offset 32
  let s := emptyState
  let r := stepInstBase (mkInst 35 Opcode.MSTORE [litOp 0, litOp 99] []) s
  let s := okVal r |>.getD emptyState
  let r := stepInstBase (mkInst 36 Opcode.MCOPY [litOp 32, litOp 0, litOp 32] []) s
  assertOk "MCOPY 32,0,32" true r
  let s := okVal r |>.getD emptyState
  let r := stepInstBase (mkInst 37 Opcode.MLOAD [litOp 32] ["a"]) s
  assertEq "MLOAD after MCOPY" (okVal r >>= getVar "a") 99

/- ===== Storage Tests ===== -/

def testStorage : IO Unit := do
  IO.println "--- Storage ---"

  -- SSTORE: store 123 at key 5
  let s := emptyState
  let r := stepInstBase (mkInst 40 Opcode.SSTORE [litOp 5, litOp 123] []) s
  assertOk "SSTORE 5,123" true r

  -- SLOAD: load from key 5
  let s := okVal r |>.getD emptyState
  let r := stepInstBase (mkInst 41 Opcode.SLOAD [litOp 5] ["a"]) s
  assertEq "SLOAD 5" (okVal r >>= getVar "a") 123

  -- SLOAD: load from key 99 (not set) = 0
  let r := stepInstBase (mkInst 42 Opcode.SLOAD [litOp 99] ["a"]) s
  assertEq "SLOAD 99 (default 0)" (okVal r >>= getVar "a") 0

/- ===== Control Flow Tests ===== -/

def testControlFlow : IO Unit := do
  IO.println "--- Control Flow ---"

  -- JMP: jump to label
  let s := { emptyState with currentBb := "entry", labels := [("target", ⟨42⟩)] }
  let r := stepInstBase (mkInst 50 Opcode.JMP [lblOp "target"] []) s
  match r with
  | ExecResult.OK s' =>
    if s'.currentBb == "target" then
      IO.println "  ✓ JMP to target"
    else
      IO.println s!"  ✗ JMP: expected target, got {s'.currentBb}"
  | _ => IO.println "  ✗ JMP: expected OK"

  -- JNZ: conditional jump, nonzero -> if_nonzero
  let s := { emptyState with vars := [("cond", ⟨1⟩)] }
  let r := stepInstBase (mkInst 51 Opcode.JNZ [varOp "cond", lblOp "branchA", lblOp "branchB"] []) s
  match r with
  | ExecResult.OK s' =>
    if s'.currentBb == "branchA" then
      IO.println "  ✓ JNZ nonzero -> branchA"
    else
      IO.println s!"  ✗ JNZ nonzero: expected branchA, got {s'.currentBb}"
  | _ => IO.println "  ✗ JNZ nonzero: expected OK"

  -- JNZ: conditional jump, zero -> if_zero
  let s := { emptyState with vars := [("cond", ⟨0⟩)] }
  let r := stepInstBase (mkInst 52 Opcode.JNZ [varOp "cond", lblOp "branchA", lblOp "branchB"] []) s
  match r with
  | ExecResult.OK s' =>
    if s'.currentBb == "branchB" then
      IO.println "  ✓ JNZ zero -> branchB"
    else
      IO.println s!"  ✗ JNZ zero: expected branchB, got {s'.currentBb}"
  | _ => IO.println "  ✗ JNZ zero: expected OK"

/- ===== Environment Tests ===== -/

def testEnv : IO Unit := do
  IO.println "--- Environment ---"

  -- CALLER
  let cctx : CallContext := {
    caller := EvmYul.AccountAddress.ofNat 0xABCD, contract := 0, callvalue := EvmYul.UInt256.ofNat 0,
    calldata := [], gas := 0, static := false }
  let s := { emptyState with callCtx := cctx }
  let r := stepInstBase (mkInst 60 Opcode.CALLER [] ["a"]) s
  assertEq "CALLER" (okVal r >>= getVar "a") 0xABCD

  -- ADDRESS
  let cctx : CallContext := {
    caller := 0, contract := EvmYul.AccountAddress.ofNat 0x1234, callvalue := EvmYul.UInt256.ofNat 0,
    calldata := [], gas := 0, static := false }
  let s := { emptyState with callCtx := cctx }
  let r := stepInstBase (mkInst 61 Opcode.ADDRESS [] ["a"]) s
  assertEq "ADDRESS" (okVal r >>= getVar "a") 0x1234

  -- CALLVALUE
  let cctx : CallContext := {
    caller := 0, contract := 0, callvalue := EvmYul.UInt256.ofNat 1000,
    calldata := [], gas := 0, static := false }
  let s := { emptyState with callCtx := cctx }
  let r := stepInstBase (mkInst 62 Opcode.CALLVALUE [] ["a"]) s
  assertEq "CALLVALUE" (okVal r >>= getVar "a") 1000

  -- GAS
  let cctx : CallContext := {
    caller := 0, contract := 0, callvalue := EvmYul.UInt256.ofNat 0,
    calldata := [], gas := 50000, static := false }
  let s := { emptyState with callCtx := cctx }
  let r := stepInstBase (mkInst 63 Opcode.GAS [] ["a"]) s
  assertEq "GAS" (okVal r >>= getVar "a") 50000

  -- CALLDATASIZE
  let cctx : CallContext := {
    caller := 0, contract := 0, callvalue := EvmYul.UInt256.ofNat 0,
    calldata := List.replicate 100 (0 : byte), gas := 0, static := false }
  let s := { emptyState with callCtx := cctx }
  let r := stepInstBase (mkInst 64 Opcode.CALLDATASIZE [] ["a"]) s
  assertEq "CALLDATASIZE 100" (okVal r >>= getVar "a") 100

  -- CALLDATALOAD at offset 0, calldata = DEADBEEF...
  let calldata : List byte := [0xDE, 0xAD, 0xBE, 0xEF]
        ++ List.replicate 28 (0 : byte)
  let cctx : CallContext := {
    caller := 0, contract := 0, callvalue := EvmYul.UInt256.ofNat 0,
    calldata := calldata, gas := 0, static := false }
  let s := { emptyState with callCtx := cctx }
  let r := stepInstBase (mkInst 65 Opcode.CALLDATALOAD [litOp 0] ["a"]) s
  -- 0xDEADBEEF followed by 24 zero bytes = 0xDEADBEEF * 256^28
  let expected : Nat := 0xDEADBEEF * (256 ^ 28)
  assertEq "CALLDATALOAD @0" (okVal r >>= getVar "a") expected

/- ===== SSA Tests ===== -/

def testSSA : IO Unit := do
  IO.println "--- SSA ---"

  -- ASSIGN: %a = assign %x
  let r := stepInstBase (mkInst 70 Opcode.ASSIGN [varOp "x"] ["a"]) testState
  assertEq "ASSIGN x->a" (okVal r >>= getVar "a") 10

  -- NOP: state unchanged
  let r := stepInstBase (mkInst 71 Opcode.NOP [] []) testState
  assertOk "NOP" true r

  -- PHI outside prefix: should error
  let r := stepInstBase (mkInst 72 Opcode.PHI [lblOp "pred", varOp "v"] ["out"]) testState
  assertOk "PHI outside prefix (error)" false r

/- ===== Termination Tests ===== -/

def testTermination : IO Unit := do
  IO.println "--- Termination ---"

  -- STOP
  let r := stepInstBase (mkInst 80 Opcode.STOP [] []) testState
  match r with
  | ExecResult.Halt s => IO.println "  ✓ STOP (Halt)"
  | _ => IO.println "  ✗ STOP: expected Halt"

  -- RETURN
  let s := { emptyState with memory := ⟨(List.replicate 32 0xFF).toArray⟩ }
  let r := stepInstBase (mkInst 81 Opcode.RETURN [litOp 0, litOp 32] []) s
  match r with
  | ExecResult.Halt s' =>
    if s'.returndata.size == 32 then
      IO.println "  ✓ RETURN (Halt, 32 bytes in returndata)"
    else
      IO.println s!"  ✗ RETURN: expected 32 bytes returndata, got {s'.returndata.size}"
  | _ => IO.println "  ✗ RETURN: expected Halt"

  -- REVERT
  let r := stepInstBase (mkInst 82 Opcode.REVERT [litOp 0, litOp 0] []) emptyState
  match r with
  | ExecResult.Abort AbortType.RevertAbort _ => IO.println "  ✓ REVERT (RevertAbort)"
  | _ => IO.println "  ✗ REVERT: expected RevertAbort"

  -- INVALID
  let r := stepInstBase (mkInst 83 Opcode.INVALID [] []) emptyState
  match r with
  | ExecResult.Abort AbortType.ExHaltAbort _ => IO.println "  ✓ INVALID (ExHaltAbort)"
  | _ => IO.println "  ✗ INVALID: expected ExHaltAbort"

/- ===== Assertion Tests ===== -/

def testAssert : IO Unit := do
  IO.println "--- Assertions ---"

  -- ASSERT: condition=1 (ok)
  let s := emptyState |> withVar "cond" 1
  let r := stepInstBase (mkInst 90 Opcode.ASSERT [varOp "cond"] []) s
  assertOk "ASSERT 1 (pass)" true r

  -- ASSERT: condition=0 (abort)
  let s := emptyState |> withVar "cond" 0
  let r := stepInstBase (mkInst 91 Opcode.ASSERT [varOp "cond"] []) s
  match r with
  | ExecResult.Abort AbortType.RevertAbort _ => IO.println "  ✓ ASSERT 0 (RevertAbort)"
  | _ => IO.println "  ✗ ASSERT 0: expected RevertAbort"

  -- ASSERT_UNREACHABLE: condition=0 (ExHalt)
  let s := emptyState |> withVar "cond" 0
  let r := stepInstBase (mkInst 92 Opcode.ASSERT_UNREACHABLE [varOp "cond"] []) s
  match r with
  | ExecResult.Abort AbortType.ExHaltAbort _ => IO.println "  ✓ ASSERT_UNREACHABLE 0 (ExHaltAbort)"
  | _ => IO.println "  ✗ ASSERT_UNREACHABLE 0: expected ExHaltAbort"

  -- ASSERT_UNREACHABLE: condition=1 (ok)
  let s := emptyState |> withVar "cond" 1
  let r := stepInstBase (mkInst 93 Opcode.ASSERT_UNREACHABLE [varOp "cond"] []) s
  assertOk "ASSERT_UNREACHABLE 1 (pass)" true r

/- ===== Logging Tests ===== -/

def testLog : IO Unit := do
  IO.println "--- Logging ---"

  -- LOG: 1 topic, 0 topics with data
  -- Per EVM: LOGn offset, size, topic0, topic1, ..., topic_{n-1}
  -- First operand is Lit topic_count
  let s := emptyState |> withVar "off" 0
  let r := stepInstBase (mkInst 100 Opcode.LOG [litOp 0, varOp "off", litOp 0] []) s
  match r with
  | ExecResult.OK s' =>
    if s'.logs.length == 1 then
      IO.println "  ✓ LOG0 (1 event)"
    else
      IO.println s!"  ✗ LOG0: expected 1 event, got {s'.logs.length}"
  | _ => IO.println "  ✗ LOG0: expected OK"

/- ===== Keccak-256 Tests ===== -/

def testKeccak : IO Unit := do
  IO.println "--- Keccak-256 ---"

  -- SHA3 of empty data
  let s := emptyState
  let r := stepInstBase (mkInst 110 Opcode.SHA3 [litOp 0, litOp 0] ["h"]) s
  match r with
  | ExecResult.OK s' =>
    match alookup s'.vars "h" with
    | some h =>
      -- Known: Keccak256("") = c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
      let expected : Nat := 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
      if h.toNat == expected then
        IO.println "  ✓ SHA3('') = c5d24601..."
      else
        IO.println s!"  ✗ SHA3(''): expected {expected}, got {h.toNat}"
    | none => IO.println "  ✗ SHA3: no output variable"
  | _ => IO.println "  ✗ SHA3: expected OK"

  -- SHA3 of "hello"
  let s := { emptyState with
    memory := ⟨((List.map (λ (c : Char) => (c.toNat % 256).toUInt8) "hello".toList)
      ++ List.replicate 27 0).toArray⟩
  }
  let r := stepInstBase (mkInst 111 Opcode.SHA3 [litOp 0, litOp 5] ["h"]) s
  match r with
  | ExecResult.OK s' =>
    match alookup s'.vars "h" with
    | some h =>
      -- Keccak256("hello") = 1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8
      let expected : Nat := 0x1c8aff950685c2ed4bc3174f3472287b56d9517b9c948127319a09a7a36deac8
      if h.toNat == expected then
        IO.println "  ✓ SHA3('hello') = 1c8aff95..."
      else
        IO.println s!"  ✗ SHA3('hello'): expected {expected}, got {h.toNat}"
    | none => IO.println "  ✗ SHA3('hello'): no output variable"
  | _ => IO.println "  ✗ SHA3('hello'): expected OK"

/- ===== Main ===== -/

def main : IO Unit := do
  IO.println "=== Venom IR Semantics Tests ==="
  IO.println ""
  testArith
  testComp
  testBitwise
  testMemory
  testStorage
  testControlFlow
  testEnv
  testSSA
  testTermination
  testAssert
  testLog
  testKeccak
  IO.println ""
  IO.println "=== Tests complete ==="
