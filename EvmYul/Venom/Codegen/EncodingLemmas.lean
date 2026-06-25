/-
Encoding Lemmas — encodeNumBytes roundtrip for spill/restore
-/

import EvmYul.Venom.Types
import EvmYul.Venom.Semantics
import EvmYul.Venom.Codegen.PlanExec
open EvmYul.Venom

namespace EvmYul.Venom.Codegen

lemma fromBytesBigEndian_encodeNumBytes (n : Nat) :
    fromBytesBigEndian (encodeNumBytes n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold encodeNumBytes
    by_cases hn0 : n = 0
    · subst hn0; rfl
    · rw [if_neg hn0]
      have h_lt : n / 256 < n := by
        apply Nat.div_lt_self <;> omega
      have h_IH : fromBytesBigEndian (encodeNumBytes (n / 256)) = n / 256 := ih (n / 256) h_lt
      unfold fromBytesBigEndian
      simp
      -- fromBytes' (b :: bs) = b.toFin.val + 2^8 * fromBytes' bs (definitional)
      have h_def : fromBytes' (UInt8.ofNat (n % 256) :: List.reverse (encodeNumBytes (n / 256))) =
        (UInt8.ofNat (n % 256)).toFin.val + 2^8 * fromBytes' (List.reverse (encodeNumBytes (n / 256))) := rfl
      have h_rev : fromBytes' (List.reverse (encodeNumBytes (n / 256))) = n / 256 := by
        calc
          fromBytes' (List.reverse (encodeNumBytes (n / 256))) = fromBytesBigEndian (encodeNumBytes (n / 256)) := rfl
          _ = n / 256 := h_IH
      have h_byte_val : (UInt8.ofNat (n % 256)).toFin.val = n % 256 := by simp
      calc
        fromBytes' (UInt8.ofNat (n % 256) :: List.reverse (encodeNumBytes (n / 256)))
            = (UInt8.ofNat (n % 256)).toFin.val + 2^8 * fromBytes' (List.reverse (encodeNumBytes (n / 256))) := h_def
        _ = (UInt8.ofNat (n % 256)).toFin.val + 2^8 * (n / 256) := by rw [h_rev]
        _ = n % 256 + 2^8 * (n / 256) := by rw [h_byte_val]
        _ = n % 256 + 256 * (n / 256) := by norm_num
        _ = n := by omega


lemma fromBytes'_encodeNumBytes_padded (n k : Nat) :
    fromBytes' ((encodeNumBytes n).reverse ++ List.replicate k 0) = n := by
  calc
    fromBytes' ((encodeNumBytes n).reverse ++ List.replicate k 0)
        = fromBytesBigEndian (encodeNumBytes n) := by
          unfold fromBytesBigEndian; simp
    _ = n := fromBytesBigEndian_encodeNumBytes n

lemma fromBytesBigEndian_encodeNumBytes_padded (off k : Nat) :
    fromBytesBigEndian (List.replicate k 0 ++ encodeNumBytes off) = off := by
  unfold fromBytesBigEndian
  simp [List.reverse_append]
  simpa using fromBytes'_encodeNumBytes_padded off k

lemma asmPushVal_encodeNumBytes_toNat (off : Nat) (hoff : off < 2 ^ 256) :
    (wordOfBytes (List.toByteArray
      (List.replicate (32 - (encodeNumBytes off).length) (0 : byte) ++ encodeNumBytes off))).toNat = off := by
  -- Deferred: needs (List.toByteArray xs).toList = xs lemma
  sorry
