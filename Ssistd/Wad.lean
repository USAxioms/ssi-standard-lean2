/-!
# WAD-18 deterministic fixed-point arithmetic

Every normative quantity is an integer `n` representing `n / 10^18`.
Floating point is never used. Non-exact results, division by zero,
excess precision, unit mismatch, and overflow are rejected explicitly
rather than rounded.
-/
namespace SsiStd

/-- Scale factor Q = 10^18. -/
def Q : Int := 1000000000000000000

/-- Declared arithmetic bound: |n| ≤ 2^255 - 1 (int256). -/
def bound : Int := 57896044618658097711785492504343953926634992332820282019728792003956564819967

/-- Reasons a WAD-18 operation is refused. -/
inductive WadError where
  | overflow
  | divByZero
  | nonExact
  | unitMismatch
  | excessPrecision
  deriving DecidableEq, Repr

/-- Result of a checked operation: a value, or an explicit refusal. -/
inductive Result (α : Type) where
  | ok : α → Result α
  | err : WadError → Result α
  deriving DecidableEq, Repr

/-- Admit a raw value only if it lies within the declared bound. -/
def checked (n : Int) : Result Int :=
  if -bound ≤ n ∧ n ≤ bound then .ok n else .err .overflow

/-- A quantity always carries an explicit unit. -/
structure Qty where
  unit : String
  raw  : Int
  deriving DecidableEq, Repr

/-- Encode `mantissa / 10^decimals`. More than 18 decimals is refused
(no declared quantization is applied). -/
def encode (mantissa : Int) (decimals : Nat) : Result Int :=
  if decimals > 18 then .err .excessPrecision
  else checked (mantissa * Int.ofNat (10 ^ (18 - decimals)))

/-- Same-unit addition. Different units are never combined implicitly. -/
def add (a b : Qty) : Result Qty :=
  if a.unit = b.unit then
    match checked (a.raw + b.raw) with
    | .ok r => .ok ⟨a.unit, r⟩
    | .err e => .err e
  else .err .unitMismatch

/-- Same-unit subtraction. -/
def sub (a b : Qty) : Result Qty :=
  if a.unit = b.unit then
    match checked (a.raw - b.raw) with
    | .ok r => .ok ⟨a.unit, r⟩
    | .err e => .err e
  else .err .unitMismatch

/-- mul_Q(a, b) = a*b / Q, admitted only when a*b is divisible by Q. -/
def mulRaw (a b : Int) : Result Int :=
  if (a * b) % Q ≠ 0 then .err .nonExact
  else checked ((a * b) / Q)

/-- div_Q(a, b) = a*Q / b, with b ≠ 0 and an exact result required. -/
def divRaw (a b : Int) : Result Int :=
  if b = 0 then .err .divByZero
  else if (a * Q) % b ≠ 0 then .err .nonExact
  else checked ((a * Q) / b)

/-! ## Guarantees -/

theorem div_by_zero_rejected (a : Int) : divRaw a 0 = .err .divByZero := by
  unfold divRaw
  rw [if_pos rfl]

theorem mul_nonexact_rejected (a b : Int) (h : (a * b) % Q ≠ 0) :
    mulRaw a b = .err .nonExact := by
  unfold mulRaw
  rw [if_pos h]

theorem excess_precision_rejected (m : Int) (d : Nat) (h : d > 18) :
    encode m d = .err .excessPrecision := by
  unfold encode
  rw [if_pos h]

theorem add_unit_mismatch_rejected (a b : Qty) (h : a.unit ≠ b.unit) :
    add a b = .err .unitMismatch := by
  unfold add
  rw [if_neg h]

theorem sub_unit_mismatch_rejected (a b : Qty) (h : a.unit ≠ b.unit) :
    sub a b = .err .unitMismatch := by
  unfold sub
  rw [if_neg h]

theorem checked_out_of_bound (n : Int) (h : bound < n) : checked n = .err .overflow := by
  unfold checked
  have : ¬(-bound ≤ n ∧ n ≤ bound) := fun ⟨_, h2⟩ => absurd h2 (Int.not_le.mpr h)
  rw [if_neg this]

end SsiStd
