/-!
# Formal safety preservation (§25), fixed point ≠ safety (§19), R³ adoption (§18)
-/
namespace SsiStd

/-- States reachable from q₀ through permitted transitions. -/
inductive Reachable {σ α : Type} (q0 : σ) (permit : σ → α → Prop) (next : σ → α → σ) : σ → Prop where
  | start : Reachable q0 permit next q0
  | step {q : σ} {u : α} : Reachable q0 permit next q → permit q u → Reachable q0 permit next (next q u)

/-- §25: if q₀ ⊨ C and every permitted transition preserves C, every reachable state satisfies C. -/
theorem every_reachable_state_safe {σ α : Type} (models : σ → Prop) (permit : σ → α → Prop)
    (next : σ → α → σ) (q0 : σ) (h0 : models q0)
    (pres : ∀ q u, models q → permit q u → models (next q u)) :
    ∀ q, Reachable q0 permit next q → models q := by
  intro q hr
  induction hr with
  | start => exact h0
  | step _ hp ih => exact pres _ _ ih hp

/-- §19: refinement convergence does not establish safety. There is a fixed point that is not safe. -/
theorem fixed_point_not_safety : ∃ (f : Nat → Nat) (safe : Nat → Bool) (x : Nat), f x = x ∧ safe x = false :=
  ⟨id, fun _ => false, 0, rfl, rfl⟩

/-- §18: q = (K, M, G, E). A refiner sees only M, G and E, so the kernel is preserved by construction. -/
structure GovSystem (K M G E : Type) where
  k : K
  m : M
  g : G
  e : E

structure Refiner (M G E : Type) where
  rm : M → M
  rg : G → G
  re : E → E

def Refiner.apply {K M G E : Type} (r : Refiner M G E) (q : GovSystem K M G E) : GovSystem K M G E :=
  { k := q.k, m := r.rm q.m, g := r.rg q.g, e := r.re q.e }

theorem kernel_equal {K M G E : Type} (r : Refiner M G E) (q : GovSystem K M G E) :
    (r.apply q).k = q.k := rfl

/-- §18: the six-part adoption predicate. -/
structure AdoptChecks where
  kernelEqual                : Bool
  safetyProofValid           : Bool
  authorizationValid         : Bool
  deploymentCertificateValid : Bool
  nonRegression              : Bool
  capabilityDisclosureValid  : Bool
  deriving DecidableEq, Repr

def adopt (a : AdoptChecks) : Bool :=
  a.kernelEqual && a.safetyProofValid && a.authorizationValid &&
  a.deploymentCertificateValid && a.nonRegression && a.capabilityDisclosureValid

theorem regression_not_adopted (a : AdoptChecks) (h : a.nonRegression = false) : adopt a = false := by
  simp [adopt, h]

theorem kernel_change_not_adopted (a : AdoptChecks) (h : a.kernelEqual = false) : adopt a = false := by
  simp [adopt, h]

end SsiStd
