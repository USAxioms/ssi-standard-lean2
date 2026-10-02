/-!
# Human authorization (§10), CSL (§11), capability non-escalation (§17),
# deployment binding (§16), and HashIntegrity ≠ Truth (§15)
-/
namespace SsiStd

/-- §10: a signed governance directive (the fields the decision depends on). -/
structure Directive where
  signatureValid  : Bool
  issueTime       : Nat
  expiryTime      : Nat
  revocationEpoch : Nat
  inScope         : Bool
  deriving DecidableEq, Repr

/-- A directive is valid only if every authorization predicate holds at time `now`
under the current revocation epoch. -/
def directiveValid (d : Directive) (now currentEpoch : Nat) : Bool :=
  d.signatureValid && decide (d.issueTime ≤ now) && decide (now ≤ d.expiryTime) &&
  decide (currentEpoch ≤ d.revocationEpoch) && d.inScope

theorem expired_directive_invalid (d : Directive) (now e : Nat) (h : d.expiryTime < now) :
    directiveValid d now e = false := by
  unfold directiveValid
  rw [decide_eq_false (Nat.not_le.mpr h)]
  simp

theorem revoked_epoch_invalid (d : Directive) (now e : Nat) (h : d.revocationEpoch < e) :
    directiveValid d now e = false := by
  unfold directiveValid
  rw [decide_eq_false (Nat.not_le.mpr h)]
  simp

theorem unsigned_directive_invalid (d : Directive) (now e : Nat) (h : d.signatureValid = false) :
    directiveValid d now e = false := by
  simp [directiveValid, h]

/-! ## §17 Capability non-escalation -/

/-- Cap(q_{t+1}) ⊆ Cap_authorized(q_t), unless governance explicitly authorizes the change. -/
def subsetCaps (next authorized : List Nat) : Bool := next.all (fun c => authorized.contains c)

def capabilityTransitionOk (next authorized : List Nat) (governanceApproved : Bool) : Bool :=
  subsetCaps next authorized || governanceApproved

theorem escalation_without_governance_rejected (next authorized : List Nat)
    (h : subsetCaps next authorized = false) : capabilityTransitionOk next authorized false = false := by
  simp [capabilityTransitionOk, h]

/-! ## §16 Deployment binding -/

structure Certificate where
  deploymentId : String
  valid        : Bool
  deriving DecidableEq, Repr

def certifies (cert : Certificate) (deployment : String) : Bool :=
  cert.valid && cert.deploymentId == deployment

/-- A certificate for Deployment_A does not establish assurance for a different Deployment_B. -/
theorem certificate_does_not_transfer (cert : Certificate) (b : String) (h : (cert.deploymentId == b) = false) :
    certifies cert b = false := by
  simp [certifies, h]

/-! ## §15 HashIntegrity ≠ Truth -/

/-- An evidence record: its integrity can be checked; its truth is a separate fact. -/
structure EvidenceRecord where
  integrityOk    : Bool
  claimIsTrue    : Bool
  deriving DecidableEq, Repr

/-- There exist records whose integrity checks out while the represented claim is false. -/
theorem hash_integrity_ne_truth : ∃ r : EvidenceRecord, r.integrityOk = true ∧ r.claimIsTrue = false :=
  ⟨⟨true, false⟩, rfl, rfl⟩

end SsiStd
