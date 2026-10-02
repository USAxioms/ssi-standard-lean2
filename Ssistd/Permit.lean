/-!
# Permit predicate (§13), verification outcomes (§14), fail-closed decision (§23)

Permit(q,u) ⟺ TypeOK ∧ ActionWellTyped ∧ CSLValid ∧ Authorized ∧ CapabilityValid
  ∧ SafetyInv ∧ ActionSafe ∧ EvidenceValid ∧ DeploymentBound ∧ Current ∧ ¬Revoked
  ∧ WithinScope ∧ Fresh
-/
namespace SsiStd

/-- The thirteen conditions of the Permit predicate. -/
structure PermitConditions where
  typeOK          : Bool
  actionWellTyped : Bool
  cslValid        : Bool
  authorized      : Bool
  capabilityValid : Bool
  safetyInv       : Bool
  actionSafe      : Bool
  evidenceValid   : Bool
  deploymentBound : Bool
  current         : Bool
  revoked         : Bool
  withinScope     : Bool
  fresh           : Bool
  deriving DecidableEq, Repr

/-- §13: Permit(q, u). -/
def permit (c : PermitConditions) : Bool :=
  c.typeOK && c.actionWellTyped && c.cslValid && c.authorized && c.capabilityValid &&
  c.safetyInv && c.actionSafe && c.evidenceValid && c.deploymentBound && c.current &&
  !c.revoked && c.withinScope && c.fresh

theorem revoked_no_permit (c : PermitConditions) (h : c.revoked = true) : permit c = false := by
  simp [permit, h]

theorem unauthorized_no_permit (c : PermitConditions) (h : c.authorized = false) : permit c = false := by
  simp [permit, h]

theorem unsafe_action_no_permit (c : PermitConditions) (h : c.actionSafe = false) : permit c = false := by
  simp [permit, h]

theorem invariant_failure_no_permit (c : PermitConditions) (h : c.safetyInv = false) : permit c = false := by
  simp [permit, h]

theorem invalid_evidence_no_permit (c : PermitConditions) (h : c.evidenceValid = false) : permit c = false := by
  simp [permit, h]

theorem unbound_deployment_no_permit (c : PermitConditions) (h : c.deploymentBound = false) :
    permit c = false := by
  simp [permit, h]

theorem stale_no_permit (c : PermitConditions) (h : c.fresh = false) : permit c = false := by
  simp [permit, h]

theorem out_of_scope_no_permit (c : PermitConditions) (h : c.withinScope = false) : permit c = false := by
  simp [permit, h]

theorem ill_typed_no_permit (c : PermitConditions) (h : c.actionWellTyped = false) : permit c = false := by
  simp [permit, h]

theorem invalid_csl_no_permit (c : PermitConditions) (h : c.cslValid = false) : permit c = false := by
  simp [permit, h]

theorem no_capability_no_permit (c : PermitConditions) (h : c.capabilityValid = false) :
    permit c = false := by
  simp [permit, h]

/-- §14: verification outcomes. -/
inductive VerResult where
  | pass
  | fail
  | unknown
  deriving DecidableEq, Repr

/-- §14: UNKNOWN ≠ PASS. -/
theorem unknown_ne_pass : VerResult.unknown ≠ VerResult.pass := by decide

/-- §13, §23, §24: the decision taken for a proposed action. -/
inductive Decision where
  | execute
  | reject
  | defer
  | safeStop
  deriving DecidableEq, Repr

/-- Invalid arithmetic stops safely; unknown verification defers; failed verification or a
failed Permit rejects; only PASS with Permit executes. -/
def decideAction (arithmeticValid : Bool) (v : VerResult) (c : PermitConditions) : Decision :=
  match arithmeticValid, v, permit c with
  | false, _, _ => .safeStop
  | true, .unknown, _ => .defer
  | true, .fail, _ => .reject
  | true, .pass, false => .reject
  | true, .pass, true => .execute

/-- §23: no verified permission, no consequential execution. -/
theorem execute_requires_permit (a : Bool) (v : VerResult) (c : PermitConditions)
    (h : decideAction a v c = .execute) : permit c = true ∧ v = .pass ∧ a = true := by
  unfold decideAction at h
  cases a <;> cases v <;> cases hp : permit c <;> simp_all

/-- §14: an UNKNOWN verification never executes. -/
theorem unknown_never_executes (a : Bool) (c : PermitConditions) : decideAction a .unknown c ≠ .execute := by
  unfold decideAction
  cases a <;> cases permit c <;> decide

/-- §14: a FAILED verification never executes. -/
theorem fail_never_executes (a : Bool) (c : PermitConditions) : decideAction a .fail c ≠ .execute := by
  unfold decideAction
  cases a <;> cases permit c <;> decide

/-- §7: invalid arithmetic results in safe stop, not implicit continuation. -/
theorem invalid_arithmetic_safe_stop (v : VerResult) (c : PermitConditions) :
    decideAction false v c = .safeStop := by
  unfold decideAction
  cases v <;> cases permit c <;> rfl

end SsiStd
