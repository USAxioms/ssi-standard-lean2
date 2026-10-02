import SsiStd.Permit

/-!
# Complete mediation (§8), action typing (§9), intelligence ≠ authority (§3)

Model output is a `Proposal`. The only way to obtain an `Effect` is `mediate`, which
emits one exactly when the action is typed and Permit holds. There is no other
constructor path from a proposal to an external effect in this model.
-/
namespace SsiStd

/-- §9: action classes. -/
inductive ActionType where
  | read | compute | communicate | write | purchase
  | deploy | credential | physical | selfModify | policyChange
  deriving DecidableEq, Repr

/-- A model's output: a proposal, never a command (§8). `kind = none` means the action
could not be represented by the action type system. -/
structure Proposal where
  description : String
  kind        : Option ActionType
  deriving DecidableEq, Repr

/-- An external effect. Its fields record the authorization it was emitted under. -/
structure Effect where
  kind       : ActionType
  permitted  : Bool
  deriving DecidableEq, Repr

/-- §8: K → J → U_e. The mediated interface emits an effect only for a typed, permitted action. -/
def mediate (p : Proposal) (c : PermitConditions) : Option Effect :=
  match p.kind, permit c with
  | some k, true => some ⟨k, true⟩
  | _, _ => none

/-- §32: ExternalEffect ⇒ Permit. -/
theorem effect_implies_permit (p : Proposal) (c : PermitConditions) (e : Effect)
    (h : mediate p c = some e) : permit c = true := by
  unfold mediate at h
  cases hk : p.kind <;> cases hp : permit c <;> simp_all

/-- §32: ¬Permit ⇒ ¬ExternalEffect. -/
theorem no_permit_no_effect (p : Proposal) (c : PermitConditions) (h : permit c = false) :
    mediate p c = none := by
  unfold mediate
  rw [h]
  cases p.kind <;> rfl

/-- §9: an action that cannot be typed receives no implicit permission. -/
theorem untyped_no_effect (p : Proposal) (c : PermitConditions) (h : p.kind = none) :
    mediate p c = none := by
  unfold mediate
  rw [h] <;> rfl

/-- §3: Intelligence ≠ Authority. However capable the proposer, an unauthorized
action produces no effect. -/
theorem capability_is_not_authority (p : Proposal) (c : PermitConditions) (h : c.authorized = false) :
    mediate p c = none :=
  no_permit_no_effect p c (unauthorized_no_permit c h)

end SsiStd
