/-!
# Safety Asset Class (§21) and lifecycle (§22)
-/
namespace SsiStd

inductive Status where
  | proposed | verified | active | revalidation | revoked | rejected
  deriving DecidableEq, Repr

/-- §22: the permitted lifecycle transitions. -/
def canTransition : Status → Status → Bool
  | .proposed, .verified => true
  | .proposed, .rejected => true
  | .verified, .active => true
  | .active, .revalidation => true
  | .revalidation, .active => true
  | .revalidation, .revoked => true
  | .active, .revoked => true
  | _, _ => false

/-- A revoked asset never becomes active again. -/
theorem revoked_is_terminal (s : Status) : canTransition .revoked s = false := by
  cases s <;> rfl

/-- A rejected proposal never proceeds. -/
theorem rejected_is_terminal (s : Status) : canTransition .rejected s = false := by
  cases s <;> rfl

/-- Nothing becomes active without first being verified. -/
theorem proposed_cannot_activate : canTransition .proposed .active = false := rfl

/-- §21: SAC(SA) ⟺ SSI ∧ ProvenanceValid ∧ ScopeValid ∧ Fresh ∧ Status = ACTIVE. -/
structure SafetyAsset where
  ssi             : Bool
  provenanceValid : Bool
  scopeValid      : Bool
  fresh           : Bool
  status          : Status
  deriving DecidableEq, Repr

def sacActive (sa : SafetyAsset) : Bool :=
  sa.ssi && sa.provenanceValid && sa.scopeValid && sa.fresh && sa.status == .active

theorem not_active_status_not_sac (sa : SafetyAsset) (h : sa.status ≠ .active) : sacActive sa = false := by
  simp [sacActive, h]

theorem stale_asset_not_sac (sa : SafetyAsset) (h : sa.fresh = false) : sacActive sa = false := by
  simp [sacActive, h]

end SsiStd
