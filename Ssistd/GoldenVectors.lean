import SsiStd.Wad
import SsiStd.Permit
import SsiStd.Mediation
import SsiStd.Governance
import SsiStd.Preservation
import SsiStd.Asset

/-!
# Golden vectors

Concrete cases checked by the Lean kernel with `decide`.
-/
namespace SsiStd

/-- Every Permit condition satisfied. -/
def allGood : PermitConditions :=
  ⟨true, true, true, true, true, true, true, true, true, true, false, true, true⟩

-- §13 Permit
example : permit allGood = true := by decide
example : permit { allGood with revoked := true } = false := by decide
example : permit { allGood with fresh := false } = false := by decide
example : permit { allGood with deploymentBound := false } = false := by decide
example : permit { allGood with authorized := false } = false := by decide

-- §14, §23 decisions
example : decideAction true .pass allGood = .execute := by decide
example : decideAction true .unknown allGood = .defer := by decide
example : decideAction true .fail allGood = .reject := by decide
example : decideAction true .pass { allGood with withinScope := false } = .reject := by decide
example : decideAction false .pass allGood = .safeStop := by decide

-- §8, §9 mediation and typing
example : mediate ⟨"send report", some .communicate⟩ allGood = some ⟨.communicate, true⟩ := by decide
example : mediate ⟨"unclassified action", none⟩ allGood = none := by decide
example : mediate ⟨"self-modify weights", some .selfModify⟩ { allGood with authorized := false } = none := by decide

-- §10 directives: issued at 10, expires at 100, revocation epoch 3
example : directiveValid ⟨true, 10, 100, 3, true⟩ 50 3 = true := by decide
example : directiveValid ⟨true, 10, 100, 3, true⟩ 101 3 = false := by decide   -- expired
example : directiveValid ⟨true, 10, 100, 3, true⟩ 50 4 = false := by decide    -- revoked by epoch
example : directiveValid ⟨true, 10, 100, 3, true⟩ 5 3 = false := by decide     -- not yet issued
example : directiveValid ⟨false, 10, 100, 3, true⟩ 50 3 = false := by decide   -- bad signature

-- §17 capability non-escalation
example : capabilityTransitionOk [1, 2] [1, 2, 3] false = true := by decide
example : capabilityTransitionOk [1, 4] [1, 2, 3] false = false := by decide
example : capabilityTransitionOk [1, 4] [1, 2, 3] true = true := by decide

-- §16 deployment binding
example : certifies ⟨"deployment-A", true⟩ "deployment-A" = true := by decide
example : certifies ⟨"deployment-A", true⟩ "deployment-B" = false := by decide

-- §18 adoption
example : adopt ⟨true, true, true, true, true, true⟩ = true := by decide
example : adopt ⟨true, true, true, true, false, true⟩ = false := by decide

-- §21–§22 Safety Asset
example : sacActive ⟨true, true, true, true, .active⟩ = true := by decide
example : sacActive ⟨true, true, true, true, .revalidation⟩ = false := by decide
example : canTransition .active .revoked = true := by decide
example : canTransition .revoked .active = false := by decide

-- §7 WAD-18
example : divRaw 1000000000000000000 0 = .err .divByZero := by decide

end SsiStd
