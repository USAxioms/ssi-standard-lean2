# Safe Super Intelligence Standard v1.0 — Lean 4 Formalization

Lean 4 formalization of **Safe Super Intelligence: Definition, Architecture, and Verification Standard v1.0** by Michael Aaron Russell, Specification I of the Safe Super Intelligence specification family.

@dataset{safe_super_intelligence_standard_2026,
  title={Safe Super Intelligence: Definition, Architecture, and Verification Standard},
  DOI={10.5281/zenodo.23101683},
  publisher={Zenodo},
  year={2026}
}
> **Safe Super Intelligence** is an advanced intelligence architecture in which externally consequential actions are constrained by a formally specified, human-governed, machine-verifiable system of safety invariants, authorization, capability boundaries, provenance, and mediated execution.

$$SSI(q,u) \iff SI(q) \land VS(q) \land HG(q) \land AUTH(q,u) \land VER(q,u)$$

Pure Lean 4 core: no Mathlib, no external dependencies. Companion repository: the SSI Axiomatic System formalization (Specification II).

## Build

```bash
# install elan (Lean toolchain manager): https://github.com/leanprover/elan
lake build
```

The toolchain is pinned in `lean-toolchain` (`leanprover/lean4:v4.12.0`). Every push runs `.github/workflows/lean.yml`, which builds the project and checks every proof and golden vector.

## Build status

This repository was written without access to a Lean compiler. **It has not yet been compiled.** The first CI run on GitHub is the first check; if a proof fails, the log names the file and line. Until a CI run passes, treat these theorems as written, not verified.

## Modules

| File | Standard sections |
|---|---|
| `SsiStd/Permit.lean` | §7, §13, §14, §23: the 13-condition Permit predicate; PASS / FAIL / UNKNOWN; EXECUTE / REJECT / DEFER / SAFE_STOP |
| `SsiStd/Mediation.lean` | §3, §8, §9, §32: complete mediation, action typing, intelligence ≠ authority |
| `SsiStd/Governance.lean` | §10, §11, §15, §16, §17: directives, capability non-escalation, deployment binding, HashIntegrity ≠ Truth |
| `SsiStd/Preservation.lean` | §18, §19, §25: reachable-state safety, fixed point ≠ safety, (K, M, G, E) refinement and adoption |
| `SsiStd/Asset.lean` | §21, §22: Safety Asset Class and lifecycle |
| `SsiStd/Wad.lean` | §7: WAD-18 normative arithmetic with explicit failure |
| `SsiStd/GoldenVectors.lean` | 30 concrete cases checked by `decide` |

## Theorems and the standard

| Theorem | Statement |
|---|---|
| `revoked_no_permit`, `unauthorized_no_permit`, `unsafe_action_no_permit`, `invariant_failure_no_permit`, `invalid_evidence_no_permit`, `unbound_deployment_no_permit`, `stale_no_permit`, `out_of_scope_no_permit`, `ill_typed_no_permit`, `invalid_csl_no_permit`, `no_capability_no_permit` | §13: every Permit condition is necessary |
| `unknown_ne_pass` | §14: UNKNOWN ≠ PASS |
| `execute_requires_permit` | §23: no verified permission ⇒ no consequential execution |
| `unknown_never_executes`, `fail_never_executes` | §14: only PASS can lead to execution |
| `invalid_arithmetic_safe_stop` | §7: invalid arithmetic ⇒ safe stop |
| `effect_implies_permit`, `no_permit_no_effect` | §32: ExternalEffect ⇒ Permit; ¬Permit ⇒ ¬ExternalEffect |
| `untyped_no_effect` | §9: untyped actions receive no implicit permission |
| `capability_is_not_authority` | §3: Intelligence ≠ Authority |
| `expired_directive_invalid`, `revoked_epoch_invalid`, `unsigned_directive_invalid` | §10: directive validity |
| `escalation_without_governance_rejected` | §17: capability non-escalation |
| `certificate_does_not_transfer` | §16: deployment binding |
| `hash_integrity_ne_truth` | §15: HashIntegrity ≠ Truth |
| `every_reachable_state_safe` | §25: formal safety preservation |
| `fixed_point_not_safety` | §19: refinement convergence ≠ safety verification |
| `kernel_equal`, `regression_not_adopted`, `kernel_change_not_adopted` | §18: governed refinement |
| `revoked_is_terminal`, `rejected_is_terminal`, `proposed_cannot_activate` | §22: lifecycle |
| `not_active_status_not_sac`, `stale_asset_not_sac` | §21: Safety Asset Class |

## Scope

These proofs establish the architecture: that the Permit predicate, mediation boundary, governance checks, and lifecycle behave as the standard specifies for any state. They do not establish that any deployed system conforms, and, as §30 requires, conformance to this standard is never a claim of unrestricted or universal safety. Signatures, hashes, and the superintelligence criterion are modelled as declared Booleans; their cryptographic and empirical substance lies outside this formalization.

## Naming

This standard and repository are independent work by Michael Aaron Russell and are not affiliated with any company of a similar name.

Choose and add a license before publishing.
