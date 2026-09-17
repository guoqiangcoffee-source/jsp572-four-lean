# Verification report

Date: 2026-09-17 UTC. Target: `JSP572Four.jsp572_four_complete`.

The complete numerical theorem has passed source elaboration, the Lean kernel, an explicit axiom allowlist audit, and two independent checker implementations. This report records local evidence. It is not an organizer-issued verification record or an award decision.

The prize's current complete-original-problem intake excludes this standalone special-case scope. See `CURRENT-INTAKE.md`. This is a scope limitation, not a failed proof check.

## Reproducible environment

- Platform actually used: Windows x64, OS version 10.0.26100.0; PowerShell 7.6.5.
- Lean: `leanprover/lean4:v4.35.0-rc2`, commit `11acb17ec6b07a8f9e9173e6845197929540936b`.
- Toolchain distribution: [official Windows release](https://github.com/leanprover/lean4/releases/tag/v4.35.0-rc2).
- mathlib: commit `f61f3ed7633ff99ecaae4a086395b501652a76ee`.
- All nine third-party package revisions are pinned in the release `lake-manifest.json`.
- The release uses a normal Git requirement for mathlib. The development project used the same revision at a local path.

The release archive contains source, configuration, scripts, recorded logs, and a compressed dependency-closed proof export. It does not include the Lean installation or the third-party dependency build cache. `MANIFEST.sha256` checks every other packaged file; it is an integrity record, not a public timestamp or cryptographic signature.

## Checks actually performed

| Check | Result | Recorded evidence |
|---|---|---|
| Complete project build | Passed, 3,127 Lake jobs including dependencies | `verification/build.log` |
| Final theorem axiom audit | Passed; only `propext`, `Classical.choice`, `Quot.sound` | `verification/axioms.log`, `Audit.lean` |
| Lean kernel replay | `leanchecker JSP572Four.Main`, exit 0 | `verification/kernel-replay-status.log`; success output is empty |
| New-directory source rebuild | Passed with the release Git configuration and an initially empty project build directory | `verification/reproduction-build.log` |
| New-directory axiom audit | Passed | `verification/reproduction-axioms.log` |
| Independent lean4lean checker | Exit 0; 8,283 declarations checked | `verification/external-lean4lean.log`, corresponding status file |
| Independent nanoda checker | Exit 0; configured to reject unpermitted axioms | `verification/external-nanoda-config.json`, corresponding status file |
| Archived-export replay script | Both checkers accepted the decompressed export after its SHA-256 was checked | `verification/external-check-metadata.json` |

The new-directory rebuild reused only the pinned third-party source and official dependency cache. It rebuilt this project's proof modules from source. It was not a fresh machine, a clean-room dependency rebuild, or a different operating system. `leanchecker` reuses Lean's kernel implementation; lean4lean and nanoda provide the additional implementation diversity.

The exported declaration includes its entire proof dependency closure, including exactly the three permitted axioms. The 8,286 named declaration records include these three axioms; lean4lean reports 8,283 checked declarations. The export contains the final theorem, not merely helper lemmas or sample instances.

The raw export is 41,818,036 bytes, with SHA-256:

`5acb1064abb7f960ef933e9c4a77552762ac032217648ebae59c4b5c02c2d438`

Tool binary hashes, compressed-export hash, source hashes, commands, and checker results are in `verification/external-check-metadata.json`. The bundled checkers' separate source repository commits were not established and are not invented here.

## Reproduce the source proof

Install the pinned Lean toolchain and Git, then extract the release archive. From its project directory, fetch mathlib's official cache and run:

```text
lake exe cache get
lake build JSP572Four
lake env lean Audit.lean
```

The equivalent build-and-audit wrappers are `./verify.ps1` on Windows and `bash verify.sh` on systems with Bash. The Bash wrapper and a fresh network-only dependency download were not tested in this Windows run. Retain the supplied `lake-manifest.json`; do not update dependencies to a newer revision when reproducing this result.

For additional Lean kernel replay with the bundled tools:

```text
lake env leanchecker JSP572Four.Main
```

## Reproduce the independent checks

With the pinned Windows toolchain, the archived export can be checked without first compiling this project:

```powershell
./verification/external-check.ps1 -FromArchive -LeanBin 'C:/path/to/lean-4.35.0-rc2-windows/bin'
```

To regenerate the export from a built project, omit `-FromArchive`. See `verification/external-check-summary.md` for the exact exporter and checker commands. The text-export route was tested; direct loading of this release's `.olean` files into lean4lean was not used for the successful check.

Reproduction scripts overwrite their local logs and may create the uncompressed export. Preserve the original archive if comparing against the recorded manifest afterward.

## Trust and review boundaries

The proof sources contain no `sorry`, `admit`, `native_decide`, or project-declared mathematical axiom. `Audit.lean` checks the transitive axiom dependencies and fails for anything outside the stated allowlist. The independent export check provides further evidence beyond a source-text scan.

The builds and checker executions ran directly in the local Windows workspace. No hermetic container, network-isolated verifier, external human reviewer, organizer verification identity, or official award status is claimed. The final theorem's relation to the published mathematics is explained in `STATEMENT.md`; a separate reading found no weakened hypotheses or missing ground-set sizes. That reading was AI-assisted, not an organizer's human review.

The contribution and limited prior-work search are described in `PRIORITY-REVIEW.md`. Local completion does not establish public formalization priority. The public landing page distributes this research artifact; it is not an official prize submission. This public research release names Guo Qiang as project lead, with OpenAI Codex assistance, in AUTHORS.md.
