# Independent checks of the final declaration

The dependency-closed text export of `JSP572Four.jsp572_four_complete` was accepted by both bundled independent checkers:

| Checker | Result | Evidence |
|---|---|---|
| lean4lean | Exit 0; 8,283 declarations checked | `external-lean4lean.log`, `external-lean4lean-status.log` |
| nanoda | Exit 0; successful run is silent | `external-nanoda.log`, `external-nanoda-status.log` |

The export contains the target theorem and exactly three axioms: `propext`, `Classical.choice`, and `Quot.sound`. Nanoda was configured to reject any other axiom. No axiom whitelist was expanded to obtain acceptance. There are 8,286 declaration records including those three axioms.

The producer toolchain is Lean `4.35.0-rc2`, commit `11acb17ec6b07a8f9e9173e6845197929540936b`. `external-check-metadata.json` records the actual checker-binary SHA256 values, export SHA256, module artifact SHA256, and source hashes. Separate source repository commits for the bundled checkers were not established and are not claimed.

## Reproduce from the archived proof export

From the project directory, on Windows with the same bundled toolchain:

```powershell
./verification/external-check.ps1 -FromArchive -LeanBin 'C:/path/to/lean-4.35.0-rc2-windows/bin'
```

This decompresses `jsp572-four-complete.ndjson.gz`, checks its recorded SHA256, then replays it through both checkers. It does not load the project's `.olean` files into either checker.

## Regenerate from a built project

After building the project with its pinned dependencies:

```powershell
./verification/external-check.ps1 -LeanBin 'C:/path/to/lean-4.35.0-rc2-windows/bin'
```

The exact exporter invocation is:

```text
lake env leanexport JSP572Four.Main -- JSP572Four.jsp572_four_complete
```

The `--` separator selects the theorem. The exporter includes its dependencies automatically; no separate closure flag is used. The checker commands, run with the verification directory as their working directory, are:

```text
lean4lean --import jsp572-four-complete.ndjson
nanoda_bin external-nanoda-config.json
```

## Scope of this evidence

These were direct executions in the Windows local workspace. They were not run in a hermetic container, a network-isolated environment, or the Linux `bwrap` sandbox used by `lake check`. Acceptance concerns this exact exported declaration and its dependencies. It is not an official prize review, a novelty determination, or a promise of eligibility.
