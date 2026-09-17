# Current official intake: scope limitation

Checked against the freshly fetched official repository on 17 September 2026. The relevant revision is `82be4c4913b8fe394d68d1391f4c221fde947211`, committed at 11:56:34 UTC that day by the merge of PR #646. This document supersedes earlier intake assumptions based on an older revision or cached web rendering.

## Completeness requirement

The [contribution guide at that revision](https://github.com/TheJustinSunPrize/awards/blob/82be4c4913b8fe394d68d1391f4c221fde947211/CONTRIBUTING.md) states:

> Only complete solutions to the original problem are accepted. Partial progress is not eligible for submission, whether mathematical or in Lean.

The following paragraphs explicitly exclude special cases, intermediate lemmas, weaker results and conditional arguments. The [current PR template](https://github.com/TheJustinSunPrize/awards/blob/82be4c4913b8fe394d68d1391f4c221fde947211/.github/PULL_REQUEST_TEMPLATE.md) likewise requires an explanation that the pinned proof covers the full original statement and every required case.

Our theorem is a complete numerical extremal theorem for **four-element sets**, with all ground-set sizes and attaining constructions. It is not a Lean proof of the original question for general uniformity. The [JSP-000572 catalog entry at the same revision](https://github.com/TheJustinSunPrize/awards/blob/82be4c4913b8fe394d68d1391f4c221fde947211/problems/catalog-0501-0600.md#JSP-000572) describes the general uniform-family problem and cites Frankl's 1977 paper.

Consequently, the completed four-uniform formalization does not satisfy the current full-original-scope requirement for a JSP-000572 proof submission. Its mathematical correctness and verification results do not remove that scope mismatch. This package must not be presented as ready for an eligible official JSP-000572 submission or as establishing award entitlement. A different, separately accepted problem scope would require an explicit organizer decision; no such decision has been obtained.

## Required publication format

The same contribution guide now directs external contributors to edit the relevant existing catalog entry and submit references only. It prohibits adding proof source, project/build files, dependencies, archives or binaries to the official awards repository.

For a qualifying Lean reference, the template requires a public repository URL, branch and full 40-character commit SHA, together with the exact theorem/file, formalization authors, public attribution evidence and build instructions. Repository ownership or PR submission alone does not establish mathematical or formalization authorship.

No public repository, commit, archive location, identity confirmation or acceptance has been invented. No public issue or PR has been posted. The offline official worktree remains at the pinned baseline with no catalog changes and no proof files copied into it.

The source project and verification package remain useful completed mathematical artifacts. Any later publication must state their four-uniform scope and preserve this current intake limitation unless the official requirements or the organizer's decision change.
