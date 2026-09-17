# Bounded priority and submission-scope review

**Intake update:** the latest official commit `82be4c4913b8fe394d68d1391f4c221fde947211` adds a complete-original-problem requirement and excludes special cases. `CURRENT-INTAKE.md` supersedes the submission-expectation discussion below. The bounded prior-work findings do not establish eligibility for this k=4 package.

Review performed on 2026-09-17, approximately 12:06–12:08 UTC. This is a limited public-source search, not a proof of first-publication priority and not an eligibility or award decision. No issue, PR, or other external message was posted during this review.

## Search scope and observed results

The official repository's issue/PR search was queried for `JSP-000572`, `702`, `Keevash`, and `singleton`. The JSP identifier search returned PR 79, recipient issue 84, and existing-proof registration issue 16. The broader searches did not reveal a directly matching submission for the exact four-uniform bound at every ground-set size.

- [JSP-000572 search](https://github.com/TheJustinSunPrize/awards/issues?q=JSP-000572)
- [Erdős 702 search](https://github.com/TheJustinSunPrize/awards/issues?q=702)
- [Keevash search](https://github.com/TheJustinSunPrize/awards/issues?q=Keevash)
- [Singleton search](https://github.com/TheJustinSunPrize/awards/issues?q=singleton)

Search results can be incomplete, are mutable, and do not cover all public repositories or private work. They must be refreshed immediately before submission.

## Directly relevant earlier work

[PR 79](https://github.com/TheJustinSunPrize/awards/pull/79), opened at 2026-09-16 14:07:54 UTC, formalizes Frankl's eventual-in-n theorem for every fixed uniformity k ≥ 4. Its exported main theorem supplies an explicit, unoptimized sufficient threshold. It also constructs a fixed-pair extremizer. The PR expressly excludes equality-case classification. Its recipient issue [84](https://github.com/TheJustinSunPrize/awards/issues/84) was created at 2026-09-16 14:20:07 UTC. These are prior submissions, not evidence of an announced award.

[Issue 16](https://github.com/TheJustinSunPrize/awards/issues/16), created at 2026-09-16 09:46:58 UTC, registers existing proofs including `Erdos702.erdos_702_eventually` and the counterexample to the unrestricted original all-n claim. Its text explicitly preserves eventual-in-n scope.

The inspected [plby source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos702.lean) is pinned to commit `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`; `git ls-remote` still returned that main-branch commit during this review. A fresh download of `main/src/latest/ErdosProblems/Erdos702.lean` matched the previously inspected bytes exactly:

`SHA-256: 3ed6feb37293f5358632ed6fbd75e4d9a12600dd438a524ef93baabc588ad24f`

The inspected export is eventual, not the exact four-uniform statement established here. No claim is made that this bounded review exhaustively inspected every dependency or every public development branch.

## Defensible contribution description

This package formalizes the numerical four-uniform theorem of Keevash, Mubayi, and Wilson: the exact bound is 15 for n = 7, 17 for n = 8, and binomial(n−2,2) for n ≥ 9, with the elementary smaller cases and attaining constructions. It is an additional formalization scope associated with JSP-000572, not the first proof or the first formalization of Frankl's general eventual theorem. It does not classify all extremizers. The mathematical result is attributed to its original authors.

The limited searches above found no directly matching exact-all-n submission. That finding does not establish exclusive priority or guarantee that an extension under an already submitted catalog entry will receive an award.

The [official FAQ, Q8](https://www.hejustinsun.com/zh/prize/faq), says solver priority and formalizer priority are separate, and formalization priority follows first public visibility across platforms. It does not follow local completion, submission, or merge time. This package's local completion therefore does not itself establish a public priority timestamp.

## Submission expectations to preserve

The [Selection Rules](https://www.hejustinsun.com/zh/prize/rules), version 1.0 effective 2026-09-16, require Lean statements, proofs, and supporting evidence, followed by designated verification and adjudication. Passing Lean is an entry condition. A local build is not an award decision. Partial or additional scope must be described accurately rather than represented as closure of a different original proposition.

The current [contribution guide](https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md) requires English records, retained third-party attribution and licensing, and confirmed public identities or placeholders. It contains no dedicated Lean proof-package intake template. The existing PR 79 submission directory is precedent, not an official prescribed location.

The [record guide](https://github.com/TheJustinSunPrize/awards/blob/main/docs/records.md) and [verification schema](https://github.com/TheJustinSunPrize/awards/blob/main/data/schema/verification-record.schema.json) distinguish draft evidence from completed official records. Full records include pinned source and library commits, theorem statements and axiom lists, statement comparison, at least two checker entries, environment/isolation information, attribution, reviewer identity/date, and archived artifacts with hashes and byte counts. Record CI validates structure and references; it does not run or certify mathematical proofs. Only report checks and isolation conditions actually performed; retain pending fields or a separate provisional evidence report for unperformed independent review.
