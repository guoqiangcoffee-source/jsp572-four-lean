# Exact four-uniform no-singleton intersection theorem

**Guo Qiang (郭强), AI-assisted formalization project · 2026-09-17**

[中文说明](README.zh-CN.md) · Public contact: [guoqiangcoffee@gmail.com](mailto:guoqiangcoffee@gmail.com)

This project formalizes the exact numerical four-uniform theorem of Keevash, Mubayi and Wilson (2006). For every natural number n, it proves the maximum size of a family of four-element subsets of an n-element set in which no two members intersect in exactly one element. It includes an attaining construction for every n.

| Ground-set size n | Exact maximum |
|---|---|
| 0 ≤ n ≤ 6 | C(n, 4) |
| n = 7 | 15 |
| n = 8 | 17 |
| n ≥ 9 | C(n−2, 2) |

The final theorem is **JSP572Four.jsp572_four_complete** in [JSP572Four/Main.lean](JSP572Four/Main.lean). It combines a maximizing witness with universal optimality. There are 23 proof modules. The exact formal statement and its relation to the mathematics are described in [STATEMENT.md](STATEMENT.md).

## Contribution and attribution

Guo Qiang initiated the project, selected the research direction, and publishes this AI-assisted formalization. OpenAI Codex assisted with mathematical reasoning, Lean implementation, verification execution, and documentation. This project claims formalization work and recorded verification, not discovery of a new mathematical theorem.

The mathematical theorem is due to **Peter Keevash, Dhruv Mubayi, and Richard M. Wilson**, *Set Systems with No Singleton Intersection*, SIAM Journal on Discrete Mathematics 20(4), 1031–1041 (2006), Theorem 1.1, numerical part. [DOI](https://doi.org/10.1137/050647372) · [Author's PDF](https://people.maths.ox.ac.uk/keevash/papers/no-singleton-journal.pdf).

The proof uses mathlib, shifting with kernel-checked finite certificates for the two-intersecting branch, and the source paper's matching and residual-colour decomposition for the nonintersecting branch. No earlier JSP-000572 proof package is imported. See [AUTHORS.md](AUTHORS.md) for the adapted mathlib fragment and its retained attribution.

## Reproduction

- Lean: **leanprover/lean4:v4.35.0-rc2**.
- mathlib: **f61f3ed7633ff99ecaae4a086395b501652a76ee**.
- Dependency revisions are pinned in **lake-manifest.json**.

Install the pinned Lean toolchain and Git, then run from this repository:

~~~text
lake exe cache get
lake build JSP572Four
lake env lean Audit.lean
~~~

Windows users may run **verify.ps1**. A Bash wrapper **verify.sh** is included, but this release's recorded checks ran on Windows. Retain the pinned manifest when reproducing the result.

## Recorded verification

- All proof modules compiled; the final theorem passed Lean kernel replay.
- An explicit audit permits only **propext**, **Classical.choice**, and **Quot.sound**.
- Proof sources contain no sorry, admit, project-declared mathematical axiom, or native_decide.
- Two independent checker implementations, **lean4lean** and **nanoda**, accepted the dependency-closed proof export. lean4lean checked 8,283 declarations, with the three permitted axioms listed separately.
- The proof modules and export are byte-identical to the checked research package. Contact and publication documentation have been updated for this release.

See [VERIFICATION.md](VERIFICATION.md) and the **verification/** directory for evidence and limits. These are recorded local checks, not organizer-issued certification. MANIFEST.sha256 covers all distributed files except itself and Git metadata. The Git attributes preserve the archived proof-source bytes without line-ending conversion.

## Relationship to JSP-000572 and submission status

This is the exact **k=4** result for all n. It does not formalize the original problem for all k≥4 and does not classify all equality cases. Earlier public work proves the general eventual-in-n statement; see [PRIORITY-REVIEW.md](PRIORITY-REVIEW.md).

The source and verification package are public at [guoqiangcoffee-source/jsp572-four-lean](https://github.com/guoqiangcoffee-source/jsp572-four-lean). Guo Qiang is preparing a formal submission for the organizers' consideration, with the four-uniform scope and prior work disclosed.

The Justin Sun Prize's complete-original-problem policy, checked at official commit **82be4c4913b8fe394d68d1391f4c221fde947211**, requires the full original problem and excludes standalone special cases. This package does not meet that general-scope requirement. Submission asks the organizers to assess the contribution; it does not establish eligibility, acceptance, priority or an award. No acceptance has been received, and those determinations remain with the reviewers. See [CURRENT-INTAKE.md](CURRENT-INTAKE.md).

License: Apache-2.0. See [LICENSE](LICENSE).
