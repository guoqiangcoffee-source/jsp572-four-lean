# Statement comparison

Let F be a family of four-element subsets of a finite n-element set. Assume no two members have intersection of size exactly one. The largest possible cardinality is binomial(n,4) for n≤6, 15 for n=7, 17 for n=8, and binomial(n−2,2) for n≥9.

`Uniform 4 F` means every member has cardinality four. `NoSingleton F` means `∀ A ∈ F, ∀ B ∈ F, (A ∩ B).card ≠ 1`. Including A=B is harmless because every member has cardinality four. `Supported X F` means every member is a subset of X. Finite sets encode families without repeated members.

`sharpBound` is exactly the piecewise formula above. The cases n<4 have value zero. `singletonFree_four_bound` gives the upper bound on an arbitrary finite ground set; the public finite-ground formulation uses `Fin n`.

`jsp572_four_complete` proves, for every n, existence of a family F satisfying both conditions with cardinality `sharpBound n`, and universal optimality against every other family G satisfying those conditions. There is no large-n, two-intersection, matching, or unproved-paper-theorem hypothesis in the final statement.

## Relationship to earlier formalizations

Frankl's result treats every fixed k≥4 once n is sufficiently large. The reviewed earlier packages prove that eventual statement. This package fixes k=4 and proves the exact threshold n=9, exceptional maxima at 7 and 8, smaller cases, and attainment. Its contribution should be evaluated only at this additional scope.

Only the numerical maximum and an attaining construction are claimed. The original paper's printed uniqueness sentence at n=9 cannot be used verbatim: the four-sets A⊆[9] with |A∩[4]|≥3 form a 21-member two-intersecting family with empty common intersection, so they are not a fixed-pair star. This does not invalidate the numerical maximum and is not claimed here as a new discovery.

## Proof organization

1. Compress two-intersecting families without changing cardinality. Kernel-checked certificates give the shifted bounds on 7, 8, and 9 points. The shifted maximum-element link is a two-intersecting triple family, yielding induction for larger n from an elementary triple bound.
2. Otherwise choose a maximum disjoint subfamily. Count internal members using the two-block lemma, then partition residual vertices into coloured supports, isolated pairs, and remaining vertices. Prove all three counts and the final numerical comparison.
3. Supply explicit attaining families at exceptional sizes and fixed-pair stars at larger sizes, and combine with the universal upper bound.
