# References and self-containment of the two preprints

Revision: **October 8, 2026**. This map applies to both the Russian and
English manuscripts. It records the sources actually used in the arguments;
it is not a claim that the literature or publication priority has been
exhaustively checked.

## Question 5.25

| Input | Exact source used | Treatment in the manuscript |
|---|---|---|
| Left quandle convention, reductivity and orbit-series classes | [BCNW, arXiv v3](https://arxiv.org/abs/2004.10227v3), Sections 2 and 4.1 | Definitions are given in Section 2. |
| Equivalence of the finite-depth unions for finite quandles | BCNW, Corollary 5.19 | Cited in the introduction and in the proof that the first family's index exists. |
| Group criterion for reductivity | BCNW, Proposition 3.2 | Credited; a direct proof with the index convention is included in Section 2. |
| NTT operator construction | [Noce–Tracey–Traustason, arXiv v1](https://arxiv.org/abs/1811.12074v1), Section 2, construction before Lemma 2.2 | The subgroup with finite labels is specified; the operator action and empty-label convention are stated. The underlying operator construction is referenced. |
| Commutator formulas, normal form and the required Engel identity | NTT, Lemma 2.3, Proposition 2.4, proof of Theorem 2.5 | The exact formulas used are stated with separate references in Section 3.1. |
| Reduced free group, class, center and Magnus embedding | [Darné, arXiv v2](https://arxiv.org/abs/1904.10677v2), Definition 1.2, Propositions 1.3 and 1.18, Corollary 1.13 | The presentation and the input statements are given in Section 4.1 with precise references. |
| Reduced associative algebra and its word basis | Darné, Definition 1.4 and Fact 1.5 | The ring, its two-sided ideal and its basis are specified before the finite-quotient argument. |
| Historical attribution of the reduced free group and class bound | [Milnor, Link groups](https://doi.org/10.2307/1969685); [Habegger–Lin, Lemma 1.3](https://doi.org/10.1090/S0894-0347-1990-1026062-0), as attributed in Darné | Original attribution is included; the proof inputs are taken from the specified version of Darné. |
| Scope of a result concerning the full conjugation quandle | BCNW, Corollary 5.24 | Its scope is explained in Section 5; the generator-class union used here is distinguished from the full conjugation quandle. |

The finite NTT family, its filtration and orbit-depth lower bound are proved
in Section 3. The finite quotient preserving the reduced free group's
class, the union of generator conjugacy classes, and all three exact indices
are proved in Section 4. These arguments require no other project notes.

## Question 5.7

| Input or terminology | Exact source used | Treatment in the manuscript |
|---|---|---|
| Orbit-series classes and the extension convention | [BCNW, arXiv v3](https://arxiv.org/abs/2004.10227v3), Sections 4.1 and 2.2, Question 5.7 | Definitions of all classes used, full fibres and surjective homomorphisms are included in Section 2. |
| Quandle covering | [Eisermann, arXiv v3](https://arxiv.org/abs/math/0612459v3), Definition 2.32 | The definition is credited and translated from right to left convention. The property of coverings needed here is proved in Section 2. |
| Failure of unrestricted subquandle closure | BCNW, Example 5.3 | Cited when distinguishing invariant subquandles and slices from arbitrary subquandles. |
| Faithful quandle terminology | BCNW, Section 2.2 | The injectivity condition is stated explicitly. No faithfulization theorem is imported. |
| Disjoint sum of finite dihedral quandles | BCNW, Example 4.2 | The original construction is credited. The projection, full fibres, orbit computation and failure of extension closure are verified in Section 6. |
| Uniform fibre-depth hypothesis and the related published assertion | BCNW, Lemma 5.5 and Corollary 5.6, specifically arXiv v3 | Both results are cited separately in the final remark, with the relevant distinction in hypotheses. |

All mathematical steps in the positive proof are proved in the manuscript:
images of orbit series, invariant subquandles and slices, the covering
lemma, the subnormal-generation lemma, automorphism ascent, conjugacy-class
orbit towers, exact full fibres, the formal cyclic lift and the passage to
arbitrary quandles. The formal lift maps include checks of defining relations
and surjectivity. No result from the Imamura–Yoshida or categorical-extension
papers is used as a proof input.

## Independent reading and compilation

Each paper supplies its own abstract, main statements, definitions,
conventions, proofs or pinpoint references for external inputs, scope
remarks, author details and bibliography. Neither paper depends on the
other preprint or on the research wiki. The `.tex` files do not include
external project files, figures or `.bib` files. Compilation requires the
standard LaTeX packages and fonts named in their preambles; the repository
README gives the build instructions.

The revised manuscripts were checked internally for source numbering,
reference coverage, agreement of the two language versions and PDF layout.
This is an internal dependency audit, not external peer review and not an
establishment of novelty or priority.

## По-русски

Каждая статья читается самостоятельно: определения, соглашения и
доказательства включены в текст, а используемые внешние результаты имеют
ссылки на конкретные места и версии источников. Изложение по 5.25 использует
групповые результаты NTT и Darné; в статье по 5.7 вспомогательные результаты
доказаны непосредственно. Исходники каждой версии также самостоятельны.
Проверка полноты ссылок не устанавливает публикационный приоритет.
