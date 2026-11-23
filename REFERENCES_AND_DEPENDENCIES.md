# References and self-containment of the two preprints

This map applies to both language versions, revised October 10, 2026
for Q5.25 and November 23, 2026 for Q5.7. It records the sources actually used in the arguments;
it is not a claim that the literature or publication priority has been
exhaustively checked.

## Question 5.25

| Input | Exact source used | Treatment in the manuscript |
|---|---|---|
| Left quandle convention, reductivity and orbit-series classes | [BCNW, arXiv v3](https://arxiv.org/abs/2004.10227v3), Sections 2 and 4.1 | Definitions are given in Section 2. |
| Equivalence of the finite-depth unions for finite quandles | BCNW, Corollary 5.19 | Cited in the introduction and in the proof that the first family's index exists. |
| Principal orbit series in finite quandles | BCNW, Proposition 4.6 and Corollary 4.8 | Used to pass from the computed principal series to the exact depth of every orbit series in the transitive conjugacy class. |
| Group criterion for reductivity | BCNW, Proposition 3.2 | Credited; a direct proof with the index convention is included in Section 2. |
| NTT operator construction | [Noce–Tracey–Traustason, arXiv v1](https://arxiv.org/abs/1811.12074v1), Section 2, construction before Lemma 2.2 | The subgroup with finite labels is specified; the operator action and empty-label convention are stated. The underlying operator construction is referenced. |
| Commutator formulas, normal form and the required Engel identity | NTT, Lemma 2.3, Proposition 2.4, proof of Theorem 2.5 | The exact formulas used are stated with separate references in Section 3.1. |
| Exact cardinalities of the principal orbit-series terms and local finiteness of the infinite product | Derived from NTT, Proposition 2.4, Theorem 2.5 and Corollary 2.7; Proposition 2.9 supplies the finite nilpotency-class bound | The exact orbit-cardinality formula and the locally finite product corollary are proved in Section 3. |
| Recursive orbit decomposition and subquandle depth | [Nelson–Wong, §5](https://arxiv.org/abs/math/0508247v3), DOI 10.1142/S0218216506004701 | Credited in the introduction; equality with $j$ is asserted only for the nontrivial first-family examples with singleton terminal leaves. |
| Known finite Cohen-group quotients of exact class $m$ | [Cohen–Mikhailov–Wu, §§1–2](https://arxiv.org/abs/1506.00948v1), DOI 10.1007/s00209-017-2018-5 | Section 4 explains why their finite groups also yield exactly $m$ trivial inner orbits and profile $(2,2,m)$; the Magnus-quotient proof remains included as another realization. |
| Reduced free group, class, center and Magnus embedding | [Darné, arXiv v2](https://arxiv.org/abs/1904.10677v2), Definition 1.2, Propositions 1.3 and 1.18, Corollary 1.13 | The presentation and the input statements are given in Section 4.1 with precise references. |
| Free reduced quandle as generator conjugacy classes in the reduced free group | [Darné, *Nilpotent quandles*, Proposition 7.10 and Corollary 7.11](https://arxiv.org/abs/2205.02480v3), also published in *Advances in Mathematics* 495 (2026), article 110977 | The infinite quandle-level predecessor and its relation to the finite family are discussed in Section 4.1. |
| Reduced associative algebra and its word basis | Darné, Definition 1.4 and Fact 1.5 | The ring, its two-sided ideal and its basis are specified before the finite-quotient argument. |
| Historical attribution of the reduced free group and class bound | [Milnor, Link groups](https://doi.org/10.2307/1969685); [Habegger–Lin, Lemma 1.3](https://doi.org/10.1090/S0894-0347-1990-1026062-0), as attributed in Darné | Original attribution is included; the proof inputs are taken from the specified version of Darné. |
| Scope of a result concerning the full conjugation quandle | BCNW, Corollary 5.24 | Its scope is explained in Section 5; the generator-class union used here is distinguished from the full conjugation quandle. |

The finite NTT family, its filtration, exact orbit-series depth and infinite
\(\mathcal{LR}_2\setminus\mathcal{OS}\) product corollary are proved in
Section 3. The finite quotient preserving the reduced free group's
class, the union of generator conjugacy classes, and all three exact indices
are proved in Section 4. These arguments require no other project notes.

### Novelty-related sources found after the earlier dependency audit

Hadjievangelou–Traustason, [*Left 3-Engel elements in locally finite
2-groups*](https://arxiv.org/html/2110.15685), §§2–3, Lemma 3.2,
Proposition 3.3 and Theorem 3.4, generalizes the NTT indexed-group
construction. Their parameter $m=2$ (hence their $n=2^m-2=2$) gives
the same two-layer group; restricting labels to nonempty subsets of
$[N]$ gives the finite sections $G_N$. The quandle filtration and exact
orbit-cardinality formula are derived in Section 3.

Darné's *Nilpotent quandles*, Proposition 7.10, gives the infinite free
reduced quandle underlying the second family. Cohen–Mikhailov–Wu already
provide finite reduced-group quotients of exact class $m$, from which the
finite quandle profile $(2,2,m)$ follows as explained in Section 4.
Consequently, finite-profile existence alone is not presented as evidence
of novelty. Nelson–Wong's subquandle depth is also credited. These
attributions do not establish priority of the remaining exact calculations.

## Question 5.7

| Input or terminology | Exact source used | Treatment in the manuscript |
|---|---|---|
| Orbit-series classes and the extension convention | [BCNW, Journal of Algebra](https://doi.org/10.1016/j.jalgebra.2020.09.026), Sections 2.2 and 4.1 and Question 5.7 on p. 301 | The main statements are in Section 1. Section 2 defines principal depth and relates it to arbitrary orbit series. |
| Principal and nonprincipal orbit series | BCNW, Corollary 4.7 and Examples 4.3 and 4.9 | Section 2 discusses finite stabilization, empty intersections, and the index-zero convention. |
| Images of orbit series | BCNW, Section 2.2 and Lemma 5.1 | Section 2 includes the proof for arbitrary and principal series. |
| Earlier uniform bound and extension assertions | [BCNW v1](https://arxiv.org/abs/2004.10227v1) and [v2](https://arxiv.org/abs/2004.10227v2), Lemma 5.5 and Corollary 5.6 | The README records the earlier assertions. Both introductions use the published statement of Question 5.7, discuss the singleton-base step in Lemma 5.5 and cite the comment about \(D_3\) on p. 302. |
| Dihedral examples | BCNW, Examples 4.1 and 4.2 and the paragraph after Corollary 5.20 | Section 4 computes the orbit depths, proves sharpness using reduction modulo a power of two, and projects the disjoint sum onto the summand index. |
| Uniform fiber-depth hypothesis | BCNW, Lemma 5.5 and Corollary 5.6 on p. 301 | Section 4 explains why extension closure of \(t\mathcal{OS}_\omega\) requires a common bound across all full fibres. |

The proof in Section 3 compares the groups generated by left translations
in the source and in the fiber over a connected base. It uses the elementary
fact that a subnormal subgroup of finite defect which normally generates its
ambient group must equal it. The manuscript proves this fact within the
argument. The [October revision](https://github.com/555tery/quandle-orbit-series/tree/42036b2d9c0aef3e21a6b68d9739bc1049919c0a/question-5-7)
gives an earlier proof using operator commutator series.

## Independent reading and compilation

Each paper supplies its own abstract, main statements, definitions,
conventions, proofs or pinpoint references for external inputs, scope
remarks, author details and bibliography. Neither paper depends on the
other preprint or on the research wiki. The `.tex` files do not include
external project files, figures or `.bib` files. Compilation requires the
standard LaTeX packages and fonts named in their preambles; the repository
README gives the build instructions.

The manuscripts were checked internally for source numbering, references to
results used in the proofs, agreement of the two language versions and PDF
layout. External peer review and publication priority remain open.

## По-русски

Каждая статья читается самостоятельно: определения, соглашения и
доказательства включены в текст, а используемые внешние результаты имеют
ссылки на конкретные места и версии источников. В 5.25 добавлены атрибуции
H–T, Darné, Nelson–Wong и Cohen–Mikhailov–Wu; существование конечного профиля
$(2,2,m)$ уже следует из известных групповых конструкций. В 5.7 история
BCNW v1/v2/v3 отражена в README, а обе версии препринта ссылаются
на журнальную постановку задачи и дают прямое доказательство точной
поточечной оценки. Публикационный приоритет остаётся неустановленным.
