# Quandles with orbit series: Questions 5.25 and 5.7

Working preprints by **Danil Pokulevskii**, Novosibirsk State Technical
University, Novosibirsk, Russia ([555tery](https://github.com/555tery),
555tery@gmail.com).

Both papers address questions in Bonatto–Crans–Nasybullov–Whitney,
*Quandles with orbit series conditions*, using the numbering and definitions
of [arXiv version 3](https://arxiv.org/abs/2004.10227v3).
Both manuscripts are revised October 10, 2026. Their references, definitions
and proof dependencies were checked in both languages; the present revision
clarifies earlier sources and the scope of the results.

## Papers and LaTeX sources

| Paper | Русский | English |
|---|---|---|
| **Question 5.25 — Unbounded Orbit-Series and Reductivity Indices of Finite Quandles** | [PDF](question-5-25/q525_preprint_ru.pdf) · [TeX](question-5-25/q525_preprint_ru.tex) | [PDF](question-5-25/q525_preprint_en.pdf) · [TeX](question-5-25/q525_preprint_en.tex) |
| **Question 5.7 — Extension closure of orbit-series classes** | [PDF](question-5-7/q57_preprint_ru.pdf) · [TeX](question-5-7/q57_preprint_ru.tex) | [PDF](question-5-7/q57_preprint_en.pdf) · [TeX](question-5-7/q57_preprint_en.tex) |

### Question 5.25

For a finite quandle, let $k,j,i$ denote the least positive indices of local
reductivity, trivialization of orbit series, and reductivity, respectively.
The paper gives two finite families:

- For every $n\ge3$, $Q_n$ satisfies
  $k(Q_n)=2$ and $j(Q_n)=\lfloor\log_3n\rfloor+1$.
- For every $m\ge2$, $P_m$ satisfies
  $(k(P_m),j(P_m),i(P_m))=(2,2,m)$.

For the distinguished orbit series in $Q_n$, the $r$-th term has exact
cardinality
$|S_r|=2^{\sum_{t=3^r}^{n}\binom nt}$ for $r\ge0$.
The infinite product $\prod_{n\ge3}Q_n$ is a locally finite quandle in
$\mathcal{LR}_2\setminus\mathcal{OS}$.

Thus there is no universal bound on $j$ in terms of $k$, nor on $i$ in terms
of $j$. The constructions use the group of Noce–Tracey–Traustason and finite
quotients of reduced free groups. Their group-theoretic inputs and sources
are identified explicitly in the papers. The indexed group also occurs in
Hadjievangelou–Traustason. Darné describes the infinite free reduced quandle,
and the finite profile $(2,2,m)$ also follows from the Cohen–Mikhailov–Wu
quotients. The manuscript credits these predecessors and distinguishes the
computed quandle filtration from its group inputs. Recursive orbit
decomposition is related to Nelson–Wong's subquandle depth.

### Question 5.7

The paper proves that $\mathcal{OS}$ is closed under extensions of arbitrary
quandles and gives a counterexample to extension closure of
$\mathcal{OS}_\omega$. An extension means that the quotient and **every full
fiber** belong to the class; no uniform bound on the fiber depths is assumed.
The positive result includes nonfaithful and infinite quandles.

The proof contains a group-theoretic ascent theorem for commutator series
under one automorphism and its extension to a group of operators. The known
split-inner case is identified through Darné–Suciu and Guaschi–Pereiro.
BCNW arXiv v1/v2 already asserted the qualitative closure statement for
$\mathcal{OS}$; v3 introduced Question 5.7. This version history is recorded
without establishing proof priority. The negative example for $\mathcal{OS}_\omega$ uses
an infinite disjoint union of finite dihedral quandles with unbounded depths.

## References and independent reading

Each article contains the definitions and conventions needed to read its
proofs. External mathematical inputs have pinpoint citations to specified
source versions; auxiliary arguments are proved in the text.
The papers do not depend on each other or on the research wiki.
See the [reference and dependency map](REFERENCES_AND_DEPENDENCIES.md).

## Build

Each `.tex` file is standalone, including its bibliography. No external
figures or bibliography files are needed. Use XeLaTeX or Tectonic; the font
configuration uses the CMU fonts. For example, with Tectonic:

```sh
tectonic question-5-25/q525_preprint_en.tex
tectonic question-5-7/q57_preprint_en.tex
```

## Status

The texts include proofs or precise references for their inputs and have
undergone internal mathematical review, comparison of the two language
versions, compilation, and visual inspection of the PDFs. External peer
review has not yet been obtained.
**Novelty and publication priority have not been established.**

## Earlier notes on Question 5.25

The separate notes from October 6, 2026 are retained as earlier versions.
For the complete article and current presentation, use the preprint above.

- Part 1: [Markdown](PART_1_BOUND_J_BY_K.md) · [PDF](PART_1_BOUND_J_BY_K.pdf).
- Part 2: [Markdown](PART_2_BOUND_I_BY_J.md) · [PDF](PART_2_BOUND_I_BY_J.pdf).

## Кратко по-русски

Здесь опубликованы две работы и их самостоятельные исходники TeX на русском
и английском языках. По вопросу 5.25 получены отрицательные ответы на обе
части: индекс $j$ не ограничивается через $k$, а индекс $i$ — через $j$.
Для первой конструкции получена точная глубина и формула мощностей членов
выбранного орбитального ряда; бесконечное произведение примеров локально
конечно и не принадлежит $\mathcal{OS}$. По вопросу 5.7 класс
$\mathcal{OS}$ замкнут относительно extensions, а
$\mathcal{OS}_\omega$ не замкнут. Внутренняя проверка завершена;
внешнее рецензирование, новизна и приоритет остаются отдельными задачами.
