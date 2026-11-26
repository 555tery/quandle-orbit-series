# QuandleResearch — statement-only Lean 4 library

Scope: all 69 issues (#1–#69) present in [quandle-orbit-series](https://github.com/555tery/quandle-orbit-series/issues) at the initial snapshot. This package records problem statements, not solutions. No issue is marked solved by this package. There are no proof stubs, extra axioms, or asserted theorems.

## Structure

- `QuandleResearch/Basic/`: rack, quandle, BNS biquandle, homomorphisms, isomorphisms and free-object specifications.
- `QuandleResearch/Theory/`: Mathlib groups, commutators, lower central/derived series, normal-closure towers, orbit series, enveloping-group universal property, skew braces, and explicitly provisional interfaces.
- `QuandleResearch/Questions/`: one module per issue, with original issue URL, source text, formal statement or candidate-answer specification, and any missing definitions.

The group commutator is x⁻¹y⁻¹xy; the quandle convention is right translation. The quadratic-equation module uses its source's alternate commutator explicitly. Group nilpotency series starts at index 0 (the whole group). Carriers currently use universe `Type` rather than arbitrary universes.

## Build

With elan installed:

```sh
cd lean
lake update
lake exe cache get
lake build
```

Pinned Lean and Mathlib: v4.19.0. Compilation has not yet been run in this environment; the files are a first-pass specification draft, not certified Lean code. Source wording has been carried over from repository issues; not all original articles have been independently audited.

## Concrete braid groups

`Theory/BraidGroups.lean` defines the classical, virtual, universal, flat virtual and Gauss virtual presentations, pure and other projection subgroups via images of free-word kernels, and the virtual quotient by the derived pure subgroup. The standard distant mixed relation is used; the discrepant printed inequality in arXiv:2107.03875v1 (21) is recorded in the module. Map descent and right-action conventions need independent audit. No solutions are asserted.

## Additional concrete structures

`ConcreteEnveloping.lean` uses the standard free-group presentation, `LinearGroups.lean` fixes the actual GL/SL targets and field automorphism action, and `AbelianExtensions.lean` encodes normalized cocycle data and multiplication. Issue062 uses rational-function matrices with explicit regularity at 1. These are statement-level constructions; no solution proof is added.

## Build audit

The earlier commit fae06e7 compiled 67 of 69 issue modules and all then-existing shared modules. The failed Issue046 used the reserved token `GL`; it has since been replaced by the concrete matrix group formulation. Issue022 required an explicit binder type for `B`; that annotation is added. The current head still requires a fresh CI result.

`Basic/StrongBiquandle.lean` directly encodes the strong switch axioms (braid equation, nondegeneracy, both fixed-pair uniqueness conditions) in the convention of the repository note. Issue064 now uses this category, separately from BNS biquandles.

## Source-level representation refinements

Issues 028, 030 and 060 now specify the Laurent coefficient rings, generator matrices or Fox product rule directly. Issue030 distinguishes lowercase extended psi from capital Psi (the latter acts on the n strand generators and an additional y). The discrepancy F_(n-1) in the printed question versus F_(n+1) in the defining display is retained in the module comment. Source: https://arxiv.org/html/2107.03875v1 §§3, 5.1. Right-action automorphism formulas are encoded via inverse images under standard composition.

## Profinite and unitriangular structures

`Theory/Profinite.lean` records finite inverse systems, compatible tuples, the initial topology and profiniteness. The Stone-indexed union constructor is a candidate interpretation of an open-ended research direction, not a source-defined operation. Issue003 now specifies the upper unitriangular matrix group over F2 and the union of conjugacy classes of elementary transvections.

## Mathlib-first migration (stage 1)

- `Basic/Quandle.lean` bundles native Mathlib `Rack` / `Quandle` typeclasses; `ShelfHom` is the homomorphism type.
- `Theory/Groups.lean` uses Mathlib's `lowerCentralSeries`, `derivedSeries`, `Group.IsNilpotent`, `IsSolvable`, `Group.FG`, `IsCyclic`, `IsMulCommutative`, `Subgroup.FiniteIndex`, and pointwise set product.
- `Theory/EnvelopingGroup.lean` uses `Rack.EnvelGroup` and `Rack.toEnvelGroup`. The inverse generator preserves the source's right-conjugation convention.
- Issue018 uses `FreeAbelianGroup`; Issue020 uses Mathlib's dihedral operation; Issue059 uses `LaurentPolynomial`.
- Issue028: added classical decidability for conditional matrix entries after the CI error.

The last verified successful complete build before the migration was c9f11ed (GitHub Actions run 45881637104). A fresh CI run is needed for the migrated statements. Bundled compatibility aliases preserve the existing issue interfaces. This is not a finished semantic audit; source-specific definitions and categorical/topological reuse remain to be reviewed.

## Mathlib-first migration (stage 2)

- `Theory/Categories.lean`: native `CategoryTheory.Category`, `Functor` and `Adjunction` specify the quandle embedding and associated-quandle functor (#21, #22). The existing universal-arrow specifications are retained for comparison, not asserted equivalent in this package.
- `Theory/OrbitSeries.lean`: layers use the subgroup of permutations generated by their translations, Mathlib's `MulAction.orbit` / `orbitRel`, and `IsPretransitive`. Equivalence with the previous restricted relation is intended on subracks, not on arbitrary subsets.
- `Theory/Profinite.lean`: indexing Stone spaces are native Mathlib `Profinite` objects; profinite quandles remain defined by finite inverse systems.
- `Theory/AbelianExtensions.lean`: native `groupCohomology.IsMulTwoCocycle` with the action pulled back along the given group homomorphism via `MulAction.compHom`.

Fresh CI and source-convention review are required. No research solutions were added.

## Statement refinements

Issue044 specifies the actual integral representation by generator matrices from Theorem 3 and Corollary 3 (arXiv:2010.03162v1, p. 12). Issue034 has a native quotient-group type for each section and a target class of possible sections. Issue039 has the canonical comparison diagram and separate surjectivity/injectivity specifications. Issue036 and Issue037 retain alternate readings of ambiguous source hypotheses as separate propositions. No solution theorem is asserted.

## Reduced quandles and knot presentation data

`ReducedQuandles.lean` specifies Definition 7.1 and Fact 7.3 of Darné v3 using native Mathlib quandle morphisms and normal closures. `LinkPresentations.lean` specifies fundamental quandle and strong biquandle by actual crossing relations and universal properties. `QuandleCocycles.lean` encodes Inoue C1–C3, signed component weights and finite-target multiplicities with Mathlib additive groups and finite sums. Issues 004, 017, 056, 057, 065 and 069 now have concrete algebraic-side specifications in addition to the historical interfaces. Geometric realizability, diagram moves, Milnor invariants and surface diagrams are not yet implemented. Do not treat these as complete source formalizations.

CI: stage 1 (66ab229) compiled all 69 modules. Stage 2 (85f20bd) failed because OrbitSeries omitted the explicit carrier type on two orbit variables; fixed here. New CI is required.

## Additional source-specific refinements

Issue024 now has explicit switch axioms and a group-valued specialization of the algebraic-system invariant, with native PresentedGroup and FreeGroup. The exact equivalence convention and other algebraic systems remain outstanding. Issue050 now uses Mathlib GenContFract for S(p,q) and fixes chi using the source's epsilon/genus cases. Issue066 records candidate PartialEquiv-based semantics with both preserving and reflecting morphisms; the journal Problem 28 does not define the intended partial-biquandle category. These do not count as completed source formalizations.

## Source audit: BCNW, Darné, and BNS

- BCNW arXiv:2004.10227v3, §3.1, §4.1 and Question 5.25: `Trivializing` now means reaching a singleton T1 within the bound, not merely a trivial subquandle; `PositiveExactIndex` matches the positive-index families. Orbit-series layers are required to be subracks. This changes the shared predicates used by #3, #7, #13 and #14.
- Darné arXiv:2205.02480v3, Definition 2.20: residual nilpotence is expressed literally by separation through surjective ShelfHom into nilpotent quandles. The orbit criterion is named separately, with no equivalence theorem asserted. #67 and #68 use the source definition. Proposition 2.24 is a known direction, not a new open problem.
- BNS arXiv:1908.08301v1, Corollary 4.14 and Problem 4.15: #23 encodes both displayed operations and the action equation; compatibility with them is a test of a proposed general semidirect-product definition, not a claim to have defined the unique intended general construction.

## Geometric links and Milnor algebra

- `Theory/GeometricLinks.lean`: native metric spheres, continuous maps and homotopies in S³, with distinct-component disjointness; disjoint spanning disks describe unlink and Brunnian conditions. Also introduces a compact connected topological surface embedded in S⁴. Smooth/tame restrictions, orientation and geometric-to-diagram correspondence remain open infrastructure tasks.
- `Theory/Milnor.lean`: finite signed words in Mathlib's free-group convention, noncommutative Magnus coefficient convolution, proper cyclic subsequences, indeterminacy as an ideal of Int, quotient residue, and approximation of peripheral words modulo lower central terms.
- #4: two precise comparison directions for nonrepeating Milnor residues, not the whole descriptive question. #17: literal Brunnian wording and the homotopically nontrivial case separately. #58: concrete surface domain and presentation specifications.
- These modules are partial. The diagram maps and choice of geometric preferred peripheral elements still need a construction; neither arbitrary diagram maps nor all continuous embeddings are silently identified with the classical tame category.

## Coverage

STATEMENT means the principal proposition is expressed using concrete shared definitions, not that source correspondence or typechecking has been verified. PARTIAL means at least one source-specific construction, descriptive component, or convention remains to be encoded or checked. Candidate-answer predicates must be instantiated with independently specified constructions, not tautological restatements.

| Issue | Module | Status | Outstanding |
|---|---|---|---|
| [#1](https://github.com/555tery/quandle-orbit-series/issues/1) | [Issue001](QuandleResearch/Questions/Issue001.lean) | PARTIAL | Inverse limit and topology explicit; proposed Stone-union constructor and transfinite limit stages need audit. |
| [#2](https://github.com/555tery/quandle-orbit-series/issues/2) | [Issue002](QuandleResearch/Questions/Issue002.lean) | STATEMENT | Source audit and typecheck |
| [#3](https://github.com/555tery/quandle-orbit-series/issues/3) | [Issue003](QuandleResearch/Questions/Issue003.lean) | PARTIAL | Unitriangular group and conjugacy carrier explicit; exact orbit count and multipermutation convention need audit. |
| [#4](https://github.com/555tery/quandle-orbit-series/issues/4) | [Issue004](QuandleResearch/Questions/Issue004.lean) | PARTIAL | Magnus coefficients, ideal indeterminacy and peripheral approximation explicit; actual geometric peripheral data and relationship remain. |
| [#5](https://github.com/555tery/quandle-orbit-series/issues/5) | [Issue005](QuandleResearch/Questions/Issue005.lean) | PARTIAL | Source convention and rack fibre closure; candidate research direction, not a published theorem. |
| [#6](https://github.com/555tery/quandle-orbit-series/issues/6) | [Issue006](QuandleResearch/Questions/Issue006.lean) | STATEMENT | Source audit and typecheck |
| [#7](https://github.com/555tery/quandle-orbit-series/issues/7) | [Issue007](QuandleResearch/Questions/Issue007.lean) | PARTIAL | Reference family and exact group filtration; this is only one candidate research question. |
| [#8](https://github.com/555tery/quandle-orbit-series/issues/8) | [Issue008](QuandleResearch/Questions/Issue008.lean) | STATEMENT | Source audit and typecheck |
| [#9](https://github.com/555tery/quandle-orbit-series/issues/9) | [Issue009](QuandleResearch/Questions/Issue009.lean) | STATEMENT | Source audit and typecheck |
| [#10](https://github.com/555tery/quandle-orbit-series/issues/10) | [Issue010](QuandleResearch/Questions/Issue010.lean) | PARTIAL | Verify verbal word, indexing and sharpness scope against source. |
| [#11](https://github.com/555tery/quandle-orbit-series/issues/11) | [Issue011](QuandleResearch/Questions/Issue011.lean) | STATEMENT | Source audit and typecheck |
| [#12](https://github.com/555tery/quandle-orbit-series/issues/12) | [Issue012](QuandleResearch/Questions/Issue012.lean) | PARTIAL | An explicit classification model, not a tautological parameterization. |
| [#13](https://github.com/555tery/quandle-orbit-series/issues/13) | [Issue013](QuandleResearch/Questions/Issue013.lean) | STATEMENT | Source audit and typecheck |
| [#14](https://github.com/555tery/quandle-orbit-series/issues/14) | [Issue014](QuandleResearch/Questions/Issue014.lean) | STATEMENT | Source positive indices and singleton tOS_n audited; typecheck pending. |
| [#15](https://github.com/555tery/quandle-orbit-series/issues/15) | [Issue015](QuandleResearch/Questions/Issue015.lean) | STATEMENT | Source audit and typecheck |
| [#16](https://github.com/555tery/quandle-orbit-series/issues/16) | [Issue016](QuandleResearch/Questions/Issue016.lean) | PARTIAL | Check residual definition against paper; embeddings encode the iterates without constructing them. |
| [#17](https://github.com/555tery/quandle-orbit-series/issues/17) | [Issue017](QuandleResearch/Questions/Issue017.lean) | PARTIAL | Continuous link-homotopy, unlink and Brunnian conditions explicit; tame-category and diagram correspondence remain. |
| [#18](https://github.com/555tery/quandle-orbit-series/issues/18) | [Issue018](QuandleResearch/Questions/Issue018.lean) | PARTIAL | Concrete enveloping group presentation; independent structural classification is the requested answer, not part of the problem statement. |
| [#19](https://github.com/555tery/quandle-orbit-series/issues/19) | [Issue019](QuandleResearch/Questions/Issue019.lean) | PARTIAL | Concrete enveloping group presentation; independent structural classification is the requested answer, not part of the problem statement. |
| [#20](https://github.com/555tery/quandle-orbit-series/issues/20) | [Issue020](QuandleResearch/Questions/Issue020.lean) | PARTIAL | The dihedral operation, inner group and orbit-preserving condition are explicit; verify the precise QInn convention against the original article. |
| [#21](https://github.com/555tery/quandle-orbit-series/issues/21) | [Issue021](QuandleResearch/Questions/Issue021.lean) | PARTIAL | Native functors and adjunction statements; source morphism convention and typecheck remain to be audited. |
| [#22](https://github.com/555tery/quandle-orbit-series/issues/22) | [Issue022](QuandleResearch/Questions/Issue022.lean) | PARTIAL | Native functors and adjunction statements; source morphism convention and typecheck remain to be audited. |
| [#23](https://github.com/555tery/quandle-orbit-series/issues/23) | [Issue023](QuandleResearch/Questions/Issue023.lean) | PARTIAL | Exact Corollary 4.14 operations and action equation encoded; the requested general definition remains open-ended. |
| [#24](https://github.com/555tery/quandle-orbit-series/issues/24) | [Issue024](QuandleResearch/Questions/Issue024.lean) | PARTIAL | Switch laws, twist, group words and group-valued invariant explicit. General algebraic systems and geometric equivalence remain. |
| [#25](https://github.com/555tery/quandle-orbit-series/issues/25) | [Issue025](QuandleResearch/Questions/Issue025.lean) | PARTIAL | Concrete quotient and distinguished symmetric subgroup now defined; independent order classification and presentation-convention audit remain. |
| [#26](https://github.com/555tery/quandle-orbit-series/issues/26) | [Issue026](QuandleResearch/Questions/Issue026.lean) | PARTIAL | Concrete quotient and algebraic Bieberbach condition; independent subgroup classification and geometric convention audit remain. |
| [#27](https://github.com/555tery/quandle-orbit-series/issues/27) | [Issue027](QuandleResearch/Questions/Issue027.lean) | PARTIAL | Concrete VP_3; field scope and equivalence of kernel-image construction require audit. |
| [#28](https://github.com/555tery/quandle-orbit-series/issues/28) | [Issue028](QuandleResearch/Questions/Issue028.lean) | PARTIAL | Source equations (30)–(31) encoded on ordered pair basis over explicit Laurent ring. Independent audit of matrix convention and construction of the representation remain. |
| [#29](https://github.com/555tery/quandle-orbit-series/issues/29) | [Issue029](QuandleResearch/Questions/Issue029.lean) | PARTIAL | Concrete UB and source psi generator images; verify extension on sigma and right-action convention against source. |
| [#30](https://github.com/555tery/quandle-orbit-series/issues/30) | [Issue030](QuandleResearch/Questions/Issue030.lean) | PARTIAL | Capital Psi on F_(n+1) encoded directly; literal F_(n-1) in Problem 5.2 conflicts with preceding definition. Source right action converted using inverse automorphisms. |
| [#31](https://github.com/555tery/quandle-orbit-series/issues/31) | [Issue031](QuandleResearch/Questions/Issue031.lean) | PARTIAL | Concrete UP; explicit answer presentation and source audit required. |
| [#32](https://github.com/555tery/quandle-orbit-series/issues/32) | [Issue032](QuandleResearch/Questions/Issue032.lean) | STATEMENT | Source audit and typecheck |
| [#33](https://github.com/555tery/quandle-orbit-series/issues/33) | [Issue033](QuandleResearch/Questions/Issue033.lean) | STATEMENT | Source audit and typecheck |
| [#34](https://github.com/555tery/quandle-orbit-series/issues/34) | [Issue034](QuandleResearch/Questions/Issue034.lean) | PARTIAL | Native quotient for each tower section and isomorphism-invariant target class now defined; finite-prefix scope and normality hypotheses need source audit. An independent description is the requested answer. |
| [#35](https://github.com/555tery/quandle-orbit-series/issues/35) | [Issue035](QuandleResearch/Questions/Issue035.lean) | STATEMENT | Source audit and typecheck |
| [#36](https://github.com/555tery/quandle-orbit-series/issues/36) | [Issue036](QuandleResearch/Questions/Issue036.lean) | PARTIAL | Literal and nonabelian versions separated; check authors' intended scope. |
| [#37](https://github.com/555tery/quandle-orbit-series/issues/37) | [Issue037](QuandleResearch/Questions/Issue037.lean) | PARTIAL | Normalized action and 2-cocycle data and multiplication now explicit; compare source's homological conventions. |
| [#38](https://github.com/555tery/quandle-orbit-series/issues/38) | [Issue038](QuandleResearch/Questions/Issue038.lean) | PARTIAL | Independent structural descriptions required; arbitrary predicates are not solutions. |
| [#39](https://github.com/555tery/quandle-orbit-series/issues/39) | [Issue039](QuandleResearch/Questions/Issue039.lean) | PARTIAL | Restricted central class, canonical quotient, induced map and kernel are explicit; full comparison still to be encoded. |
| [#40](https://github.com/555tery/quandle-orbit-series/issues/40) | [Issue040](QuandleResearch/Questions/Issue040.lean) | PARTIAL | Equality is a candidate relation, not the whole descriptive question. |
| [#41](https://github.com/555tery/quandle-orbit-series/issues/41) | [Issue041](QuandleResearch/Questions/Issue041.lean) | STATEMENT | Source audit and typecheck |
| [#42](https://github.com/555tery/quandle-orbit-series/issues/42) | [Issue042](QuandleResearch/Questions/Issue042.lean) | STATEMENT | Exact issue hypotheses (odd prime, finite abelian kernel and all automorphisms) are encoded; independent source audit and typecheck remain pending. |
| [#43](https://github.com/555tery/quandle-orbit-series/issues/43) | [Issue043](QuandleResearch/Questions/Issue043.lean) | PARTIAL | Concrete FVB and theta images from issue; verify y-generator action and right-action convention against source. |
| [#44](https://github.com/555tery/quandle-orbit-series/issues/44) | [Issue044](QuandleResearch/Questions/Issue044.lean) | PARTIAL | Theorem 3 and Corollary 3 generator matrices transcribed directly from printed p. 12 (arXiv:2010.03162v1); remaining obligation is source-convention/typecheck review, not a kernel solution. |
| [#45](https://github.com/555tery/quandle-orbit-series/issues/45) | [Issue045](QuandleResearch/Questions/Issue045.lean) | PARTIAL | Concrete presentations and both kernel-image subgroups; verify Gauss relations and source projection conventions. |
| [#46](https://github.com/555tery/quandle-orbit-series/issues/46) | [Issue046](QuandleResearch/Questions/Issue046.lean) | PARTIAL | Both GL and SL, actual field hypotheses and entrywise automorphisms, all four propositions; verify dimension restrictions against source. |
| [#47](https://github.com/555tery/quandle-orbit-series/issues/47) | [Issue047](QuandleResearch/Questions/Issue047.lean) | PARTIAL | Concrete GL, actual field hypotheses and entrywise automorphisms; verify dimension restrictions against source. |
| [#48](https://github.com/555tery/quandle-orbit-series/issues/48) | [Issue048](QuandleResearch/Questions/Issue048.lean) | STATEMENT | Source audit and typecheck |
| [#49](https://github.com/555tery/quandle-orbit-series/issues/49) | [Issue049](QuandleResearch/Questions/Issue049.lean) | PARTIAL | Independent structural classification required. |
| [#50](https://github.com/555tery/quandle-orbit-series/issues/50) | [Issue050](QuandleResearch/Questions/Issue050.lean) | PARTIAL | Mathlib GenContFract and capped-base Euler characteristic explicit; geometric Seifert realization, irreducibility and Matveev complexity remain. |
| [#51](https://github.com/555tery/quandle-orbit-series/issues/51) | [Issue051](QuandleResearch/Questions/Issue051.lean) | STATEMENT | Source audit and typecheck |
| [#52](https://github.com/555tery/quandle-orbit-series/issues/52) | [Issue052](QuandleResearch/Questions/Issue052.lean) | STATEMENT | Source audit and typecheck |
| [#53](https://github.com/555tery/quandle-orbit-series/issues/53) | [Issue053](QuandleResearch/Questions/Issue053.lean) | STATEMENT | Source audit and typecheck |
| [#54](https://github.com/555tery/quandle-orbit-series/issues/54) | [Issue054](QuandleResearch/Questions/Issue054.lean) | STATEMENT | Source audit and typecheck |
| [#55](https://github.com/555tery/quandle-orbit-series/issues/55) | [Issue055](QuandleResearch/Questions/Issue055.lean) | STATEMENT | Source audit and typecheck |
| [#56](https://github.com/555tery/quandle-orbit-series/issues/56) | [Issue056](QuandleResearch/Questions/Issue056.lean) | PARTIAL | Fundamental strong biquandle specified by actual crossing relations; geometric virtual knot equivalence and source scope remain. |
| [#57](https://github.com/555tery/quandle-orbit-series/issues/57) | [Issue057](QuandleResearch/Questions/Issue057.lean) | PARTIAL | Fundamental quandle and strong biquandle specified by actual crossing relations; classical realizability and geometric domain remain external. |
| [#58](https://github.com/555tery/quandle-orbit-series/issues/58) | [Issue058](QuandleResearch/Questions/Issue058.lean) | PARTIAL | Embedded surface domain and presentation conditions explicit; smooth/oriented scope and broken-surface diagram correspondence remain. |
| [#59](https://github.com/555tery/quandle-orbit-series/issues/59) | [Issue059](QuandleResearch/Questions/Issue059.lean) | PARTIAL | Concrete Laurent group algebra and Burau matrix images; verify matrix convention and typecheck. |
| [#60](https://github.com/555tery/quandle-orbit-series/issues/60) | [Issue060](QuandleResearch/Questions/Issue060.lean) | PARTIAL | Laurent ring, Artin action and abelianized Fox derivatives characterized by generator values and product rule; matrix convention and existence/typechecking still require audit. |
| [#61](https://github.com/555tery/quandle-orbit-series/issues/61) | [Issue061](QuandleResearch/Questions/Issue061.lean) | PARTIAL | Concrete VP_n; field scope and source-convention audit remain. |
| [#62](https://github.com/555tery/quandle-orbit-series/issues/62) | [Issue062](QuandleResearch/Questions/Issue062.lean) | PARTIAL | Concrete rational function matrix model; group defined by closure, equality with the source matrix set still requires a construction audit. |
| [#63](https://github.com/555tery/quandle-orbit-series/issues/63) | [Issue063](QuandleResearch/Questions/Issue063.lean) | PARTIAL | Concrete quotient and algebraic Bieberbach condition; journal wording and geometric equivalence require audit. |
| [#64](https://github.com/555tery/quandle-orbit-series/issues/64) | [Issue064](QuandleResearch/Questions/Issue064.lean) | PARTIAL | Strong-switch axioms and universal property explicit; descriptive model is the requested answer, not a proof obligation at this stage. |
| [#65](https://github.com/555tery/quandle-orbit-series/issues/65) | [Issue065](QuandleResearch/Questions/Issue065.lean) | PARTIAL | Fundamental strong biquandle specified by actual crossing relations; geometric model and naturality are requested, not asserted. |
| [#66](https://github.com/555tery/quandle-orbit-series/issues/66) | [Issue066](QuandleResearch/Questions/Issue066.lean) | PARTIAL | PartialEquiv-based candidate with preserving/reflecting morphisms. Exact author's admissibility and category remain unspecified. |
| [#67](https://github.com/555tery/quandle-orbit-series/issues/67) | [Issue067](QuandleResearch/Questions/Issue067.lean) | STATEMENT | Source audit and typecheck |
| [#68](https://github.com/555tery/quandle-orbit-series/issues/68) | [Issue068](QuandleResearch/Questions/Issue068.lean) | STATEMENT | Literal Definition 2.20 audited; native enveloping group and eight directions, with Proposition 2.24 already known. |
| [#69](https://github.com/555tery/quandle-orbit-series/issues/69) | [Issue069](QuandleResearch/Questions/Issue069.lean) | PARTIAL | Universal reduced quotient and fundamental quandle presentation specified. Welded link-homotopy and reversed mirror of non-split components in S4 still need geometric encoding. |

Multi-part questions have separate definitions wherever practical. Research directions and literature corrections retain their distinct nature. An open-ended classification or construction problem is not replaced by an existential quantifier over arbitrary predicates and called solved.
