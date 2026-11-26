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

## Coverage

STATEMENT means the principal proposition is expressed using concrete shared definitions, not that source correspondence or typechecking has been verified. PARTIAL means at least one source-specific construction, descriptive component, or convention remains to be encoded or checked. Candidate-answer predicates must be instantiated with independently specified constructions, not tautological restatements.

| Issue | Module | Status | Outstanding |
|---|---|---|---|
| [#1](https://github.com/555tery/quandle-orbit-series/issues/1) | [Issue001](QuandleResearch/Questions/Issue001.lean) | PARTIAL | Profinite topology, Stone-indexed semi-disjoint unions and transfinite construction. |
| [#2](https://github.com/555tery/quandle-orbit-series/issues/2) | [Issue002](QuandleResearch/Questions/Issue002.lean) | STATEMENT | Source audit and typecheck |
| [#3](https://github.com/555tery/quandle-orbit-series/issues/3) | [Issue003](QuandleResearch/Questions/Issue003.lean) | PARTIAL | Construct the specified unitriangular group/quandle family; exact orbit count, central quotient and multipermutation level remain to be encoded. |
| [#4](https://github.com/555tery/quandle-orbit-series/issues/4) | [Issue004](QuandleResearch/Questions/Issue004.lean) | PARTIAL | Actual cocycle and Milnor invariants, coefficients, indeterminacy and meaningful relation; arbitrary relations do not count as answers. |
| [#5](https://github.com/555tery/quandle-orbit-series/issues/5) | [Issue005](QuandleResearch/Questions/Issue005.lean) | PARTIAL | Source convention and rack fibre closure; candidate research direction, not a published theorem. |
| [#6](https://github.com/555tery/quandle-orbit-series/issues/6) | [Issue006](QuandleResearch/Questions/Issue006.lean) | STATEMENT | Source audit and typecheck |
| [#7](https://github.com/555tery/quandle-orbit-series/issues/7) | [Issue007](QuandleResearch/Questions/Issue007.lean) | PARTIAL | Reference family and exact group filtration; this is only one candidate research question. |
| [#8](https://github.com/555tery/quandle-orbit-series/issues/8) | [Issue008](QuandleResearch/Questions/Issue008.lean) | STATEMENT | Source audit and typecheck |
| [#9](https://github.com/555tery/quandle-orbit-series/issues/9) | [Issue009](QuandleResearch/Questions/Issue009.lean) | STATEMENT | Source audit and typecheck |
| [#10](https://github.com/555tery/quandle-orbit-series/issues/10) | [Issue010](QuandleResearch/Questions/Issue010.lean) | PARTIAL | Verify verbal word, indexing and sharpness scope against source. |
| [#11](https://github.com/555tery/quandle-orbit-series/issues/11) | [Issue011](QuandleResearch/Questions/Issue011.lean) | STATEMENT | Source audit and typecheck |
| [#12](https://github.com/555tery/quandle-orbit-series/issues/12) | [Issue012](QuandleResearch/Questions/Issue012.lean) | PARTIAL | An explicit classification model, not a tautological parameterization. |
| [#13](https://github.com/555tery/quandle-orbit-series/issues/13) | [Issue013](QuandleResearch/Questions/Issue013.lean) | STATEMENT | Source audit and typecheck |
| [#14](https://github.com/555tery/quandle-orbit-series/issues/14) | [Issue014](QuandleResearch/Questions/Issue014.lean) | PARTIAL | Check BCNW convention and exact index offsets against source. |
| [#15](https://github.com/555tery/quandle-orbit-series/issues/15) | [Issue015](QuandleResearch/Questions/Issue015.lean) | STATEMENT | Source audit and typecheck |
| [#16](https://github.com/555tery/quandle-orbit-series/issues/16) | [Issue016](QuandleResearch/Questions/Issue016.lean) | PARTIAL | Check residual definition against paper; embeddings encode the iterates without constructing them. |
| [#17](https://github.com/555tery/quandle-orbit-series/issues/17) | [Issue017](QuandleResearch/Questions/Issue017.lean) | PARTIAL | Link-homotopy, actual cocycle invariants and unlink/Brunnian constructions. |
| [#18](https://github.com/555tery/quandle-orbit-series/issues/18) | [Issue018](QuandleResearch/Questions/Issue018.lean) | PARTIAL | Supply an independent classification predicate, not the target predicate itself. |
| [#19](https://github.com/555tery/quandle-orbit-series/issues/19) | [Issue019](QuandleResearch/Questions/Issue019.lean) | PARTIAL | Supply an independent classification predicate, not the target predicate itself. |
| [#20](https://github.com/555tery/quandle-orbit-series/issues/20) | [Issue020](QuandleResearch/Questions/Issue020.lean) | PARTIAL | The dihedral operation, inner group and orbit-preserving condition are explicit; verify the precise QInn convention against the original article. |
| [#21](https://github.com/555tery/quandle-orbit-series/issues/21) | [Issue021](QuandleResearch/Questions/Issue021.lean) | PARTIAL | Universal-arrow specification in the BNS convention; candidate constructions and independent source audit are still required. |
| [#22](https://github.com/555tery/quandle-orbit-series/issues/22) | [Issue022](QuandleResearch/Questions/Issue022.lean) | PARTIAL | Universal-arrow specification for both adjoints in the BNS convention; candidate constructions and independent source audit are still required. |
| [#23](https://github.com/555tery/quandle-orbit-series/issues/23) | [Issue023](QuandleResearch/Questions/Issue023.lean) | PARTIAL | Design constraints only; need a meaningful action, embedding and product structure. |
| [#24](https://github.com/555tery/quandle-orbit-series/issues/24) | [Issue024](QuandleResearch/Questions/Issue024.lean) | PARTIAL | Virtual-switch axioms, canonical twist and invariant construction. |
| [#25](https://github.com/555tery/quandle-orbit-series/issues/25) | [Issue025](QuandleResearch/Questions/Issue025.lean) | PARTIAL | Concrete quotient and distinguished symmetric subgroup now defined; independent order classification and presentation-convention audit remain. |
| [#26](https://github.com/555tery/quandle-orbit-series/issues/26) | [Issue026](QuandleResearch/Questions/Issue026.lean) | PARTIAL | Concrete quotient and algebraic Bieberbach condition; independent subgroup classification and geometric convention audit remain. |
| [#27](https://github.com/555tery/quandle-orbit-series/issues/27) | [Issue027](QuandleResearch/Questions/Issue027.lean) | PARTIAL | Concrete VP_3; field scope and equivalence of kernel-image construction require audit. |
| [#28](https://github.com/555tery/quandle-orbit-series/issues/28) | [Issue028](QuandleResearch/Questions/Issue028.lean) | PARTIAL | Concrete VB and H_n; Psi generator matrices and Laurent ring still required. |
| [#29](https://github.com/555tery/quandle-orbit-series/issues/29) | [Issue029](QuandleResearch/Questions/Issue029.lean) | PARTIAL | Concrete UB and source psi generator images; verify extension on sigma and right-action convention against source. |
| [#30](https://github.com/555tery/quandle-orbit-series/issues/30) | [Issue030](QuandleResearch/Questions/Issue030.lean) | PARTIAL | Concrete UB and psi generator images; verify source's capital Psi convention and integer scope. |
| [#31](https://github.com/555tery/quandle-orbit-series/issues/31) | [Issue031](QuandleResearch/Questions/Issue031.lean) | PARTIAL | Concrete UP; explicit answer presentation and source audit required. |
| [#32](https://github.com/555tery/quandle-orbit-series/issues/32) | [Issue032](QuandleResearch/Questions/Issue032.lean) | STATEMENT | Source audit and typecheck |
| [#33](https://github.com/555tery/quandle-orbit-series/issues/33) | [Issue033](QuandleResearch/Questions/Issue033.lean) | STATEMENT | Source audit and typecheck |
| [#34](https://github.com/555tery/quandle-orbit-series/issues/34) | [Issue034](QuandleResearch/Questions/Issue034.lean) | PARTIAL | Verify tower hypotheses; descriptive question needs independent structural properties, not an arbitrary predicate. |
| [#35](https://github.com/555tery/quandle-orbit-series/issues/35) | [Issue035](QuandleResearch/Questions/Issue035.lean) | STATEMENT | Source audit and typecheck |
| [#36](https://github.com/555tery/quandle-orbit-series/issues/36) | [Issue036](QuandleResearch/Questions/Issue036.lean) | PARTIAL | Literal and nonabelian versions separated; check authors' intended scope. |
| [#37](https://github.com/555tery/quandle-orbit-series/issues/37) | [Issue037](QuandleResearch/Questions/Issue037.lean) | PARTIAL | Construct extension cocycle/action and homological criterion. |
| [#38](https://github.com/555tery/quandle-orbit-series/issues/38) | [Issue038](QuandleResearch/Questions/Issue038.lean) | PARTIAL | Independent structural descriptions required; arbitrary predicates are not solutions. |
| [#39](https://github.com/555tery/quandle-orbit-series/issues/39) | [Issue039](QuandleResearch/Questions/Issue039.lean) | PARTIAL | Construct central quotient, induced automorphism, factor and canonical comparison; current image property is only a component. |
| [#40](https://github.com/555tery/quandle-orbit-series/issues/40) | [Issue040](QuandleResearch/Questions/Issue040.lean) | PARTIAL | Equality is a candidate relation, not the whole descriptive question. |
| [#41](https://github.com/555tery/quandle-orbit-series/issues/41) | [Issue041](QuandleResearch/Questions/Issue041.lean) | STATEMENT | Source audit and typecheck |
| [#42](https://github.com/555tery/quandle-orbit-series/issues/42) | [Issue042](QuandleResearch/Questions/Issue042.lean) | STATEMENT | Exact issue hypotheses (odd prime, finite abelian kernel and all automorphisms) are encoded; independent source audit and typecheck remain pending. |
| [#43](https://github.com/555tery/quandle-orbit-series/issues/43) | [Issue043](QuandleResearch/Questions/Issue043.lean) | PARTIAL | Concrete FVB and theta images from issue; verify y-generator action and right-action convention against source. |
| [#44](https://github.com/555tery/quandle-orbit-series/issues/44) | [Issue044](QuandleResearch/Questions/Issue044.lean) | PARTIAL | Concrete FVB and integral matrix target; Delta generator matrices still required. |
| [#45](https://github.com/555tery/quandle-orbit-series/issues/45) | [Issue045](QuandleResearch/Questions/Issue045.lean) | PARTIAL | Concrete presentations and both kernel-image subgroups; verify Gauss relations and source projection conventions. |
| [#46](https://github.com/555tery/quandle-orbit-series/issues/46) | [Issue046](QuandleResearch/Questions/Issue046.lean) | PARTIAL | Construct GL_n, SL_n, algebraically closed characteristic-zero field and entrywise automorphism sets; check dimension bounds separately. |
| [#47](https://github.com/555tery/quandle-orbit-series/issues/47) | [Issue047](QuandleResearch/Questions/Issue047.lean) | PARTIAL | Construct GL_n and the entrywise automorphisms under the source field hypotheses. |
| [#48](https://github.com/555tery/quandle-orbit-series/issues/48) | [Issue048](QuandleResearch/Questions/Issue048.lean) | STATEMENT | Source audit and typecheck |
| [#49](https://github.com/555tery/quandle-orbit-series/issues/49) | [Issue049](QuandleResearch/Questions/Issue049.lean) | PARTIAL | Independent structural classification required. |
| [#50](https://github.com/555tery/quandle-orbit-series/issues/50) | [Issue050](QuandleResearch/Questions/Issue050.lean) | PARTIAL | Construct Seifert spaces, admissibility, complexity, Euler characteristic and S function. |
| [#51](https://github.com/555tery/quandle-orbit-series/issues/51) | [Issue051](QuandleResearch/Questions/Issue051.lean) | STATEMENT | Source audit and typecheck |
| [#52](https://github.com/555tery/quandle-orbit-series/issues/52) | [Issue052](QuandleResearch/Questions/Issue052.lean) | STATEMENT | Source audit and typecheck |
| [#53](https://github.com/555tery/quandle-orbit-series/issues/53) | [Issue053](QuandleResearch/Questions/Issue053.lean) | STATEMENT | Source audit and typecheck |
| [#54](https://github.com/555tery/quandle-orbit-series/issues/54) | [Issue054](QuandleResearch/Questions/Issue054.lean) | STATEMENT | Source audit and typecheck |
| [#55](https://github.com/555tery/quandle-orbit-series/issues/55) | [Issue055](QuandleResearch/Questions/Issue055.lean) | STATEMENT | Source audit and typecheck |
| [#56](https://github.com/555tery/quandle-orbit-series/issues/56) | [Issue056](QuandleResearch/Questions/Issue056.lean) | PARTIAL | Construct fundamental biquandle and precise equivalence of virtual knots. |
| [#57](https://github.com/555tery/quandle-orbit-series/issues/57) | [Issue057](QuandleResearch/Questions/Issue057.lean) | PARTIAL | Instantiate with classical knots and actual fundamental invariants. |
| [#58](https://github.com/555tery/quandle-orbit-series/issues/58) | [Issue058](QuandleResearch/Questions/Issue058.lean) | PARTIAL | Instantiate with surface knots and actual fundamental invariants. |
| [#59](https://github.com/555tery/quandle-orbit-series/issues/59) | [Issue059](QuandleResearch/Questions/Issue059.lean) | PARTIAL | Concrete B4 and unreduced generator matrices; coefficient ring and canonical Laurent generator still not encoded. |
| [#60](https://github.com/555tery/quandle-orbit-series/issues/60) | [Issue060](QuandleResearch/Questions/Issue060.lean) | PARTIAL | Concrete pure braid group and matrix dimension; Fox derivatives and Laurent coefficients still required. |
| [#61](https://github.com/555tery/quandle-orbit-series/issues/61) | [Issue061](QuandleResearch/Questions/Issue061.lean) | PARTIAL | Concrete VP_n; field scope and source-convention audit remain. |
| [#62](https://github.com/555tery/quandle-orbit-series/issues/62) | [Issue062](QuandleResearch/Questions/Issue062.lean) | PARTIAL | Construct the exact matrix group and translation subgroup of Example 2. |
| [#63](https://github.com/555tery/quandle-orbit-series/issues/63) | [Issue063](QuandleResearch/Questions/Issue063.lean) | PARTIAL | Concrete quotient and algebraic Bieberbach condition; journal wording and geometric equivalence require audit. |
| [#64](https://github.com/555tery/quandle-orbit-series/issues/64) | [Issue064](QuandleResearch/Questions/Issue064.lean) | PARTIAL | Universal property in BNS convention; explicit carrier/operations and source-convention correspondence remain required. |
| [#65](https://github.com/555tery/quandle-orbit-series/issues/65) | [Issue065](QuandleResearch/Questions/Issue065.lean) | PARTIAL | Topological construction and naturality not encoded; pointwise isomorphism is only a component. |
| [#66](https://github.com/555tery/quandle-orbit-series/issues/66) | [Issue066](QuandleResearch/Questions/Issue066.lean) | PARTIAL | Establish author's partial-biquandle category, admissibility, morphisms and generator scope. |
| [#67](https://github.com/555tery/quandle-orbit-series/issues/67) | [Issue067](QuandleResearch/Questions/Issue067.lean) | STATEMENT | Source audit and typecheck |
| [#68](https://github.com/555tery/quandle-orbit-series/issues/68) | [Issue068](QuandleResearch/Questions/Issue068.lean) | PARTIAL | Verify residual nilpotency indexing against Darné v3; known implications are still statements, not proofs. |
| [#69](https://github.com/555tery/quandle-orbit-series/issues/69) | [Issue069](QuandleResearch/Questions/Issue069.lean) | PARTIAL | Construct reduced fundamental quandle and the precise equivalence relation in S^4. |

Multi-part questions have separate definitions wherever practical. Research directions and literature corrections retain their distinct nature. An open-ended classification or construction problem is not replaced by an existential quantifier over arbitrary predicates and called solved.
