# YesMetaZFC

[中文](README.md) | [English](README.en.md)

**Toward a general-purpose platform for set theory research in Lean 4.**

YesMetaZFC develops formalized first-order logic, set theory, and metamathematics.
Its long-term goal is a shared foundation for set theory research: reusable object-language
syntax, formal derivations, model semantics, and proof automation on which further results
and constructions can build. The project uses the Lean / Std libraries supplied with its
toolchain and declares no external Lake package dependencies.

## Current results

The project includes concrete metamathematical results for ZFC in the pure membership
language, with equality and logical symbols. ZFC is represented by `PureModel.theory`,
and provability uses the project's ordinary `Derives` relation.

| Result | Source entry point | Assumptions and scope |
| --- | --- | --- |
| Native small-graph model and consistency | [SmallGraph/ZFC](YesMetaZFC/Model/SmallGraph/ZFC.lean): `sg_models_zfc`, `zfc_consistent` | Constructs a model of the original ZFC axioms from well-founded pointed graphs modulo bisimulation and proves consistency in Lean's metatheory, without a model-existence or consistency assumption. |
| Rosser independence | [PureRosserComplete](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureRosserComplete.lean): `PureRosser.independent` | Assuming ZFC is consistent, a specific pure sentence and its negation are both unprovable. |
| Derivability conditions D1–D3 | [PureProvability](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureProvability.lean): `necessitation_m`, `distribution_m`, `introspection_m` | For arbitrary pure sentences; no consistency or standard-model assumption. |
| Löb's theorem | [PureLoeb](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureLoeb.lean): `PureProvability.loeb_axiom_m`, `loeb_m` | Includes the internal formula and the rule, using an established fixed-point construction. |
| Gödel's second incompleteness theorem | [PureSecondIncompleteness](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureSecondIncompleteness.lean): `PureProvability.second_incompleteness_m` | Assuming ZFC is consistent, it cannot prove the consistency sentence associated with the represented provability predicate. |
| Fixed points with finite parameters | [PureFixedPoint](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureFixedPoint.lean): `fixed_point_m` | Uses the complete AST code of the resulting pure formula itself. |
| Tarski undefinability | [PureTarski](YesMetaZFC/Logic/FirstOrder/FormalSystem/Metatheory/ProofT/ZFC/PureTarski.lean): `undefinable_syntax_m`, `undefinable_parameters_m` | The syntactic version assumes consistency. The semantic version covers every ZFC model and finite parameter assignment, for all pure open formulas in the same parameter context. |

The provability predicate retains the source quotation and proof checker through the
pure-language translation. The fixed-point and Tarski results also provide a separate
encoding of the final pure formulas themselves. Precise statements and encoding conventions
are recorded in [TROPHIES.md](markdown/TROPHIES.md) and [NAT_DECODING.md](markdown/NAT_DECODING.md).

## Explore the infrastructure

Repository guides other than README files are collected in [markdown/](markdown/).

The existing development connects typed syntax and substitution, formal proof systems,
set-theoretic definitions, model interpretations, internal proof coding, and automation.
These interfaces support the current results and the broader research-platform goal.

| Interest | Start here |
| --- | --- |
| Mathematical results and exact hypotheses | [TROPHIES.md](markdown/TROPHIES.md) |
| Reusable proof interfaces and `prove_auto` automation | [ENGINEERING.md](markdown/ENGINEERING.md) |
| Natural-number proof certificates, quotation, and complete AST coding | [NAT_DECODING.md](markdown/NAT_DECODING.md) |
| Definitions, internal recursion, and staged extensions | [ELIMINATION.md](markdown/ELIMINATION.md) |
| Axiom coverage, model correspondence, and recorded dependency audits | [UNIFIED_VERIFICATION.md](markdown/UNIFIED_VERIFICATION.md) |
| Source recovery and toolchain setup | [RESTORE.md](markdown/RESTORE.md) |
| Development conventions | [AGENTS.md](markdown/AGENTS.md), [ProofNaming.md](markdown/ProofNaming.md) |

The detailed guides are currently mainly in Chinese; the source links above identify
the relevant declarations directly. The platform remains under active development.

## Build

The pinned toolchain is **Lean 4.33.1**; see [lean-toolchain](lean-toolchain).
With Git and Lean's toolchain manager installed:

```bash
git clone https://github.com/lanxinge/YesMetaZFC.git
cd YesMetaZFC
lake --wfail build
```

For the full source check, including independent modules outside the default import graph
and the proof-scanning tool, use Python 3.11 or later:

```bash
python scripts/lean_cache.py build
```

Warnings cause these checks to fail. Recorded validation runs and their scope are documented
in [UNIFIED_VERIFICATION.md](markdown/UNIFIED_VERIFICATION.md) and
[PROOF_REDUCTION.md](markdown/PROOF_REDUCTION.md).

## Prebuilt caches

After installing the toolchain, run `python scripts/lean_cache.py get` from a checkout of
the desired commit. Use `python scripts/lean_cache.py get --kind full` to include native
static and shared libraries and the proof-scanning executable.

CI builds separate Linux x86-64/ARM64, Windows x86-64, and macOS Intel/Apple Silicon caches.
Successful main-branch builds publish a complete set in a release named `cache-<commit>`.
The downloader checks the source fingerprint, exact Lean version, platform, and SHA-256,
then verifies that all corresponding targets are ready without rebuilding.
Python 3.11+ is required; no third-party Python packages are needed.
See [CACHE.md](markdown/CACHE.md) for supported environments and offline restoration.

## Get involved

Contributions can help make the existing infrastructure easier to use for further research:
English documentation, focused entry-point guides, reusable model and coding interfaces,
and improvements to proof automation and checking performance.

For a concrete question or proposed contribution, identify the relevant declaration or
module in a [GitHub issue](https://github.com/lanxinge/YesMetaZFC/issues).

## License

Original project code and accompanying documentation are licensed under the
[Apache License 2.0](LICENSE). See [NOTICE](NOTICE) for attribution.
Separately identified third-party material retains its original license.
