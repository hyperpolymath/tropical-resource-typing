<!--
SPDX-License-Identifier: CC-BY-SA-4.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> (hyperpolymath)
-->

# Changelog

All notable changes to `tropical-resource-typing` will be documented in this file.

This file is generated from conventional commits by the
[`changelog-reusable.yml`](https://github.com/hyperpolymath/standards/blob/main/.github/workflows/changelog-reusable.yml)
workflow (`hyperpolymath/standards#206`). Adopt the workflow in this repo's CI to keep this file in sync automatically — see
[`templates/cliff.toml`](https://github.com/hyperpolymath/standards/blob/main/templates/cliff.toml)
for the canonical config.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/);
this project aims to follow [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- feat(lean4): bridge the two original twins onto the resource-grade axis (`Resource.Bridge`) — max-plus session grading shown resource-algebra-structured (`grade_spec_par = ⊞`, `grade_send = val 1 ⊠ ·`) with the QTT refinement restated in the resource order (`grade_le_sequential`); the bounded bottleneck algebra embedded into `Resource.Instances.MinMax`, with `embed_tcZero_ne_zero` exposing the finite-`∞` approximation and `hub_ceiling_le` restating `hub_ceiling` in `⊑`. Closes the standing "construct a functor / state the QTT quotient morphism" open items
- feat(lean4): add the **resource-grade axis** — `Resource.*` library exporting a reusable resource-algebra interface (`ResourceSemiring` + ordered `ResourceAlgebra`, no Mathlib), the canonical dioid-order builder, concrete instances (Linear/Affine `{0,1,ω}`, MaxPlus, MinPlus, MinMax), and the parametric transport theorem `parametric_resource_transport` (alias `resource_laws_sufficient_for_consumers`) over `ConsumerLawBundle`; aggregator `Resource.lean`; `lake build` green, new theorems depend only on propext/Quot.sound (or nothing)
- feat(lean4): prove tropical carriers are infinite (`Resource.Stress`: `infinite_maxPlus/minPlus/minMax`) — the infinite-carrier stress test that the abstraction is not a finite `{0,1,ω}` reification
- feat(lean4): add `Resource.EchoBridge` — abstract `ResidueMeasure` showing a resource algebra may measure (opaque) Echo residues, direction `E → R`, with a compiling max-plus witness; no `echo-types` dependency
- docs: add `FOUNDATION_CONTRACT.md`, `docs/RESOURCE-ALGEBRA.adoc`, `docs/ECHO-RESIDUE-BRIDGE.adoc` (resource grade vs resource algebra vs tropical instance vs residue measure; the "tropical is not Echo" boundary invariant)
- ci(lean4): extend `lean.yml` axiom audit to the new `Resource.*` headline theorems and instances
- feat(lean4): migrate the min-max transport semiring (TropicalAdapterPath) in beside the max-plus twin; pin Lean 4.13.0 via lean-toolchain; add lakefile + lake-manifest; `lake build` green
- feat(lean4): prove the De Morgan duality bridge — dualGrade_invol, dual_tcAdd_is_max (dual of min = max), dual_tcMul_is_min (dual of max = min)
- docs(lean4): add docs/LEAN-FORMALIZATION.adoc (authoritative Lean reference: build/verify recipe, theorem index, axiom audit, provenance) + README section
- ci(lean4): add lean.yml — lake build + axiom audit (propext/Quot.sound only, no sorry) on push/PR
- feat(isabelle): close all sorries in Tropical_Kleene and Tropical_Matrices_Clean
- feat(isabelle): close all sorries in Tropical_CNO.thy
- feat(determinants): add Tropical_Determinants.thy — optimal assignment theorem
- feat(isabelle): close bellman_ford OFFICIAL SORRY 2 — min-plus Bellman-Ford proved
- feat(isabelle): extend Tropical_Matrices_Full.thy
- feat(afp): create AFP submission files for Tropical_Semirings
- feat(isabelle): recover Tropical_Matrices_Full, Kleene, CNO, and Clean
- feat(isabelle,lean4): recover Tropical_v2.thy and TropicalSessionTypes.lean v6.0
- feat(lean4): add tropical session types formalisation
- feat(isabelle): add verified tropical semiring formalisation

### Fixed

- fix(lean4): repair TropicalSessionTypes + TropicalAdapterPath to compile clean under core Lean 4.13.0 — import ordering, Mathlib-only `push_neg`→core tactics, `AdapterPath` def→abbrev, local `One` shim (4.13.0 core lacks One), `pathCost_append`/`pathCost_le_sequential` reproved; the inherited "Verified" headers were never true
- fix(lean4): replace the FALSE `dual_tcMul_bounded` (`dual(max m n)=dual m+dual n−maxGrade`, wrong at m=1,n=2) with the correct De Morgan dual `dual_tcMul_is_min`
- fix(ci): sync hypatia-scan.yml to canonical (413: env.HOME+Phase-2+SARIF) (#1)
- fix(Tropical_Semirings): close all 16 sites + ~10 doc drifts — session GREEN under Isabelle 2025-1
- fix(Tropical_CNO): close 4 more sites — triangle NegInf cases, CNO close conditional, ge_id 1=Fin0
- fix(Tropical_Semirings): close most CNO drift, hoist sum_le_const + trop_mat_pow_n_le_star
- fix(Tropical_Semirings): close Det/Kleene/Matrices/CNO regressions, add ordered_ab_semigroup_add
- fix(Tropical_Determinants): close type-class regression at 153/207
- fix(matrices): close cycle-excise root + use-before-define + 5 supporting fixes
- fix(isabelle2025): Permutations import + less_tropical definition fixes

### Documentation

- docs(lean4): note that docs/FORMAL-PROOFS.adoc's code listings predate the v6.0 source (illustrative API); point to LEAN-FORMALIZATION.adoc as authoritative
- docs(swarm): SWARM-SESSION 2026-04-26 + 6a2 sextet completion + STATE update
- docs(afp): update HANDOVER_v2 — all sorries closed, AFP submission ready
- docs: add arXiv paper outline for Rigorous Tropical Session Types
- docs: add TROPICAL-ESTATE-MAP.adoc
- docs(ecosystem): add ECOSYSTEM.a2ml with pipeline and tropical connection
- docs: add HANDOVER_v2.adoc from Claude.ai session
- docs: add formal proof document and handover guide
- docs: add TOPOLOGY.md
- docs: substantive CRG C annotation (EXPLAINME.adoc)

## Pre-history

Prior commits to this file's introduction are recorded in git history but not formally classified into Keep-a-Changelog sections. To backfill, run `git cliff -o CHANGELOG.md` locally using the canonical [`cliff.toml`](https://github.com/hyperpolymath/standards/blob/main/templates/cliff.toml) — this is one-shot mechanical work.

---

<!-- This file was seeded by the 2026-05-26 estate tech-debt audit follow-up (Row-2 Phase 3); see [`hyperpolymath/standards/docs/audits/2026-05-26-estate-documentation-debt.md`](https://github.com/hyperpolymath/standards/blob/main/docs/audits/2026-05-26-estate-documentation-debt.md). -->
