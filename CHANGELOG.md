<!--
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)
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

- fix(ci): sync hypatia-scan.yml to canonical (413: env.HOME+Phase-2+SARIF) (#1)
- fix(Tropical_Semirings): close all 16 sites + ~10 doc drifts — session GREEN under Isabelle 2025-1
- fix(Tropical_CNO): close 4 more sites — triangle NegInf cases, CNO close conditional, ge_id 1=Fin0
- fix(Tropical_Semirings): close most CNO drift, hoist sum_le_const + trop_mat_pow_n_le_star
- fix(Tropical_Semirings): close Det/Kleene/Matrices/CNO regressions, add ordered_ab_semigroup_add
- fix(Tropical_Determinants): close type-class regression at 153/207
- fix(matrices): close cycle-excise root + use-before-define + 5 supporting fixes
- fix(isabelle2025): Permutations import + less_tropical definition fixes

### Documentation

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
