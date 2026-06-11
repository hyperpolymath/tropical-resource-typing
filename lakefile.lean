-- SPDX-License-Identifier: MPL-2.0
-- SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

import Lake
open Lake DSL

/-- Pure core Lean 4 proofs (no Mathlib dependency).
    Toolchain is pinned to `leanprover/lean4:v4.13.0` in `lean-toolchain`. -/
package «tropical-resource-typing» where

@[default_target]
lean_lib Tropical where
  srcDir := "."
  -- The two order-reversing twins: max-plus session grading and the
  -- min-max (bottleneck) transport semiring.
  roots := #[`TropicalSessionTypes, `TropicalAdapterPath]
