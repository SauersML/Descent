import Lake
open Lake DSL

package calibration where

-- Pin to a specific Mathlib commit for reproducible builds.
  -- Using Aristotle's Mathlib version for compatibility
  require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib Calibrator where
  srcDir := "proofs"
  -- `autoImplicit` turns any unresolved identifier into a fresh implicit
  -- argument, so a mistyped name in a hypothesis becomes a universally
  -- quantified variable and the theorem still compiles while saying nothing
  -- about the quantity it names. This corpus has already recorded one such
  -- incident: see the header of `proofs/Calibrator/CausalInference.lean`,
  -- where 35 unresolved names had silently become implicit parameters.
  leanOptions := #[⟨`autoImplicit, false⟩]
