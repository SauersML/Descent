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

-- The generated-declaration filter and the results writer that the detectors
-- under `proofs/validation/` share.  A separate library, and deliberately not
-- part of `Calibrator`:
--   * the detectors `import Calibrator`, so anything they import must be able to
--     build BEFORE the corpus does -- these two modules import only `Lean`;
--   * a proof module must not be able to import its own auditor, which putting
--     them under the `Calibrator` root would permit.
-- A default target so a plain `lake build` produces the oleans the detectors
-- import.  A build that names its targets must name this one too:
--   lake build Calibrator ValidationShared
@[default_target]
lean_lib ValidationShared where
  srcDir := "proofs/validation"
  roots := #[`Shared.DeclFilter, `Shared.Results]
  leanOptions := #[⟨`autoImplicit, false⟩]
