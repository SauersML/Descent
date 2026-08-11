/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lake

/-!
# Descent build configuration

Defines the proof library and validation executables against a pinned Mathlib revision.
-/

open Lake DSL

package descent where

-- Pin to a specific Mathlib commit for reproducible builds.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "f897ebcf72cd16f89ab4577d0c826cd14afaafc7"

@[default_target]
lean_lib Descent where
  srcDir := "."
  -- `autoImplicit` turns any unresolved identifier into a fresh implicit
  -- argument, so a mistyped name in a hypothesis becomes a universally
  -- quantified variable and the theorem still compiles while saying nothing
  -- about the quantity it names. This corpus has already recorded one such
  -- incident: see the header of `Descent/Foundations/CausalInference.lean`,
  -- where 35 unresolved names had silently become implicit parameters.
  -- `relaxedAutoImplicit` is the second half of the same hazard and was left on.
  -- With `autoImplicit` off, Lean still auto-binds a SINGLE-LETTER unresolved
  -- identifier, and single letters are exactly what this corpus's hypotheses are
  -- named: `h`, `t`, `d`, `m`, `p`. A mistyped `hd` is caught; a mistyped `d` was
  -- not. Turning it off costs nothing a corpus with `autoImplicit := false`
  -- already pays and closes the case the incident in
  -- `Descent/Foundations/CausalInference.lean` is a record of.
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- Deliberately-wrong declarations, kept out of the corpus proper.  A body that
-- asserts nothing about the world is not a law, and a reader who meets one inside
-- `Descent/` has to be warned off it every time; Mathlib keeps `Counterexamples`
-- separate for the same reason.  These modules `import Descent`, so they are built
-- and type-checked with everything else, and they sit outside the reach of
-- `validation/code/check.py`, which scans `Descent/` only -- which is the point:
-- the guards enforce properties of production laws, and none of them should be
-- asked to hold of a body kept precisely because it is false.
-- A build that names its targets must name this one too:
--   lake build Descent Counterexamples ValidationShared
@[default_target]
lean_lib Counterexamples where
  srcDir := "."
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

-- The generated-declaration filter and the results writer that the detectors
-- under `validation/` share.  A separate library, and deliberately not
-- part of `Descent`:
--   * the detectors `import Descent`, so anything they import must be able to
--     build BEFORE the corpus does -- these two modules import only `Lean`;
--   * a proof module must not be able to import its own auditor, which putting
--     them under the `Descent` root would permit.
-- A default target so a plain `lake build` produces the oleans the detectors
-- import.  A build that names its targets must name this one too:
--   lake build Descent ValidationShared
@[default_target]
lean_lib ValidationShared where
  srcDir := "validation"
  roots := #[`Shared.DeclFilter, `Shared.Results]
  leanOptions := #[⟨`autoImplicit, false⟩]
