/-
Stored output for the detectors under `proofs/validation/`.

WHY THIS MODULE EXISTS.  Until now no detector here wrote a file.  Every count
in circulation — 3393, 104, 12, 354, and RflScan's 8 — lived in a commit message
or a docstring and nowhere else, so none could be re-read, re-checked, or dated.
The cost is on the record: three of the nine specimens named in commit 6e47789b
did not exist in the tree that commit describes, which means that result list was
not a transcript of a run, and nothing could have caught it. See
`proofs/validation/inflation/CROSSCHECK.md` §3.

A detector whose output nobody can re-read is not an instrument. Every writer
here stamps the revision it ran against and whether the tree was clean, so a
reader can tell a current result from a stale one WITHOUT trusting the person
quoting it.

Imports only `Lean`, for the same reason as `Shared.DeclFilter`: it must load
before the corpus it reports on.
-/
import Lean

open Lean

namespace Shared.Results

/-- Standard output of a command, or `none` if it could not be run or exited
nonzero.  Never throws: a missing `git` must degrade the provenance stamp to
"unknown", not destroy a measurement that already succeeded. -/
private def capture (cmd : String) (args : Array String) : IO (Option String) := do
  try
    let out ← IO.Process.output { cmd := cmd, args := args }
    if out.exitCode == 0 then return some out.stdout.trim else return none
  catch _ => return none

/-- The revision the detector ran against, or `"unknown"`. -/
def gitRevision : IO String := do
  return (← capture "git" #["rev-parse", "HEAD"]).getD "unknown"

/-- The paths that differed from that revision when the detector ran, or `none`
if git could not answer.

Load-bearing, not decoration.  A result measured over a dirty tree does not
describe the revision it names, and that is exactly how RflScan's "8 of 8" came
to describe a module allow-list the committed file no longer contains.  The
paths themselves are stored, not just a flag, so a reader can see whether the
dirty file was one that could have changed the answer.

The detectors' own JSON outputs are excluded from the check.  When two detectors
run in sequence the first one's write would otherwise make the tree "dirty" for
the second, reporting a corruption that did not happen and training a reader to
ignore the field. -/
def gitDirtyPaths : IO (Option (Array String)) := do
  match ← capture "git" #["status", "--porcelain", "--",
                          ":(exclude)proofs/validation/**/*.json"] with
  | none => return none
  | some s =>
    return some <| (s.splitOn "\n").toArray.filterMap fun line =>
      let line := line.trim
      if line.isEmpty then none else some line

/-- Wall-clock time of the run, UTC, or `null`. -/
def runAt : IO Json := do
  match ← capture "date" #["-u", "+%Y-%m-%dT%H:%M:%SZ"] with
  | none => return Json.null
  | some s => return toJson s

/-- Resolve a repo-relative path against the repository root.

The detectors are invoked as `lake env lean proofs/validation/…`, whose imports
resolve through an absolute `LEAN_PATH` and so do not pin the working directory.
Asking git for the root means the results file lands beside its detector however
the run was launched, rather than wherever the caller happened to be standing. -/
def repoPath (rel : String) : IO System.FilePath := do
  match ← capture "git" #["rev-parse", "--show-toplevel"] with
  | some root => return (System.FilePath.mk root).join (System.FilePath.mk rel)
  | none => return System.FilePath.mk rel

/-- Write a detector's results as JSON, stamped with its provenance.

`fields` is the detector's own payload: its counts and, for every count, the
full list of names behind it.  A total with no members is the failure this
module exists to prevent, so a caller that reports a size must also report the
list of that size. -/
def write (rel : String) (detector : String) (fields : List (String × Json)) : IO Unit := do
  let dirty ← gitDirtyPaths
  let cleanField : Json :=
    match dirty with
    | none => Json.null
    | some ps => toJson ps.isEmpty
  let dirtyField : Json :=
    match dirty with
    | none => Json.null
    | some ps => toJson ps
  let header : List (String × Json) :=
    [ ("detector", toJson detector),
      ("revision", toJson (← gitRevision)),
      ("workingTreeClean", cleanField),
      ("workingTreeDirtyPaths", dirtyField),
      ("runAt", ← runAt) ]
  let path ← repoPath rel
  IO.FS.writeFile path (Json.pretty (Json.mkObj (header ++ fields)) ++ "\n")
  IO.println s!"wrote {path}"

end Shared.Results
