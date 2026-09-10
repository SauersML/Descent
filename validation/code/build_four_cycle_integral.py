import os, subprocess, sys, shutil
from pathlib import Path
shared = Path("/projects/standard/hsiehph/sauer354/portability-lean-20260910")
base = Path("/tmp/descent-proof-20260910")
mathlib = base / "mathlib4-f897ebcf72cd16f89ab4577d0c826cd14afaafc7"
project = base / "project"
source = "Descent/Portability/FourCycleIntegratedCorrelation.lean"
shutil.copyfile(str(shared / "FourCycleIntegratedCorrelation.lean"), str(project / source))
env = dict(os.environ)
env["LEAN_PATH"] = ":".join([str(project), str(mathlib / ".lake/build/lib/lean")] + [str(p / ".lake/build/lib/lean") for p in (mathlib / ".lake/packages").iterdir()])
cmd = [str(base / "lean424/bin/lean"), "-j", "2", "-M", "4096", "-DautoImplicit=false", "-DrelaxedAutoImplicit=false", "-o", source[:-5] + ".olean", source]
r = subprocess.run(cmd, cwd=str(project), env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(shared / "four-cycle-integrated-correlation-build.log").write_bytes(r.stdout)
print(r.stdout.decode(), end="")
sys.exit(r.returncode)
