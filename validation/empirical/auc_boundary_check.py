#!/usr/bin/env python3
"""Class F: does the equal-variance Gaussian AUC survive its own boundary?

Body under test, identical in both copies:

    gaussianAUC v w = Phi (sqrt (v / (2 * w)))

The claim to test is about the attainable boundary w = 0, perfect prediction.
Lean's division is total and `x / 0 = 0`, so the argument does not diverge
there; it lands on 0. The question this asks with numbers:

  (1) What does the formula return at w = 0, and what is the limit as w -> 0+?
  (2) Is the defect a property of Phi, or of the argument?  Repeat with several
      monotone increasing f in place of Phi.  If every one of them is wrong in
      the same direction, the defect is upstream of Phi and no numeric
      stand-in for the Gaussian CDF is implicated.
  (3) Is the LIMIT the right answer?  Monte-Carlo the underlying two-Gaussian
      model and compare, so the grading is against a simulated observable
      rather than against another formula.
"""
import math, random

# ---------- the pieces ----------

def Phi(z):
    return 0.5 * (1.0 + math.erf(z / math.sqrt(2.0)))

def lean_div(a, b):
    """Lean's total division: junk value 0 at a zero denominator."""
    return 0.0 if b == 0.0 else a / b

def auc_body(v, w, f=Phi):
    """The body under test, with the Gaussian CDF swappable."""
    return f(math.sqrt(lean_div(v, 2.0 * w)))

# monotone increasing, each mapping [0, inf) into a bounded range, chance at 0
MONOTONE = {
    "Phi              ": Phi,
    "logistic         ": lambda z: 1.0 / (1.0 + math.exp(-z)),
    "tanh-shifted     ": lambda z: 0.5 * (1.0 + math.tanh(z)),
    "z/(1+z) shifted  ": lambda z: 0.5 * (1.0 + z / (1.0 + z)),
}

def empirical_auc(v, w, n=200000, seed=11):
    """P(score_case > score_control) for two equal-variance normals whose
    separation gives signal variance v against noise variance w."""
    rng = random.Random(seed)
    sd = math.sqrt(w)
    dprime = math.sqrt(v / w)          # separation in noise units
    wins = 0
    for _ in range(n):
        case = dprime * sd + rng.gauss(0.0, sd)
        ctrl = rng.gauss(0.0, sd)
        if case > ctrl:
            wins += 1
        elif case == ctrl:
            wins += 0.5
    return wins / n

# ---------- (1) the boundary ----------

V = 1.0
print("(1) approach to the attainable boundary w = 0, at vSignal = 1")
print(f"    {'vNoise':>12}  {'argument v/(2w)':>18}  {'sqrt':>12}  {'AUC = Phi(sqrt)':>16}")
for w in [1e0, 1e-1, 1e-2, 1e-4, 1e-8, 1e-12, 1e-16, 0.0]:
    arg = lean_div(V, 2.0 * w)
    tag = "   <-- BOUNDARY" if w == 0.0 else ""
    print(f"    {w:12.0e}  {arg:18.6g}  {math.sqrt(arg):12.6g}  {auc_body(V, w):16.6f}{tag}")

lim = 1.0
at0 = auc_body(V, 0.0)
print(f"\n    limit as w -> 0+ : {lim:.6f}   (perfect discrimination)")
print(f"    value AT w = 0   : {at0:.6f}   (chance discrimination)")
print(f"    gap              : {abs(lim - at0):.6f}")
print(f"    range of AUC     : [0.5, 1.0]  -> the returned value sits at the")
print(f"                       OPPOSITE END of the range from the limit.")

# ---------- (2) is Phi implicated? ----------

print("\n(2) same boundary with Phi replaced by other monotone increasing maps")
print(f"    {'f':<18}  {'f at w=1e-12':>14}  {'f AT w=0':>12}  {'wrong?':>8}")
for name, f in MONOTONE.items():
    near = auc_body(V, 1e-12, f)
    at_b = auc_body(V, 0.0, f)
    print(f"    {name:<18}  {near:14.6f}  {at_b:12.6f}  {'YES' if at_b < near else 'no':>8}")
print("    The argument itself jumps from divergent to 0, so every monotone f")
print("    is wrong in the same direction. The defect is upstream of Phi and no")
print("    numeric stand-in for the Gaussian CDF is implicated.")

# ---------- (3) is the limit the right answer? ----------

print("\n(3) Monte-Carlo of the underlying two-Gaussian model, vSignal = 1")
print(f"    {'vNoise':>10}  {'formula':>10}  {'simulated':>10}  {'abs diff':>10}")
for w in [1.0, 0.25, 0.04, 0.01, 0.0025]:
    pred = auc_body(V, w)
    sim = empirical_auc(V, w)
    print(f"    {w:10.4f}  {pred:10.6f}  {sim:10.6f}  {abs(pred - sim):10.6f}")
print("    Away from the boundary the body tracks the simulated observable, so")
print("    the formula is right and only its boundary value is wrong: the limit")
print("    is the correct answer there, and the returned value contradicts it.")
