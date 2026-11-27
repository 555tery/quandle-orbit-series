"""Generate exact comparator targets from the strict #print axioms audit.

For this unfinished proof, compare the module to itself: this is a
sandboxed six-kernel replay of its audited declarations, NOT independent
verification of the mathematical specification of the final theorem.
No challenge-only axioms or proof holes are introduced.
"""
import argparse
import json
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("scope", choices=["local", "geometry"])
parser.add_argument("output", type=Path)
args = parser.parse_args()

root = Path("QuandleResearch/Proofs/Kourovka88a")
local_sources = [Path("QuandleResearch/Questions/Issue070.lean"),
                 *(root / (name + ".lean")
                   for name in ("Greedy", "Words", "Heights", "WeightedGreedy"))]
geometry = Path("Experiments/Kourovka88aGeometry.lean")
audit = Path("QuandleResearch/Checks/Kourovka88aAudit.lean")
sources = local_sources if args.scope == "local" else [geometry]
audit = audit if args.scope == "local" else geometry
module = ".".join(audit.with_suffix("").parts)
kinds = {}
for path in sources:
    for kind, name in re.findall(
        r"^(?:@\[[^\]\n]*\]\s*)?(?:(?:noncomputable|protected|private|local)\s+)*"
        r"(theorem|lemma|def|abbrev|instance)\s+(\w+)", path.read_text(), re.M
    ):
        if name in kinds:
            raise SystemExit("Duplicate declaration: " + name)
        # Lean elaborates Prop-valued instances as theorems.
        # The two current named instances prove subgroup normality.
        if kind == "instance":
            assert name in {"stageNormal", "adjoinNormal"}, (
                "Classify new instance by its kernel declaration kind", name)
            kind = "theorem"
        kinds[name] = kind
names = re.findall(r"^#print axioms (\w+)\s*$", audit.read_text(), re.M)
assert names and len(names) == len(set(names)), "Missing or duplicate audit names"
assert set(names) == set(kinds), (
    "Audit/source mismatch", sorted(set(kinds) - set(names)),
    sorted(set(names) - set(kinds))
)
qualified = lambda name: "QuandleResearch.Issue070." + name
config = {
    "challenge_module": module,
    "solution_module": module,
    "theorem_names": [qualified(n) for n in names if kinds[n] in ("theorem", "lemma")],
    "definition_names": [qualified(n) for n in names if kinds[n] not in ("theorem", "lemma")],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
}
args.output.write_text(json.dumps(config, indent=2) + "\n")
print(f"Paranoid replay targets: {len(names)} ({args.scope})")
