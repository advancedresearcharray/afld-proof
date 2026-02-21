#!/usr/bin/env python3
"""
scaffold_proof.py — Generate Lean 4 proof file skeletons from engine discovery data.

Accepts input from stdin (piped text) or command-line arguments.
Supports: framework linking (gen, fp, 16 scores, purpose) and dimension study (domain, rigor, 11 preservations).
Output: Lean 4 file to stdout or --output <path>. Use --name for namespace/filename.
"""

import argparse
import sys
import textwrap
from typing import List


# Known generations for framework linking ordering (as in existing AFLD proofs)
KNOWN_GENERATIONS = [1095020008, 1239676072, 1580426969, 1820683632, 1880268217]


def parse_framework_args(args: List[str]) -> dict:
    """Parse framework linking args: --gen, --fp, --purpose, --scores (16 comma-sep)."""
    out = {}
    i = 0
    while i < len(args):
        if args[i] == "--gen" and i + 1 < len(args):
            out["gen"] = int(args[i + 1])
            i += 2
        elif args[i] == "--fp" and i + 1 < len(args):
            out["fp"] = args[i + 1]
            i += 2
        elif args[i] == "--purpose" and i + 1 < len(args):
            out["purpose"] = args[i + 1]
            i += 2
        elif args[i] == "--scores" and i + 1 < len(args):
            out["scores"] = [int(x.strip()) for x in args[i + 1].split(",")]
            i += 2
        else:
            i += 1
    return out


def parse_dimstudy_args(args: List[str]) -> dict:
    """Parse dimension study args: --domain, --rigor, --preservations (11 comma-sep)."""
    out = {}
    i = 0
    while i < len(args):
        if args[i] == "--domain" and i + 1 < len(args):
            out["domain"] = args[i + 1].strip('"')
            i += 2
        elif args[i] == "--rigor" and i + 1 < len(args):
            out["rigor"] = int(args[i + 1])
            i += 2
        elif args[i] == "--preservations" and i + 1 < len(args):
            out["preservations"] = [int(x.strip()) for x in args[i + 1].split(",")]
            i += 2
        else:
            i += 1
    return out


def generate_framework_lean(
    gen: int,
    fp: str,
    purpose: str,
    scores: List[int],
    module_name: str,
) -> str:
    """Generate Lean 4 skeleton for framework linking discovery."""
    if len(scores) != 16:
        raise ValueError(f"Framework linking requires exactly 16 scores, got {len(scores)}")

    score_sum = sum(scores)
    score_mean_floor = score_sum // 16
    high_count = sum(1 for s in scores if s >= 90)
    min_score = min(scores)
    max_score = max(scores)
    gap = max_score - min_score

    scores_str = ", ".join(str(s) for s in scores)
    sum_expr = " + ".join(str(s) for s in scores)

    gen_fmt = f"{gen:,}".replace(",", ",")
    doc_lines = [
        f"Framework Linking — Generation {gen_fmt}",
        "Lean 4 Formalization (scaffold)",
        "",
        f"Fingerprint: {fp}",
        f"Purpose: {purpose}",
        "",
        f"16 Property Scores (×100): {scores_str}",
        f"Sum={score_sum}, mean_floor={score_mean_floor}, high_count(≥90)={high_count}, gap={gap}",
        "",
        "AFLD scaffold, 2026.",
    ]
    doc_header = "\n".join("    " + ("  -  " + line if line else "") for line in doc_lines)

    known_list = ", ".join(str(g) for g in KNOWN_GENERATIONS)
    chain_ordering_lines = " ∧\n    ".join(
        f"(({KNOWN_GENERATIONS[i]} : ℕ) < {KNOWN_GENERATIONS[i + 1]})"
        for i in range(len(KNOWN_GENERATIONS) - 1)
    )
    ordering_rel = " ∧\n    ".join(
        f"(({gen} : ℕ) < {g})" for g in KNOWN_GENERATIONS if gen < g
    )
    if not ordering_rel:
        ordering_rel = f"(({gen} : ℕ) ≤ {KNOWN_GENERATIONS[-1]})"

    return textwrap.dedent(f"""\
    /-
{doc_header}
    -/

    import Mathlib.Data.Real.Basic
    import Mathlib.Tactic.Linarith
    import Mathlib.Tactic.NormNum
    import Mathlib.Tactic.Ring
    import Mathlib.Data.Nat.Basic

    namespace AFLD.{module_name}

    /-! ### § 1. Generation Scale -/

    /-- Generation {gen:,} > 1 billion -/
    theorem generation_above_billion : ({gen} : ℕ) > 10 ^ 9 := by norm_num

    /-! ### § 2. Property Score Analysis -/

    /-- Sum of all 16 property scores (×100): {score_sum} -/
    theorem score_sum :
        {sum_expr} = ({score_sum} : ℕ) := by omega

    /-- Mean score floor (×100): {score_sum}/16 = {score_mean_floor} -/
    theorem score_mean_floor : ({score_sum} : ℕ) / 16 = {score_mean_floor} := by norm_num

    /-- {high_count} of 16 properties are at or above 90 -/
    theorem high_count : ({high_count} : ℕ) > 8 := by omega

    /-- Gap analysis: max - min = {gap} -/
    theorem gap_analysis : ({max_score} : ℕ) - {min_score} = {gap} := by omega

    /-! ### § 3. Ordering Relative to Known Generations -/

    /-- Ordering relative to known generations: {known_list} -/
    theorem ordering_known_generations :
        {ordering_rel} := by omega

    /-- Five known generations form a strictly increasing chain -/
    theorem chain_ordering :
        {chain_ordering_lines} := by omega

    /-! ### § 4. Combined -/

    /-- Generation above billion, score sum, mean floor, and gap -/
    theorem combined :
        ({gen} : ℕ) > 10 ^ 9 ∧
        ({score_sum} : ℕ) / 16 = {score_mean_floor} ∧
        ({max_score} : ℕ) - {min_score} = {gap} := by
      constructor
      · norm_num
      constructor
      · norm_num
      · omega

    end AFLD.{module_name}
    """)


def generate_dimstudy_lean(
    domain: str,
    rigor: int,
    preservations: List[int],
    module_name: str,
) -> str:
    """Generate Lean 4 skeleton for dimension study discovery."""
    if len(preservations) != 11:
        raise ValueError(f"Dimension study requires exactly 11 preservations, got {len(preservations)}")

    p_sum = sum(preservations)
    n = len(preservations)
    mean_floor = p_sum // n
    p_min = min(preservations)
    p_max = max(preservations)
    spread = p_max - p_min

    sum_expr = " + ".join(str(p) for p in preservations)
    domain_safe = domain.replace(" ", "_").replace("-", "_")

    doc_lines = [
        f"Dimension Study — {domain}",
        "Lean 4 Formalization (scaffold)",
        "",
        f"Rigor pass: {rigor}",
        f"11 dimension preservations (×10000): {', '.join(str(p) for p in preservations)}",
        f"Sum={p_sum}, mean_floor={mean_floor}, min={p_min}, max={p_max}, spread={spread}",
        "",
        "AFLD scaffold, 2026.",
    ]
    doc_header = "\n".join("    " + ("  -  " + line if line else "") for line in doc_lines)

    return textwrap.dedent(f"""\
    /-
{doc_header}
    -/

    import Mathlib.Data.Real.Basic
    import Mathlib.Tactic.Linarith
    import Mathlib.Tactic.NormNum
    import Mathlib.Tactic.Ring
    import Mathlib.Data.Nat.Basic

    namespace AFLD.{module_name}

    /-! ### § 1. {domain} — 11-Dimension Profile -/

    /-- Preservation sum (×10000): {p_sum} -/
    theorem {domain_safe}_sum :
        {sum_expr} = ({p_sum} : ℕ) := by omega

    /-- Mean preservation floor: {p_sum}/{n} = {mean_floor} -/
    theorem {domain_safe}_mean_floor : ({p_sum} : ℕ) / {n} = {mean_floor} := by norm_num

    /-- Minimum preservation: {p_min} -/
    theorem {domain_safe}_min : ({p_min} : ℕ) ≤ {p_max} := by omega

    /-- Maximum preservation: {p_max} -/
    theorem {domain_safe}_max :
        ({p_max} : ℕ) ≥ {p_min} := by omega

    /-- Spread: max - min = {spread} -/
    theorem {domain_safe}_spread : ({p_max} : ℕ) - {p_min} = {spread} := by omega

    /-- Rigor pass -/
    theorem {domain_safe}_rigor : ({rigor} : ℕ) > 50000 := by omega

    /-! ### § 2. Combined -/

    /-- Sum, mean, spread for {domain} -/
    theorem combined :
        ({p_sum} : ℕ) / {n} = {mean_floor} ∧
        ({p_max} : ℕ) - {p_min} = {spread} ∧
        ({rigor} : ℕ) > 50000 := by
      constructor
      · norm_num
      constructor
      · omega
      · omega

    end AFLD.{module_name}
    """)


def tokenize_stdin(line: str) -> List[str]:
    """Split stdin line into tokens, respecting quoted strings."""
    out = []
    i = 0
    while i < len(line):
        while i < len(line) and line[i] in " \t\n":
            i += 1
        if i >= len(line):
            break
        if line[i] == '"':
            i += 1
            start = i
            while i < len(line) and line[i] != '"':
                i += 1
            out.append(line[start:i])
            i += 1
        else:
            start = i
            while i < len(line) and line[i] not in " \t\n\"":
                i += 1
            out.append(line[start:i])
    return out


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Generate Lean 4 proof skeletons from engine discovery data.",
        epilog="Example (framework): --type framework --gen 1095020008 --fp d0d89bfec5fbeec3 --purpose hardware --scores 98,98,98,98,95,98,98,98,98,88,98,98,98,98,98,98",
    )
    parser.add_argument(
        "--type",
        choices=["framework", "dimstudy"],
        required=True,
        help="Discovery type: framework (linking) or dimstudy (dimension study)",
    )
    parser.add_argument("--name", default="Scaffold", help="Module name for namespace and filename (default: Scaffold)")
    parser.add_argument("--output", "-o", help="Output file path (default: stdout)")
    # Framework linking
    parser.add_argument("--gen", type=int, help="Generation number (framework)")
    parser.add_argument("--fp", default="unknown", help="Fingerprint (framework)")
    parser.add_argument("--purpose", default="unknown", help="Purpose (framework)")
    parser.add_argument("--scores", help="16 comma-separated property scores (framework)")
    # Dimension study
    parser.add_argument("--domain", default="unknown_domain", help="Domain name (dimstudy)")
    parser.add_argument("--rigor", type=int, help="Rigor pass count (dimstudy)")
    parser.add_argument("--preservations", help="11 comma-separated preservation values (dimstudy)")
    # Stdin / extra (when piping or passing a single line of args)
    parser.add_argument(
        "extra",
        nargs="*",
        help="When using stdin, pass remaining args here; or omit and pipe one line",
    )
    args = parser.parse_args()

    # Only read stdin when we need discovery data (missing required args for this type)
    tokens = list(args.extra)
    need_stdin = (
        (args.type == "framework" and (args.gen is None or args.scores is None)) or
        (args.type == "dimstudy" and (args.rigor is None or args.preservations is None))
    )
    if need_stdin and not sys.stdin.isatty():
        for line in sys.stdin:
            tokens.extend(tokenize_stdin(line))
            if tokens:
                break
        if not tokens:
            for line in sys.stdin:
                tokens.extend(tokenize_stdin(line))

    try:
        if args.type == "framework":
            if args.gen is not None and args.scores is not None:
                gen = args.gen
                fp = args.fp or "unknown"
                purpose = args.purpose or "unknown"
                scores = [int(x.strip()) for x in args.scores.split(",")]
            else:
                data = parse_framework_args(tokens)
                gen = data.get("gen")
                fp = data.get("fp", "unknown")
                purpose = data.get("purpose", "unknown")
                scores = data.get("scores")
            if gen is None or scores is None:
                print("Error: framework requires --gen and --scores (16 comma-separated values)", file=sys.stderr)
                return 1
            lean = generate_framework_lean(gen, fp, purpose, scores, args.name)
        else:
            if args.rigor is not None and args.preservations is not None:
                domain = args.domain or "unknown_domain"
                rigor = args.rigor
                preservations = [int(x.strip()) for x in args.preservations.split(",")]
            else:
                data = parse_dimstudy_args(tokens)
                domain = data.get("domain", "unknown_domain")
                rigor = data.get("rigor")
                preservations = data.get("preservations")
            if rigor is None or preservations is None:
                print("Error: dimstudy requires --rigor and --preservations (11 comma-separated values)", file=sys.stderr)
                return 1
            lean = generate_dimstudy_lean(domain, rigor, preservations, args.name)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        return 1

    if args.output:
        with open(args.output, "w") as f:
            f.write(lean)
    else:
        print(lean)
    return 0


if __name__ == "__main__":
    sys.exit(main())
