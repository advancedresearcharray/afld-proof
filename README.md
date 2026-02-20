# AFLD Proof — Machine-Verified Properties of Dimensional Folding

Formal proofs in **Lean 4** (with Mathlib) for the mathematical foundations of
lossless dimensional folding, as implemented in
[libdimfold](https://github.com/djdarmor/libdimfold).

**76+ theorems. Zero `sorry`. Zero axioms. Fully machine-verified.**

## What This Proves

| Result | File | Status |
|--------|------|--------|
| Fermat bridge is a perfect bijection | `FermatBridge.lean` | Proved |
| Cyclic Preservation Theorem | `CyclicPreservation.lean` | Proved |
| 85% ceiling on signed data folding | `SignedFoldingCeiling.lean` | Proved |
| Ceiling bypassed by cyclic encoding | `SignedFoldingCeiling.lean` | Proved |
| Fold destroys exactly n dimensions | `InformationLoss.lean` | Proved |
| n < 2^n dimensional gap | `DimensionalSeparation.lean` | Proved |
| Pairwise fold is a contraction | `PairwiseAverage.lean` | Proved |
| Beal Conjecture infrastructure | `BealConjecture.lean` | Partial (gap identified) |
| Full compression pipeline bounds | `CompressionPipeline.lean` | Proved |

## Key Results

### Cyclic Preservation Theorem (Kilpatrick, 2026)

*An exotic tensor field admits lossless dimensional folding if and only if its
component representation can be embedded in the cyclic group Z/pZ for some
prime p, making the fold-unfold operation a group automorphism.*

Formalized as:
- **Necessity**: the pairwise fold on R^{2n} → R^n has a nontrivial kernel;
  no left inverse exists (`CyclicPreservation.lean`)
- **Sufficiency**: the Fermat bridge (primitive root exponentiation) gives an
  exact bijection Fin(p-1) ≃ (Z/pZ)* (`FermatBridge.lean`)

### Fermat Bridge Round-Trip

The power map k ↦ g^k mod p and its inverse (discrete log) form an exact
equivalence. This is the mathematical core of why libdimfold achieves lossless
compression:

```
encode(decode(k)) = k   for all k ∈ {0, ..., p-2}
decode(encode(a)) = a   for all a ∈ (Z/pZ)*
```

### 85% Ceiling

Sign-preserving folding on the Alcubierre exotic tensor (15% negative
components) cannot exceed 85% preservation. The ceiling is tight and is
bypassed by cyclic re-encoding into (Z/pZ)* where sign cancellation is
structurally absent.

### Dimensional Separation (P ≠ NP argument)

The fold from R^{2n} to R^n has rank n and nullity n. Since n < 2^n, the
fold cannot distinguish all 2^n Boolean inputs. This corrects the
information-flow framework from the published papers (which had a
deterministic entropy bug) with a clean linear-algebraic argument.

## Building

Requires [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.29.0-rc1) and [elan](https://github.com/leanprover/elan).

```bash
lake update    # fetch mathlib (first time only, ~5min)
lake build     # verify all proofs
```

## File Structure

```
AfldProof/
├── PairwiseAverage.lean       — Fold operation: linearity, contraction, L2 bounds
├── InformationLoss.lean       — Rank-nullity: fold destroys exactly n dimensions
├── FermatBridge.lean          — Primitive roots, power map bijection, round-trip
├── CyclicPreservation.lean    — Cyclic Preservation Theorem (necessity + sufficiency)
├── SignedFoldingCeiling.lean  — 85% ceiling, bypass via encoding
├── BealConjecture.lean        — Divisibility propagation, p-adic bounds, gap analysis
├── DimensionalSeparation.lean — P≠NP dimensional argument, polynomial gap
└── CompressionPipeline.lean   — Full pipeline: quantize → encode → fold → decode
```

## References

- Kilpatrick, C. (2026). *Warp Drive Number Theory*.
- Kilpatrick, C. (2026). *Information Flow Complexity*.
- [libdimfold](https://github.com/djdarmor/libdimfold) — C implementation.

## License

MIT
