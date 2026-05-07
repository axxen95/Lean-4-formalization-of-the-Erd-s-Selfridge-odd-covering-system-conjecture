# Erdős-Selfridge Conjecture — Lean 4 Formalization

**Theorem.** No covering system with distinct odd moduli greater than 1 exists.

This resolves the Erdős-Selfridge conjecture (Erdős Problem #7) by extending the BBMST square-free result to all odd moduli via a coset sieve monotonicity argument, with full machine verification in Lean 4.

## Status

- **0 sorry** — fully machine-verified
- **2 axioms** — both reference published BBMST results only
- `#print axioms erdos_selfridge` → `sieve_criterion`, `sf_sieve_lt_one` + standard Lean axioms
- Compiled against Mathlib v4.28.0
- Verified by the [Aristotle](https://aristotle.harmonic.fun) proof verification system

## Files

| File | Description |
|------|-------------|
| `ErdosSelfridge_v17.lean` | Lean 4 formalization (786 lines) |
| `erdos_selfridge_paper_v3.pdf` | Paper (6 pages) |
| `erdos_selfridge_paper_v3.tex` | LaTeX source |
| `aristotle_instruction_v17.md` | Aristotle verification instructions |

## Architecture

### Axioms (2, BBMST published)

1. **`sieve_criterion`** (BBMST Thm 3.1 + 3.2): If sieve sum with actual block sizes < 1, covering is impossible.
2. **`sf_sieve_lt_one`** (BBMST Thm 1.1): For any odd primes, ∃ parameters with SF sieve sum < 1.

### Proved in Lean (our contribution)

| Theorem | Description |
|---------|-------------|
| `sieveProd_antitone` | Sieve product antitone in block sizes |
| `sieveProd_diff_mono` | **Core lemma**: P₁(x)−P₂(x) monotone increasing in x |
| `M2_num_antitone` | M₂ numerator antitone in block sizes |
| `sieveSum_antitone` | Full sieve sum antitone (nonSF ≤ SF) |
| `blockSize_effective_le` | p^{e-1}(p-1) ≥ p-1 |
| `weight_le_sf` | Coset weight 1/p^a ≤ hyperplane weight 1/p |
| `erdos_selfridge` | **Main theorem** |

## Version History

- **v17** (2026-05-07): Correct sieve sum definition. Full coset monotonicity proved in Lean. 0 sorry, 2 axioms. Core lemma: `sieveProd_diff_mono`.
- **v11** (2026-05-06): First version. Used sieve product instead of sieve sum — axiom system was inconsistent (sieveProd ≥ 1 always, but axiom claimed < 1). Error identified by natso26.

## References

- P. Balister, B. Bollobás, R. Morris, J. Sahasrabudhe, M. Tiba, *The Erdős–Selfridge problem with square-free moduli*, Algebra & Number Theory **15** (2021), 609–626. [arXiv:1901.11465](https://arxiv.org/abs/1901.11465)

## DOI

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19982394.svg)](https://doi.org/10.5281/zenodo.19982394)

## Acknowledgements

Thanks to natso26 for identifying the critical sieve product vs. sieve sum error in v11.

## Author

Jinook Lee (이진욱)
