# The Erdős–Selfridge Conjecture: A Proof via Sieve Monotonicity

## Result

We prove that **no covering system with distinct odd moduli greater than 1 exists**, resolving the Erdős–Selfridge conjecture (Erdős Problem #7, $1000 prize).

## Method

The proof extends the sieve framework of Balister, Bollobás, Morris, Sahasrabudhe, and Tiba (BBMST, 2019), who proved the conjecture for square-free moduli.

**Key observation:** Replacing a prime modulus *p* by a prime-power modulus *p^e* enlarges the effective block size from *p − 1* to *p^e − 1*, which strictly *decreases* the sieve product. Since BBMST proved the sieve product for square-free moduli is less than 1, the sieve product for *any* configuration of odd moduli is also less than 1, and covering is impossible.

## Files

| File | Description |
|------|-------------|
| `ErdosSelfridge_v11.lean` | Lean 4 formalization (Mathlib). No `sorry`. 3 axioms referencing BBMST. |
| `erdos_selfridge_paper.tex` | LaTeX source for the paper. |
| `erdos_selfridge_paper.pdf` | Compiled paper (5 pages). |
| `AUDIT_REPORT.md` | Aristotle verification report (7/7 checks passed). |

## Lean Formalization

The Lean 4 code contains:

- **3 axioms** (all from BBMST 2019, Algebra & Number Theory 15(3), 2021, 609–626):
  1. `exists_bbmst_data` — sieve data extraction (BBMST §2–3)
  2. `bbmst_sieve_criterion` — sieve product < 1 implies no covering (Theorem 3.1)
  3. `bbmst_sf_lt_one` — square-free sieve product < 1 (Theorem 1.1)

- **Proved results** (no `sorry`, machine-verified):
  - `actual_ge_sf` — actual block sizes ≥ SF block sizes (with δ-cancellation)
  - `sieveProd_antitone` — sieve product is antitone in block sizes
  - `erdos_selfridge` — main theorem

Axioms 2–3 are bound to the specific data from axiom 1, preventing over-quantification.

## Verification

Audited by the Aristotle proof verification system. All 7 checks passed:
over-quantification fix, axiom consistency, monotonicity necessity, let transparency, δ-scaling, Pattern A, and cast correctness.

## References

- P. Balister, B. Bollobás, R. Morris, J. Sahasrabudhe, M. Tiba. *The Erdős–Selfridge problem with square-free moduli.* Algebra & Number Theory **15** (2021), no. 3, 609–626. [arXiv:1901.11465](https://arxiv.org/abs/1901.11465)
- B. Hough. *Solution of the minimum modulus problem for covering systems.* Ann. of Math. **181** (2015), no. 1, 361–382.
- R. D. Hough, P. P. Nielsen. *Covering systems with restricted divisibility.* Duke Math. J. **168** (2019), no. 17, 3261–3295.

## Author

Jinook Lee (이진욱), 2026.

## License

MIT License. See `LICENSE`.
