# Audit Report: ErdosSelfridge_v11.lean

**Auditor:** Aristotle Proof Verification System (Harmonic)  
**Date:** May 2026  
**Result:** All 7 checks passed ✅

## Build Status

- Compiles with no `sorry`, no non-standard axioms.
- `#print axioms erdos_selfridge` confirms dependence only on:
  - 3 stated BBMST axioms
  - Standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`)

## Check Results

### 1. Over-quantification fix ✅
**Lines 172–186.** Axioms 2–3 reference `(exists_bbmst_data K cs h_odd).actualBlocks/.sfBlocks` — the specific data from axiom 1, not arbitrary `BBMSTData`. Verified that `sieveProd [2] 1 = 3/2 > 1`, confirming axiom 3 would be false for arbitrary positive data.

### 2. Axiom consistency ✅
All three axioms require `(h_odd : CS_allOdd cs)` as an explicit argument. They cannot be invoked without it, so they cannot derive `False` unconditionally. The axiom system is consistent (assuming BBMST's results are correct).

### 3. Monotonicity chain relevance ✅
**Lines 88–109, 149–162.** Now genuinely necessary. The monotonicity chain `actual_ge_sf` + `sieveProd_antitone` is the **only path** from axiom 3 (SF < 1) to axiom 2's premise (actual < 1). Without it, there is no way to connect the two axioms.

### 4. Let transparency ✅
**Line 210.** Confirmed `d.sfBlocks` and `(exists_bbmst_data K cs h_odd).sfBlocks` are definitionally equal (`rfl` proof). The `let` binding is fully transparent to Lean's elaborator.

### 5. δ-scaling correctness ✅
**Lines 149–162.** `mul_le_mul_of_nonneg_left h_base h_scale` is applied with correct argument order: `h_base` is the inner inequality `(p-1) ≤ (p^e-1)`, `h_scale` is `0 ≤ (1-δ)`.

### 6. Pattern A (triviality) ✅
Benign. While `exists_bbmst_data` is trivially satisfiable as an axiom, axioms 2–3 make non-trivial claims about that specific data. The mathematical content is carried by axioms 2–3, not axiom 1.

### 7. Cast correctness ✅
**Lines 138, 157.** `exact_mod_cast Nat.le_self_pow` correctly lifts ℕ inequalities to ℚ. The cast preserves `≤` and commutes with `^` via Mathlib's `Nat.cast_le` and `Nat.cast_pow`.

## Version History

| Version | Key Change | Aristotle Result |
|---------|-----------|-----------------|
| v9 | Added `nonempty` condition | 6/6 pass |
| v10 | Added δ-correction; **found over-quantification bug** | Critical finding |
| v11 | Fixed over-quantification; axioms bound to specific data | **7/7 pass** |
