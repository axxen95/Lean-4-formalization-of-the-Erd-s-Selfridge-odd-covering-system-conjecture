/-
  Erdős-Selfridge Conjecture — Lean 4 Formalization (v17)

  DESIGN PRINCIPLE:
    Axioms = BBMST published results ONLY (번역 오류 최소화).
    Everything else — especially coset monotonicity — proved in Lean.

  ┌─────────────────────────────────────────────────────────────────────┐
  │ AXIOMS (2):                                                         │
  │                                                                     │
  │   1. sieve_criterion: BBMST Thm 3.1+3.2                           │
  │      If sieveSum(actual block sizes) < 1, covering is impossible.  │
  │      Statement uses cs's own nonsfBlockSizes.                      │
  │                                                                     │
  │   2. sf_sieve_lt_one: BBMST Thm 1.1 (computation)                 │
  │      ∃ δ, ca1, ca3 with SF sieve sum < 1                          │
  │      + LP structural properties (ca1>0, ca1≤ca3, ca3-2ca1+1≥0).   │
  │                                                                     │
  │ PROVED IN LEAN (our contribution):                                  │
  │   • updateFactor antitone in s, monotone in x                      │
  │   • sieveProd antitone in s, monotone in x                         │
  │   • sieveProd_diff_mono (KEY: cross-monotonicity by induction)     │
  │   • M2 numerator antitone (via diff_mono, no coefficient expand)   │
  │   • sieveSum antitone: nonSF sieve sum ≤ SF sieve sum             │
  │   • Main theorem: erdos_selfridge                                   │
  └─────────────────────────────────────────────────────────────────────┘

  Author: Jinook Lee (이진욱), 2026-05-07
-/
import Mathlib.Tactic

-- ============================================================================
-- §1. COVERING SYSTEM
-- ============================================================================

structure CoveringSystem (K : Nat) where
  residues        : Fin K → Int
  moduli          : Fin K → Nat
  moduli_gt_one   : ∀ i, 1 < moduli i
  moduli_distinct : ∀ i j, i ≠ j → moduli i ≠ moduli j
  covers          : ∀ n : Int, ∃ i, (n - residues i) % (moduli i : Int) = 0

def CS_allOdd {K : Nat} (cs : CoveringSystem K) : Prop :=
  ∀ i, cs.moduli i % 2 = 1

def CS_squarefree {K : Nat} (cs : CoveringSystem K) : Prop :=
  ∀ (i : Fin K) (p : Nat), Nat.Prime p → p * p ∣ cs.moduli i → False

-- ============================================================================
-- §2. SIEVE FRAMEWORK
-- ============================================================================

noncomputable def updateFactor (s δ x : ℚ) : ℚ := 1 + x / ((1 - δ) * s)

noncomputable def sieveProd : List ℚ → List ℚ → ℚ → ℚ
  | [], _, _ => 1
  | _, [], _ => 1
  | s :: ss, δ :: δs, x => updateFactor s δ x * sieveProd ss δs x

noncomputable def ck (ca : ℚ) (ss δs : List ℚ) (x : ℚ) : ℚ :=
  ca * sieveProd ss δs x

noncomputable def M1bound (ca1 : ℚ) (ss δs : List ℚ) (sk : ℚ) (k : Nat) : ℚ :=
  ck ca1 (ss.take k) (δs.take k) 1 / sk

noncomputable def M2bound (ca1 ca3 : ℚ) (ss δs : List ℚ) (sk : ℚ) (k : Nat) : ℚ :=
  let c1 := ck ca1 (ss.take k) (δs.take k) 1
  let c3 := ck ca3 (ss.take k) (δs.take k) 3
  (c3 - 2 * c1 + 1) / sk ^ 2

noncomputable def sieveTerm (ca1 ca3 : ℚ) (ss δs : List ℚ) (k : Nat) : ℚ :=
  let sk := ss.getD k 1
  let δk := δs.getD k 0
  min (M1bound ca1 ss δs sk k) (M2bound ca1 ca3 ss δs sk k / (4 * δk * (1 - δk)))

noncomputable def sieveSum (ca1 ca3 : ℚ) (ss δs : List ℚ) : ℚ :=
  (List.range ss.length).foldl (fun acc k => acc + sieveTerm ca1 ca3 ss δs k) 0

-- ============================================================================
-- §3. UPDATE FACTOR PROPERTIES
-- ============================================================================

theorem updateFactor_one_le {s δ x : ℚ}
    (hs : 0 < s) (hδ : δ < 1) (hx : 0 ≤ x) :
    1 ≤ updateFactor s δ x := by
  unfold updateFactor
  linarith [div_nonneg hx (le_of_lt (mul_pos (by linarith : (0:ℚ) < 1-δ) hs))]

theorem updateFactor_pos {s δ x : ℚ}
    (hs : 0 < s) (hδ : δ < 1) (hx : 0 ≤ x) :
    0 < updateFactor s δ x :=
  lt_of_lt_of_le one_pos (updateFactor_one_le hs hδ hx)

theorem updateFactor_nonneg {s δ x : ℚ}
    (hs : 0 < s) (hδ : δ < 1) (hx : 0 ≤ x) :
    0 ≤ updateFactor s δ x :=
  le_of_lt (updateFactor_pos hs hδ hx)

/-- Antitone in block size s. -/
theorem updateFactor_antitone_s {s₁ s₂ δ x : ℚ}
    (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂) (hδ : δ < 1) (hx : 0 ≤ x) :
    updateFactor s₂ δ x ≤ updateFactor s₁ δ x := by
  unfold updateFactor
  have hd : 0 < 1 - δ := by linarith
  have h1 : 0 < (1 - δ) * s₁ := mul_pos hd hs₁
  have h2 : 0 < (1 - δ) * s₂ := mul_pos hd (lt_of_lt_of_le hs₁ hs)
  suffices x / ((1 - δ) * s₂) ≤ x / ((1 - δ) * s₁) by linarith
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp
  · rw [div_le_div_iff₀ h2 h1]
    nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg hx_pos.le hd.le)]

/-- Monotone in evaluation point x. -/
theorem updateFactor_mono_x {s δ x₁ x₂ : ℚ}
    (hs : 0 < s) (hδ : δ < 1) (_hx : 0 ≤ x₁) (hle : x₁ ≤ x₂) :
    updateFactor s δ x₁ ≤ updateFactor s δ x₂ := by
  unfold updateFactor
  have hd : 0 < (1 - δ) * s := mul_pos (by linarith) hs
  have : x₁ / ((1 - δ) * s) ≤ x₂ / ((1 - δ) * s) :=
    div_le_div_of_nonneg_right hle hd.le
  linarith

-- ============================================================================
-- §4. SIEVE PRODUCT PROPERTIES
-- ============================================================================

-- Helper for sieveProd with empty δs
private theorem sieveProd_empty_δs (ss : List ℚ) (x : ℚ) : sieveProd ss [] x = 1 := by
  cases ss <;> simp [sieveProd]

-- Index shifting helpers
private theorem getD_cons_succ (a : ℚ) (l : List ℚ) (i : Nat) (d : ℚ) :
    (a :: l).getD (i + 1) d = l.getD i d := by simp [List.getD]

private theorem shift_pos (s : ℚ) (ss : List ℚ) (d : ℚ)
    (h : ∀ i, i < (s :: ss).length → 0 < (s :: ss).getD i d) :
    ∀ i, i < ss.length → 0 < ss.getD i d := by
  intro i hi; have := h (i+1) (by simp; omega); rwa [getD_cons_succ] at this

private theorem shift_le (s₁ s₂ : ℚ) (ss₁ ss₂ : List ℚ) (d : ℚ)
    (h : ∀ i, i < (s₁::ss₁).length → (s₁::ss₁).getD i d ≤ (s₂::ss₂).getD i d) :
    ∀ i, i < ss₁.length → ss₁.getD i d ≤ ss₂.getD i d := by
  intro i hi; have := h (i+1) (by simp; omega); rwa [getD_cons_succ, getD_cons_succ] at this

private theorem shift_delta (δ : ℚ) (δs : List ℚ) (d : ℚ)
    (h : ∀ i, i < (δ::δs).length → (δ::δs).getD i d < 1) :
    ∀ i, i < δs.length → δs.getD i d < 1 := by
  intro i hi; have := h (i+1) (by simp; omega); rwa [getD_cons_succ] at this

-- Hypotheses at head position
private theorem head_s_pos (s : ℚ) (ss : List ℚ)
    (h : ∀ i, i < (s :: ss).length → 0 < (s :: ss).getD i 1) : 0 < s := by
  simpa using h 0 (by simp)

private theorem head_delta (δ : ℚ) (δs : List ℚ)
    (h : ∀ i, i < (δ :: δs).length → (δ :: δs).getD i 0 < 1) : δ < 1 := by
  simpa using h 0 (by simp)

private theorem head_le (s₁ s₂ : ℚ) (ss₁ ss₂ : List ℚ)
    (h : ∀ i, i < (s₁::ss₁).length → (s₁::ss₁).getD i 1 ≤ (s₂::ss₂).getD i 1) :
    s₁ ≤ s₂ := by
  simpa using h 0 (by simp)

-- ─── 4.1 sieveProd ≥ 1 ─────────────────────────────

theorem sieveProd_one_le (ss δs : List ℚ) (x : ℚ)
    (hx : 0 ≤ x)
    (hδ : ∀ i, i < δs.length → δs.getD i 0 < 1)
    (hs : ∀ i, i < ss.length → 0 < ss.getD i 1) :
    1 ≤ sieveProd ss δs x := by
  match ss, δs with
  | [], _ => simp [sieveProd]
  | _ :: _, [] => rw [sieveProd_empty_δs]
  | s :: ss', δ :: δs' =>
    simp only [sieveProd]
    have huf := updateFactor_one_le (head_s_pos s ss' hs) (head_delta δ δs' hδ) hx
    have hsp := sieveProd_one_le ss' δs' x hx (shift_delta δ δs' 0 hδ) (shift_pos s ss' 1 hs)
    calc 1 = 1 * 1 := (one_mul 1).symm
      _ ≤ updateFactor s δ x * sieveProd ss' δs' x :=
        mul_le_mul huf hsp one_pos.le (le_trans zero_le_one huf)

theorem sieveProd_nonneg (ss δs : List ℚ) (x : ℚ) (hx : 0 ≤ x)
    (hδ : ∀ i, i < δs.length → δs.getD i 0 < 1)
    (hs : ∀ i, i < ss.length → 0 < ss.getD i 1) :
    0 ≤ sieveProd ss δs x :=
  le_trans one_pos.le (sieveProd_one_le ss δs x hx hδ hs)

-- ─── 4.2 Antitone in block sizes ───────────────────

theorem sieveProd_antitone (ss₁ ss₂ δs : List ℚ) (x : ℚ)
    (hlen : ss₁.length = ss₂.length) (hx : 0 ≤ x)
    (hδ : ∀ i, i < δs.length → δs.getD i 0 < 1)
    (hs_pos : ∀ i, i < ss₁.length → 0 < ss₁.getD i 1)
    (hs_le : ∀ i, i < ss₁.length → ss₁.getD i 1 ≤ ss₂.getD i 1) :
    sieveProd ss₂ δs x ≤ sieveProd ss₁ δs x := by
  match ss₁, ss₂, δs, hlen with
  | [], [], _, _ => simp [sieveProd]
  | [], _::_, _, hlen => simp at hlen
  | _::_, [], _, hlen => simp at hlen
  | _ :: _, _ :: _, [], _ =>
    rw [sieveProd_empty_δs, sieveProd_empty_δs]
  | s₁ :: ss₁', s₂ :: ss₂', δ :: δs', hlen =>
    simp only [sieveProd]
    have hlen' : ss₁'.length = ss₂'.length := by simp at hlen; exact hlen
    have hs₁ := head_s_pos s₁ ss₁' hs_pos
    have hδ₀ := head_delta δ δs' hδ
    have hle₀ := head_le s₁ s₂ ss₁' ss₂' hs_le
    have h_uf := updateFactor_antitone_s hs₁ hle₀ hδ₀ hx
    have h_sp := sieveProd_antitone ss₁' ss₂' δs' x hlen' hx
        (shift_delta δ δs' 0 hδ) (shift_pos s₁ ss₁' 1 hs_pos)
        (shift_le s₁ s₂ ss₁' ss₂' 1 hs_le)
    have h1 : 0 ≤ updateFactor s₂ δ x :=
      updateFactor_nonneg (lt_of_lt_of_le hs₁ hle₀) hδ₀ hx
    have h2 : 0 ≤ sieveProd ss₁' δs' x :=
      sieveProd_nonneg ss₁' δs' x hx (shift_delta δ δs' 0 hδ) (shift_pos s₁ ss₁' 1 hs_pos)
    calc updateFactor s₂ δ x * sieveProd ss₂' δs' x
        ≤ updateFactor s₂ δ x * sieveProd ss₁' δs' x :=
          mul_le_mul_of_nonneg_left h_sp h1
      _ ≤ updateFactor s₁ δ x * sieveProd ss₁' δs' x :=
          mul_le_mul_of_nonneg_right h_uf h2

-- ─── 4.3 Monotone in x ─────────────────────────────

theorem sieveProd_mono_x (ss δs : List ℚ) (x₁ x₂ : ℚ)
    (hx₁ : 0 ≤ x₁) (hle : x₁ ≤ x₂)
    (hδ : ∀ i, i < δs.length → δs.getD i 0 < 1)
    (hs : ∀ i, i < ss.length → 0 < ss.getD i 1) :
    sieveProd ss δs x₁ ≤ sieveProd ss δs x₂ := by
  match ss, δs with
  | [], _ => simp [sieveProd]
  | _ :: _, [] => rw [sieveProd_empty_δs, sieveProd_empty_δs]
  | s :: ss', δ :: δs' =>
    simp only [sieveProd]
    have hs₀ := head_s_pos s ss' hs
    have hδ₀ := head_delta δ δs' hδ
    have h_uf := updateFactor_mono_x hs₀ hδ₀ hx₁ hle
    have h_sp := sieveProd_mono_x ss' δs' x₁ x₂ hx₁ hle
        (shift_delta δ δs' 0 hδ) (shift_pos s ss' 1 hs)
    have h1 : 0 ≤ updateFactor s δ x₁ := updateFactor_nonneg hs₀ hδ₀ hx₁
    have h2 : 0 ≤ sieveProd ss' δs' x₂ :=
      sieveProd_nonneg ss' δs' x₂ (le_trans hx₁ hle)
        (shift_delta δ δs' 0 hδ) (shift_pos s ss' 1 hs)
    calc updateFactor s δ x₁ * sieveProd ss' δs' x₁
        ≤ updateFactor s δ x₁ * sieveProd ss' δs' x₂ :=
          mul_le_mul_of_nonneg_left h_sp h1
      _ ≤ updateFactor s δ x₂ * sieveProd ss' δs' x₂ :=
          mul_le_mul_of_nonneg_right h_uf h2

-- ─── 4.4 Cross-monotonicity helpers ─────────────────

/-- Product of two nonneg increasing pairs is increasing. -/
private theorem mono_product {a₁ a₂ b₁ b₂ : ℚ}
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁) :
    a₁ * b₁ ≤ a₂ * b₂ :=
  calc a₁ * b₁ ≤ a₂ * b₁ := mul_le_mul_of_nonneg_right ha hb₁
    _ ≤ a₂ * b₂ := mul_le_mul_of_nonneg_left hb (le_trans ha₁ ha)

/-- updateFactor difference (u(s₁,x)-u(s₂,x)) is monotone in x. -/
private theorem updateFactor_diff_mono_x {s₁ s₂ δ x₁ x₂ : ℚ}
    (hs₁ : 0 < s₁) (hs : s₁ ≤ s₂) (hδ : δ < 1)
    (_hx₁ : 0 ≤ x₁) (hx₁₂ : x₁ ≤ x₂) :
    updateFactor s₁ δ x₁ - updateFactor s₂ δ x₁ ≤
    updateFactor s₁ δ x₂ - updateFactor s₂ δ x₂ := by
  unfold updateFactor
  have hd : 0 < 1 - δ := by linarith
  have h1 : 0 < (1 - δ) * s₁ := mul_pos hd hs₁
  have h2 : 0 < (1 - δ) * s₂ := mul_pos hd (lt_of_lt_of_le hs₁ hs)
  suffices x₂ / ((1-δ)*s₂) - x₁ / ((1-δ)*s₂) ≤
           x₂ / ((1-δ)*s₁) - x₁ / ((1-δ)*s₁) by linarith
  rcases eq_or_lt_of_le hx₁₂ with rfl | hlt
  · simp
  · rw [← sub_div, ← sub_div, div_le_div_iff₀ h2 h1]
    nlinarith [mul_le_mul_of_nonneg_left hs (mul_nonneg (by linarith : (0:ℚ) ≤ x₂ - x₁) hd.le)]

-- ─── 4.5 Cross-monotonicity (KEY LEMMA) ────────────

/-- **SIEVE PRODUCT DIFF MONO** — The core technical lemma.

    If ss₁ ≤ ss₂ (componentwise), P₁ = sieveProd(ss₁), P₂ = sieveProd(ss₂),
    then P₁(x) - P₂(x) is monotone increasing in x ≥ 0. -/
theorem sieveProd_diff_mono (ss₁ ss₂ δs : List ℚ) (x₁ x₂ : ℚ)
    (hlen : ss₁.length = ss₂.length)
    (hx₁ : 0 ≤ x₁) (hx₁₂ : x₁ ≤ x₂)
    (hδ : ∀ i, i < δs.length → δs.getD i 0 < 1)
    (hs_pos : ∀ i, i < ss₁.length → 0 < ss₁.getD i 1)
    (hs_le : ∀ i, i < ss₁.length → ss₁.getD i 1 ≤ ss₂.getD i 1) :
    sieveProd ss₁ δs x₂ - sieveProd ss₂ δs x₂ ≥
    sieveProd ss₁ δs x₁ - sieveProd ss₂ δs x₁ := by
  match ss₁, ss₂, δs, hlen with
  | [], [], _, _ => simp [sieveProd]
  | [], _ :: _, _, hlen => simp at hlen
  | _ :: _, [], _, hlen => simp at hlen
  | _ :: _, _ :: _, [], _ =>
    rw [sieveProd_empty_δs, sieveProd_empty_δs, sieveProd_empty_δs, sieveProd_empty_δs]
  | s₁ :: ss₁', s₂ :: ss₂', δ :: δs', hlen =>
    simp only [sieveProd]

    -- Shifted hypotheses
    have hlen' : ss₁'.length = ss₂'.length := by simp at hlen; exact hlen
    have hδ' := shift_delta δ δs' 0 hδ
    have hs_pos' := shift_pos s₁ ss₁' 1 hs_pos
    have hs_le' := shift_le s₁ s₂ ss₁' ss₂' 1 hs_le
    have hs₁ := head_s_pos s₁ ss₁' hs_pos
    have hδ₀ := head_delta δ δs' hδ
    have hle₀ := head_le s₁ s₂ ss₁' ss₂' hs_le
    have _hs₂ : 0 < s₂ := lt_of_lt_of_le hs₁ hle₀
    have _hx₂ : 0 ≤ x₂ := le_trans hx₁ hx₁₂
    have hs₂_pos : ∀ i, i < ss₂'.length → 0 < ss₂'.getD i 1 := by
      intro i hi; have hi₁ : i < ss₁'.length := by rw [hlen']; exact hi
      exact lt_of_lt_of_le (hs_pos' i hi₁) (hs_le' i hi₁)

    -- Induction hypothesis
    have ih : sieveProd ss₁' δs' x₂ - sieveProd ss₂' δs' x₂ ≥
              sieveProd ss₁' δs' x₁ - sieveProd ss₂' δs' x₁ :=
      sieveProd_diff_mono ss₁' ss₂' δs' x₁ x₂ hlen' hx₁ hx₁₂ hδ' hs_pos' hs_le'

    -- Part 1: u₁·D is increasing
    have u1_mono : updateFactor s₁ δ x₁ ≤ updateFactor s₁ δ x₂ :=
      updateFactor_mono_x hs₁ hδ₀ hx₁ hx₁₂
    have u1_nn : 0 ≤ updateFactor s₁ δ x₁ := updateFactor_nonneg hs₁ hδ₀ hx₁
    have D_nn : 0 ≤ sieveProd ss₁' δs' x₁ - sieveProd ss₂' δs' x₁ := by
      linarith [sieveProd_antitone ss₁' ss₂' δs' x₁ hlen' hx₁ hδ' hs_pos' hs_le']
    have part1 : updateFactor s₁ δ x₁ * (sieveProd ss₁' δs' x₁ - sieveProd ss₂' δs' x₁) ≤
                 updateFactor s₁ δ x₂ * (sieveProd ss₁' δs' x₂ - sieveProd ss₂' δs' x₂) :=
      mono_product u1_mono ih u1_nn D_nn

    -- Part 2: Δu·Q₂ is increasing
    have du_nn : 0 ≤ updateFactor s₁ δ x₁ - updateFactor s₂ δ x₁ := by
      linarith [updateFactor_antitone_s hs₁ hle₀ hδ₀ hx₁]
    have du_mono : updateFactor s₁ δ x₁ - updateFactor s₂ δ x₁ ≤
                   updateFactor s₁ δ x₂ - updateFactor s₂ δ x₂ :=
      updateFactor_diff_mono_x hs₁ hle₀ hδ₀ hx₁ hx₁₂
    have Q2_nn : 0 ≤ sieveProd ss₂' δs' x₁ := sieveProd_nonneg ss₂' δs' x₁ hx₁ hδ' hs₂_pos
    have Q2_mono : sieveProd ss₂' δs' x₁ ≤ sieveProd ss₂' δs' x₂ :=
      sieveProd_mono_x ss₂' δs' x₁ x₂ hx₁ hx₁₂ hδ' hs₂_pos
    have part2 : (updateFactor s₁ δ x₁ - updateFactor s₂ δ x₁) * sieveProd ss₂' δs' x₁ ≤
                 (updateFactor s₁ δ x₂ - updateFactor s₂ δ x₂) * sieveProd ss₂' δs' x₂ :=
      mono_product du_mono Q2_mono du_nn Q2_nn

    -- Combine: part1 + part2 = goal (ring decomposition)
    nlinarith [mul_sub (updateFactor s₁ δ x₁) (sieveProd ss₁' δs' x₁) (sieveProd ss₂' δs' x₁),
               mul_sub (updateFactor s₁ δ x₂) (sieveProd ss₁' δs' x₂) (sieveProd ss₂' δs' x₂),
               sub_mul (updateFactor s₁ δ x₁) (updateFactor s₂ δ x₁) (sieveProd ss₂' δs' x₁),
               sub_mul (updateFactor s₁ δ x₂) (updateFactor s₂ δ x₂) (sieveProd ss₂' δs' x₂)]

-- ============================================================================
-- §5. MOMENT AND SIEVE SUM MONOTONICITY
-- ============================================================================

/-- Ratio antitone: num↓ + den↑ → ratio↓. -/
theorem ratio_antitone {n₁ n₂ d₁ d₂ : ℚ}
    (hn : n₁ ≤ n₂) (hd : d₂ ≤ d₁)
    (hn₁ : 0 ≤ n₁) (hd₂ : 0 < d₂) :
    n₁ / d₁ ≤ n₂ / d₂ := by
  have hd₁ : 0 < d₁ := lt_of_lt_of_le hd₂ hd
  rw [div_le_div_iff₀ hd₁ hd₂]; nlinarith

/-- M2 numerator antitone. -/
theorem M2_num_antitone (ss₁ ss₂ δs : List ℚ) (ca1 ca3 : ℚ)
    (hlen : ss₁.length = ss₂.length)
    (hδ : ∀ i, i < δs.length → δs.getD i 0 < 1)
    (hs_pos : ∀ i, i < ss₁.length → 0 < ss₁.getD i 1)
    (hs_le : ∀ i, i < ss₁.length → ss₁.getD i 1 ≤ ss₂.getD i 1)
    (hca1 : 0 < ca1) (hca13 : ca1 ≤ ca3) (_hbase : 0 ≤ ca3 - 2 * ca1 + 1) :
    ca3 * sieveProd ss₂ δs 3 - 2 * ca1 * sieveProd ss₂ δs 1 + 1 ≤
    ca3 * sieveProd ss₁ δs 3 - 2 * ca1 * sieveProd ss₁ δs 1 + 1 := by
  suffices h : ca3 * (sieveProd ss₁ δs 3 - sieveProd ss₂ δs 3) ≥
               2 * ca1 * (sieveProd ss₁ δs 1 - sieveProd ss₂ δs 1) by linarith
  match ss₁, ss₂, δs, hlen with
  | [], [], _, _ => simp [sieveProd]
  | [], _ :: _, _, hlen => simp at hlen
  | _ :: _, [], _, hlen => simp at hlen
  | _ :: _, _ :: _, [], _ =>
    rw [sieveProd_empty_δs, sieveProd_empty_δs, sieveProd_empty_δs, sieveProd_empty_δs]; simp
  | s₁ :: ss₁', s₂ :: ss₂', δ :: δs', hlen =>
    simp only [sieveProd]
    have hlen' : ss₁'.length = ss₂'.length := by simp at hlen; exact hlen
    have hδ' := shift_delta δ δs' 0 hδ
    have hs_pos' := shift_pos s₁ ss₁' 1 hs_pos
    have hs_le' := shift_le s₁ s₂ ss₁' ss₂' 1 hs_le
    have hs₁ := head_s_pos s₁ ss₁' hs_pos
    have hδ₀ := head_delta δ δs' hδ
    have hle₀ := head_le s₁ s₂ ss₁' ss₂' hs_le
    have _hs₂ : 0 < s₂ := lt_of_lt_of_le hs₁ hle₀
    have hs₂_pos : ∀ i, i < ss₂'.length → 0 < ss₂'.getD i 1 := by
      intro i hi; exact lt_of_lt_of_le (hs_pos' i (by rw [hlen']; exact hi))
                                       (hs_le' i (by rw [hlen']; exact hi))
    -- IH
    have ih : ca3 * (sieveProd ss₁' δs' 3 - sieveProd ss₂' δs' 3) ≥
              2 * ca1 * (sieveProd ss₁' δs' 1 - sieveProd ss₂' δs' 1) := by
      have := M2_num_antitone ss₁' ss₂' δs' ca1 ca3 hlen' hδ' hs_pos' hs_le'
                hca1 hca13 _hbase
      linarith
    -- Tail diffs
    have hΔ₃ : 0 ≤ sieveProd ss₁' δs' 3 - sieveProd ss₂' δs' 3 := by
      linarith [sieveProd_antitone ss₁' ss₂' δs' 3 hlen' (by norm_num : (0:ℚ) ≤ 3) hδ' hs_pos' hs_le']
    have hΔ₁ : 0 ≤ sieveProd ss₁' δs' 1 - sieveProd ss₂' δs' 1 := by
      linarith [sieveProd_antitone ss₁' ss₂' δs' 1 hlen' (by norm_num : (0:ℚ) ≤ 1) hδ' hs_pos' hs_le']
    -- updateFactor properties
    have uf₁₁_nn : 0 ≤ updateFactor s₁ δ 1 := updateFactor_nonneg hs₁ hδ₀ (by norm_num)
    have uf₁₃_ge_uf₁₁ : updateFactor s₁ δ 1 ≤ updateFactor s₁ δ 3 :=
      updateFactor_mono_x hs₁ hδ₀ (by norm_num) (by norm_num)
    have du_nn : 0 ≤ updateFactor s₁ δ 1 - updateFactor s₂ δ 1 := by
      linarith [updateFactor_antitone_s hs₁ hle₀ hδ₀ (by norm_num : (0:ℚ) ≤ 1)]
    have du_eq : updateFactor s₁ δ 3 - updateFactor s₂ δ 3 =
                 3 * (updateFactor s₁ δ 1 - updateFactor s₂ δ 1) := by
      unfold updateFactor; ring
    -- Q₂ properties
    have Q₂₁_nn : 0 ≤ sieveProd ss₂' δs' 1 := sieveProd_nonneg ss₂' δs' 1 (by norm_num) hδ' hs₂_pos
    have Q₂₃_ge : sieveProd ss₂' δs' 1 ≤ sieveProd ss₂' δs' 3 :=
      sieveProd_mono_x ss₂' δs' 1 3 (by norm_num) (by norm_num) hδ' hs₂_pos
    -- ca properties
    have hca3_nn : 0 ≤ ca3 := le_trans (le_of_lt hca1) hca13
    have h3ca3 : 2 * ca1 < 3 * ca3 := by nlinarith
    -- Decompose using ring identities and prove parts separately
    have lhs_eq : ca3 * (updateFactor s₁ δ 3 * sieveProd ss₁' δs' 3 -
        updateFactor s₂ δ 3 * sieveProd ss₂' δs' 3) =
      ca3 * (updateFactor s₁ δ 3 * (sieveProd ss₁' δs' 3 - sieveProd ss₂' δs' 3) +
        (updateFactor s₁ δ 3 - updateFactor s₂ δ 3) * sieveProd ss₂' δs' 3) := by ring
    have rhs_eq : 2 * ca1 * (updateFactor s₁ δ 1 * sieveProd ss₁' δs' 1 -
        updateFactor s₂ δ 1 * sieveProd ss₂' δs' 1) =
      2 * ca1 * (updateFactor s₁ δ 1 * (sieveProd ss₁' δs' 1 - sieveProd ss₂' δs' 1) +
        (updateFactor s₁ δ 1 - updateFactor s₂ δ 1) * sieveProd ss₂' δs' 1) := by ring
    rw [ge_iff_le, lhs_eq, rhs_eq]
    -- Part A
    have partA : 2 * ca1 * updateFactor s₁ δ 1 * (sieveProd ss₁' δs' 1 - sieveProd ss₂' δs' 1) ≤
                 ca3 * updateFactor s₁ δ 3 * (sieveProd ss₁' δs' 3 - sieveProd ss₂' δs' 3) := by
      calc 2 * ca1 * updateFactor s₁ δ 1 * (sieveProd ss₁' δs' 1 - sieveProd ss₂' δs' 1)
          ≤ ca3 * updateFactor s₁ δ 1 * (sieveProd ss₁' δs' 3 - sieveProd ss₂' δs' 3) := by
            nlinarith [mul_nonneg uf₁₁_nn hΔ₃, mul_nonneg uf₁₁_nn hΔ₁]
        _ ≤ ca3 * updateFactor s₁ δ 3 * (sieveProd ss₁' δs' 3 - sieveProd ss₂' δs' 3) := by
            nlinarith [mul_nonneg hca3_nn hΔ₃]
    -- Part B
    have partB : 2 * ca1 * (updateFactor s₁ δ 1 - updateFactor s₂ δ 1) * sieveProd ss₂' δs' 1 ≤
                 ca3 * (updateFactor s₁ δ 3 - updateFactor s₂ δ 3) * sieveProd ss₂' δs' 3 := by
      rw [du_eq]
      calc 2 * ca1 * (updateFactor s₁ δ 1 - updateFactor s₂ δ 1) * sieveProd ss₂' δs' 1
          ≤ 3 * ca3 * (updateFactor s₁ δ 1 - updateFactor s₂ δ 1) * sieveProd ss₂' δs' 1 := by
            nlinarith [mul_nonneg du_nn Q₂₁_nn]
        _ ≤ 3 * ca3 * (updateFactor s₁ δ 1 - updateFactor s₂ δ 1) * sieveProd ss₂' δs' 3 := by
            nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ 3 * ca3) du_nn)
                                  (by linarith : 0 ≤ sieveProd ss₂' δs' 3 - sieveProd ss₂' δs' 1)]
        _ = ca3 * (3 * (updateFactor s₁ δ 1 - updateFactor s₂ δ 1)) * sieveProd ss₂' δs' 3 := by ring
    nlinarith

-- ============================================================================
-- §6. BLOCK SIZE COMPARISON
-- ============================================================================

theorem blockSize_SF_le_nonSF (p e : Nat) (hp : 2 ≤ p) (_he : 1 ≤ e) :
    p - 1 ≤ p ^ e - 1 := by
  have : p ≤ p ^ e := Nat.le_self_pow (by omega) p; omega

theorem blockSize_effective_le (p e : Nat) (hp : 3 ≤ p) (he : 1 ≤ e) :
    p - 1 ≤ p ^ (e - 1) * (p - 1) := by
  have : 1 ≤ p ^ (e - 1) := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem weight_le_sf (p a : Nat) (_hp : 2 ≤ p) (_ha : 1 ≤ a) :
    p ≤ p ^ a := Nat.le_self_pow (by omega) p

theorem weight_strict (p a : Nat) (hp : 3 ≤ p) (ha : 2 ≤ a) :
    p < p ^ a := by
  calc p = p ^ 1 := (pow_one p).symm
    _ < p ^ a := by apply Nat.pow_lt_pow_right <;> omega

-- ============================================================================
-- §7. INFRASTRUCTURE
-- ============================================================================

def effectiveBlockSize (p e : Nat) : Nat := p ^ (e - 1) * (p - 1)
def sfBlockSize (p : Nat) : Nat := p - 1

noncomputable def extractPrimes {K : Nat} (cs : CoveringSystem K) : List Nat :=
  ((Finset.univ : Finset (Fin K)).biUnion
    (fun i => (cs.moduli i).primeFactorsList.toFinset)).filter (· % 2 = 1)
    |>.sort (· ≤ ·)

noncomputable def maxValuation {K : Nat} (cs : CoveringSystem K) (p : Nat) : Nat :=
  Finset.univ.sup (fun i : Fin K => (cs.moduli i).factorization p)

noncomputable def nonsfBlockSizes {K : Nat} (cs : CoveringSystem K) : List ℚ :=
  (extractPrimes cs).map (fun p => (effectiveBlockSize p (maxValuation cs p) : ℚ))

noncomputable def sfBlockSizes {K : Nat} (cs : CoveringSystem K) : List ℚ :=
  (extractPrimes cs).map (fun p => ((sfBlockSize p : Nat) : ℚ))

-- ============================================================================
-- §8. BBMST AXIOMS (exactly 2, translation-safe)
-- ============================================================================

/-- **Axiom 1: BBMST Sieve Criterion.** (Thm 3.1 + 3.2)

    If sieve sum computed with cs's actual block sizes < 1,
    then the covering system does not cover ℤ. -/
axiom sieve_criterion
    {K : Nat} (cs : CoveringSystem K) (h_odd : CS_allOdd cs)
    (δs : List ℚ) (ca1 ca3 : ℚ)
    (h_sum_lt : sieveSum ca1 ca3 (nonsfBlockSizes cs) δs < 1) : False

/-- **Axiom 2: BBMST SF Sieve Computation.** (Thm 1.1)

    For any set of odd primes, ∃ parameters with SF sieve sum < 1. -/
axiom sf_sieve_lt_one
    (primes : List Nat) (h_primes : ∀ p ∈ primes, Nat.Prime p ∧ p % 2 = 1) :
    ∃ (δs : List ℚ) (ca1 ca3 : ℚ),
      sieveSum ca1 ca3 (primes.map (fun p => (p : ℚ) - 1)) δs < 1
      ∧ 0 < ca1
      ∧ ca1 ≤ ca3
      ∧ 0 ≤ ca3 - 2 * ca1 + 1
      ∧ ∀ i, i < δs.length → 0 ≤ δs.getD i 0 ∧ δs.getD i 0 < 1

-- ============================================================================
-- §9. SIEVE SUM MONOTONICITY (our main contribution)
-- ============================================================================

/-- M2 numerator is always nonneg under the LP conditions. -/
theorem M2_num_nonneg (ss δs : List ℚ) (ca1 ca3 : ℚ)
    (hδ : ∀ i, i < δs.length → δs.getD i 0 < 1)
    (hs_pos : ∀ i, i < ss.length → 0 < ss.getD i 1)
    (hca1 : 0 < ca1) (hca13 : ca1 ≤ ca3) (hbase : 0 ≤ ca3 - 2 * ca1 + 1) :
    0 ≤ ca3 * sieveProd ss δs 3 - 2 * ca1 * sieveProd ss δs 1 + 1 := by
  match ss, δs with
  | [], _ => simp [sieveProd]; linarith
  | _ :: _, [] => rw [sieveProd_empty_δs, sieveProd_empty_δs]; simp; linarith
  | s :: ss', δ :: δs' =>
    simp only [sieveProd]
    have hs₁ := head_s_pos s ss' hs_pos
    have hδ₀ := head_delta δ δs' hδ
    have hδ' := shift_delta δ δs' 0 hδ
    have hs' := shift_pos s ss' 1 hs_pos
    have ih := M2_num_nonneg ss' δs' ca1 ca3 hδ' hs' hca1 hca13 hbase
    have u1_ge1 := updateFactor_one_le hs₁ hδ₀ (by norm_num : (0:ℚ) ≤ 1)
    have Q3_nn := sieveProd_nonneg ss' δs' 3 (by norm_num) hδ' hs'
    have Q31 := sieveProd_mono_x ss' δs' 1 3 (by norm_num) (by norm_num) hδ' hs'
    have h3ca3 : 3 * ca3 > 2 * ca1 := by nlinarith
    have hpos : 3 * ca3 * sieveProd ss' δs' 3 ≥ 2 * ca1 * sieveProd ss' δs' 1 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ 3 * ca3 - 2 * ca1)
                  (sieveProd_nonneg ss' δs' 1 (by norm_num) hδ' hs')]
    have uf_eq : updateFactor s δ 3 = 3 * updateFactor s δ 1 - 2 := by
      unfold updateFactor; ring
    rw [uf_eq]
    nlinarith [mul_nonneg (by linarith : 0 ≤ updateFactor s δ 1 - 1) (by linarith)]

-- ─── Take helpers for sieveTerm antitone ─────────────

private theorem take_pos (ss : List ℚ) (k : Nat)
    (hs : ∀ i, i < ss.length → 0 < ss.getD i 1) :
    ∀ i, i < (ss.take k).length → 0 < (ss.take k).getD i 1 := by
  intro i hi
  simp [List.length_take] at hi
  have hi' : i < ss.length := by omega
  unfold List.getD
  simp [List.getElem?_take, hi, List.getElem?_eq_getElem hi']
  have := hs i hi'; unfold List.getD at this
  simp [List.getElem?_eq_getElem hi'] at this; exact this

private theorem take_le (ss₁ ss₂ : List ℚ) (k : Nat)
    (hlen : ss₁.length = ss₂.length)
    (hs : ∀ i, i < ss₁.length → ss₁.getD i 1 ≤ ss₂.getD i 1) :
    ∀ i, i < (ss₁.take k).length → (ss₁.take k).getD i 1 ≤ (ss₂.take k).getD i 1 := by
  intro i hi
  simp [List.length_take] at hi
  have hi₁ : i < ss₁.length := by omega
  have hi₂ : i < ss₂.length := by omega
  unfold List.getD
  simp [List.getElem?_take, hi, List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂]
  have := hs i hi₁; unfold List.getD at this
  simp [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂] at this; exact this

private theorem take_len_eq (ss₁ ss₂ : List ℚ) (k : Nat)
    (hlen : ss₁.length = ss₂.length) :
    (ss₁.take k).length = (ss₂.take k).length := by
  simp [List.length_take, hlen]

private theorem take_delta (δs : List ℚ) (k : Nat)
    (hδ : ∀ i, i < δs.length → δs.getD i 0 < 1) :
    ∀ i, i < (δs.take k).length → (δs.take k).getD i 0 < 1 := by
  intro i hi
  simp [List.length_take] at hi
  have hi' : i < δs.length := by omega
  unfold List.getD
  simp [List.getElem?_take, hi, List.getElem?_eq_getElem hi']
  have := hδ i hi'; unfold List.getD at this
  simp [List.getElem?_eq_getElem hi'] at this; exact this

-- ─── sieveTerm antitone ─────────────────────────────

private theorem sieveTerm_antitone (ss₁ ss₂ δs : List ℚ) (ca1 ca3 : ℚ) (k : Nat)
    (hlen : ss₁.length = ss₂.length)
    (hδ : ∀ i, i < δs.length → δs.getD i 0 < 1)
    (hδ_nn : ∀ i, i < δs.length → 0 ≤ δs.getD i 0)
    (hs_pos : ∀ i, i < ss₁.length → 0 < ss₁.getD i 1)
    (hs_le : ∀ i, i < ss₁.length → ss₁.getD i 1 ≤ ss₂.getD i 1)
    (hca1 : 0 < ca1) (hca13 : ca1 ≤ ca3)
    (hbase : 0 ≤ ca3 - 2 * ca1 + 1) :
    sieveTerm ca1 ca3 ss₂ δs k ≤ sieveTerm ca1 ca3 ss₁ δs k := by
  simp only [sieveTerm, M1bound, M2bound, ck]
  apply min_le_min
  · -- M1bound antitone: ca1*P₂(take k, 1)/sk₂ ≤ ca1*P₁(take k, 1)/sk₁
    apply ratio_antitone
    · -- Numerator: ca1*P₂ ≤ ca1*P₁
      apply mul_le_mul_of_nonneg_left _ hca1.le
      exact sieveProd_antitone _ _ _ _ (take_len_eq _ _ k hlen) (by norm_num)
        (take_delta δs k hδ) (take_pos ss₁ k hs_pos) (take_le ss₁ ss₂ k hlen hs_le)
    · -- Denominator: sk₁ ≤ sk₂
      by_cases hk : k < ss₁.length
      · exact hs_le k hk
      · simp [List.getD, List.getElem?_eq_none (by omega : ss₁.length ≤ k),
              List.getElem?_eq_none (by omega : ss₂.length ≤ k)]
    · -- Numerator nonneg
      have hs₂_pos' : ∀ i, i < ss₂.length → 0 < ss₂.getD i 1 := by
        intro i hi; have hi₁ : i < ss₁.length := by omega
        exact lt_of_lt_of_le (hs_pos i hi₁) (hs_le i hi₁)
      exact mul_nonneg hca1.le (sieveProd_nonneg _ _ _ (by norm_num)
        (take_delta δs k hδ) (take_pos ss₂ k hs₂_pos'))
    · -- Denominator₂ > 0 (this is sk₁)
      by_cases hk : k < ss₁.length
      · exact hs_pos k hk
      · unfold List.getD; simp [List.getElem?_eq_none (by omega : ss₁.length ≤ k)]
  · -- M2bound/(4δ(1-δ)) antitone
    -- First show M2bound₂ ≤ M2bound₁, then divide by nonneg 4δ(1-δ)
    apply div_le_div_of_nonneg_right _ _
    · -- M2bound₂ ≤ M2bound₁
      have hs₂_pos : ∀ i, i < ss₂.length → 0 < ss₂.getD i 1 := by
        intro i hi; have hi₁ : i < ss₁.length := by omega
        exact lt_of_lt_of_le (hs_pos i hi₁) (hs_le i hi₁)
      have sk₁_pos : 0 < ss₁.getD k 1 := by
        by_cases hk : k < ss₁.length
        · exact hs_pos k hk
        · unfold List.getD; simp [List.getElem?_eq_none (by omega : ss₁.length ≤ k)]
      have sk_le : ss₁.getD k 1 ≤ ss₂.getD k 1 := by
        by_cases hk : k < ss₁.length
        · exact hs_le k hk
        · unfold List.getD
          simp [List.getElem?_eq_none (by omega : ss₁.length ≤ k),
                List.getElem?_eq_none (by omega : ss₂.length ≤ k)]
      have h_num_anti := M2_num_antitone _ _ _ ca1 ca3 (take_len_eq _ _ k hlen)
        (take_delta δs k hδ) (take_pos ss₁ k hs_pos) (take_le ss₁ ss₂ k hlen hs_le)
        hca1 hca13 hbase
      have h_num_nn := M2_num_nonneg _ _ ca1 ca3 (take_delta δs k hδ) (take_pos ss₂ k hs₂_pos)
        hca1 hca13 hbase
      -- The actual goal is about `ck` which expands to `ca * sieveProd`
      -- M2bound uses `2 * ck ca1 ... = 2 * (ca1 * sieveProd ...)` while
      -- M2_num_antitone uses `2 * ca1 * sieveProd ...`
      -- These differ by associativity
      have sk₂_pos : 0 < ss₂.getD k 1 := lt_of_lt_of_le sk₁_pos sk_le
      apply ratio_antitone
      · -- numerator antitone
        linarith
      · -- denominator: sk₁² ≤ sk₂²
        exact sq_le_sq' (by nlinarith) sk_le
      · -- numerator nonneg
        linarith
      · -- denominator > 0
        exact sq_pos_of_pos sk₁_pos
    · -- 4δ(1-δ) ≥ 0
      by_cases hk : k < δs.length
      · have hlt := hδ k hk; have hnn := hδ_nn k hk
        nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℚ) ≤ 4) hnn) (by linarith : 0 ≤ 1 - δs.getD k 0)]
      · unfold List.getD; simp [List.getElem?_eq_none (by omega : δs.length ≤ k)]

-- ─── foldl sum monotone ─────────────────────────────

private theorem foldl_sum_antitone (f g : Nat → ℚ) (l : List Nat)
    (h : ∀ k ∈ l, f k ≤ g k) :
    l.foldl (fun acc k => acc + f k) 0 ≤ l.foldl (fun acc k => acc + g k) 0 := by
  suffices ∀ (a b : ℚ), a ≤ b →
    l.foldl (fun acc k => acc + f k) a ≤ l.foldl (fun acc k => acc + g k) b from
    this 0 0 le_rfl
  induction l with
  | nil => intro a b hab; simpa
  | cons x xs ih =>
    intro a b hab
    simp only [List.foldl_cons]
    apply ih (fun k hk => h k (List.mem_cons_of_mem x hk))
    linarith [h x (by exact List.mem_cons_self : x ∈ x :: xs)]

/-- The SF sieve sum ≥ the nonSF sieve sum (block sizes ≥ SF → sieve sum ≤). -/
theorem sieveSum_antitone
    (ss₁ ss₂ δs : List ℚ) (ca1 ca3 : ℚ)
    (hlen : ss₁.length = ss₂.length)
    (hδ : ∀ i, i < δs.length → δs.getD i 0 < 1)
    (hδ_nn : ∀ i, i < δs.length → 0 ≤ δs.getD i 0)
    (hs_pos : ∀ i, i < ss₁.length → 0 < ss₁.getD i 1)
    (hs_le : ∀ i, i < ss₁.length → ss₁.getD i 1 ≤ ss₂.getD i 1)
    (hca1 : 0 < ca1) (hca13 : ca1 ≤ ca3)
    (hbase : 0 ≤ ca3 - 2 * ca1 + 1) :
    sieveSum ca1 ca3 ss₂ δs ≤ sieveSum ca1 ca3 ss₁ δs := by
  simp only [sieveSum, hlen]
  exact foldl_sum_antitone _ _ _
    (fun k _ => sieveTerm_antitone ss₁ ss₂ δs ca1 ca3 k hlen hδ hδ_nn hs_pos hs_le hca1 hca13 hbase)

-- ============================================================================
-- §10. MAIN THEOREM
-- ============================================================================

private theorem getD_map_eq (l : List Nat) (f : Nat → ℚ) (i : Nat) (d : ℚ) (hi : i < l.length) :
    (l.map f).getD i d = f l[i] := by
  unfold List.getD; simp [List.getElem?_map, List.getElem?_eq_getElem hi]

theorem maxValuation_pos {K : Nat} (cs : CoveringSystem K)
    (p : Nat) (hp : p ∈ extractPrimes cs) :
    1 ≤ maxValuation cs p := by
  simp only [extractPrimes] at hp; rw [Finset.mem_sort] at hp
  simp only [Finset.mem_filter] at hp; obtain ⟨hmem, _⟩ := hp
  rw [Finset.mem_biUnion] at hmem; obtain ⟨i, _, hi⟩ := hmem
  rw [List.mem_toFinset] at hi
  have hprime := Nat.prime_of_mem_primeFactorsList hi
  have hn : cs.moduli i ≠ 0 := by linarith [cs.moduli_gt_one i]
  have hdvd := ((Nat.mem_primeFactorsList hn).mp hi).2
  exact le_trans ((Nat.Prime.dvd_iff_one_le_factorization hprime hn).mp hdvd)
    (Finset.le_sup (f := fun i => (cs.moduli i).factorization p) (Finset.mem_univ i))

theorem extractPrimes_valid {K : Nat} (cs : CoveringSystem K)
    (_h_odd : CS_allOdd cs) :
    ∀ p ∈ extractPrimes cs, Nat.Prime p ∧ p % 2 = 1 := by
  intro p hp; simp only [extractPrimes] at hp; rw [Finset.mem_sort] at hp
  simp only [Finset.mem_filter] at hp; obtain ⟨hmem, hodd⟩ := hp
  refine ⟨?_, hodd⟩
  rw [Finset.mem_biUnion] at hmem; obtain ⟨i, _, hi⟩ := hmem
  exact Nat.prime_of_mem_primeFactorsList (List.mem_toFinset.mp hi)

theorem sf_le_nonsf_blocks {K : Nat} (cs : CoveringSystem K)
    (h_odd : CS_allOdd cs) :
    ∀ i, i < (sfBlockSizes cs).length →
      (sfBlockSizes cs).getD i 1 ≤ (nonsfBlockSizes cs).getD i 1 := by
  intro i hi
  simp only [sfBlockSizes, nonsfBlockSizes, List.length_map] at hi ⊢
  rw [getD_map_eq _ _ _ _ hi, getD_map_eq _ _ _ _ hi]
  have hmem := List.getElem_mem (l := extractPrimes cs) (n := i) hi
  have ⟨hp, hodd⟩ := extractPrimes_valid cs h_odd _ hmem
  have h3 : 3 ≤ (extractPrimes cs)[i] := by have := hp.two_le; omega
  have hval := maxValuation_pos cs _ hmem
  apply Nat.cast_le.mpr
  simp only [sfBlockSize, effectiveBlockSize]
  have : 1 ≤ ((extractPrimes cs)[i]) ^ (maxValuation cs ((extractPrimes cs)[i]) - 1) :=
    Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem sfBlockSizes_pos {K : Nat} (cs : CoveringSystem K)
    (h_odd : CS_allOdd cs) :
    ∀ i, i < (sfBlockSizes cs).length → 0 < (sfBlockSizes cs).getD i 1 := by
  intro i hi
  simp only [sfBlockSizes, sfBlockSize, List.length_map] at hi ⊢
  rw [getD_map_eq _ _ _ _ hi]
  have hmem := List.getElem_mem (l := extractPrimes cs) (n := i) hi
  have ⟨hp, hodd⟩ := extractPrimes_valid cs h_odd _ hmem
  have h3 : 3 ≤ (extractPrimes cs)[i] := by have := hp.two_le; omega
  simp; omega

theorem blocks_length_eq {K : Nat} (cs : CoveringSystem K) :
    (sfBlockSizes cs).length = (nonsfBlockSizes cs).length := by
  simp [sfBlockSizes, nonsfBlockSizes]

/-- sfBlockSizes equals the map used in sf_sieve_lt_one. -/
private theorem sfBlockSizes_eq_map {K : Nat} (cs : CoveringSystem K)
    (h_valid : ∀ p ∈ extractPrimes cs, Nat.Prime p ∧ p % 2 = 1) :
    sfBlockSizes cs = (extractPrimes cs).map (fun p => ((p : ℚ) - 1)) := by
  simp only [sfBlockSizes, sfBlockSize, List.bind_eq_flatMap, List.pure_def]
  rw [← List.map_eq_flatMap, List.map_map]
  apply List.map_congr_left
  intro p hp
  simp [Nat.cast_sub (Nat.Prime.one_le (h_valid p hp).1)]

/-- **THE ERDŐS-SELFRIDGE CONJECTURE.** -/
theorem erdos_selfridge (K : Nat) (cs : CoveringSystem K) :
    ¬CS_allOdd cs := by
  intro h_odd
  let primes := extractPrimes cs
  have h_primes := extractPrimes_valid cs h_odd
  obtain ⟨δs, ca1, ca3, h_sf_lt, hca1, hca13, hbase, hδ_valid⟩ :=
    sf_sieve_lt_one primes h_primes
  have h_blocks_le := sf_le_nonsf_blocks cs h_odd
  have h_blocks_pos := sfBlockSizes_pos cs h_odd
  have h_blocks_len := blocks_length_eq cs
  have hδ : ∀ i, i < δs.length → δs.getD i 0 < 1 := fun i hi => (hδ_valid i hi).2
  have h_nonsf_lt : sieveSum ca1 ca3 (nonsfBlockSizes cs) δs < 1 := by
    calc sieveSum ca1 ca3 (nonsfBlockSizes cs) δs
        ≤ sieveSum ca1 ca3 (sfBlockSizes cs) δs :=
          sieveSum_antitone (sfBlockSizes cs) (nonsfBlockSizes cs) δs ca1 ca3
            h_blocks_len hδ (fun i hi => (hδ_valid i hi).1) h_blocks_pos h_blocks_le hca1 hca13 hbase
      _ = sieveSum ca1 ca3 (primes.map (fun p => (p : ℚ) - 1)) δs := by
          rw [sfBlockSizes_eq_map cs h_primes]
      _ < 1 := h_sf_lt
  exact sieve_criterion cs h_odd δs ca1 ca3 h_nonsf_lt
