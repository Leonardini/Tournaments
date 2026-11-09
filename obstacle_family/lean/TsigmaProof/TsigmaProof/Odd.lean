import TsigmaProof.Common

/-! # The odd family: loads of the completion of `H_{2k+9}`, k ≥ 1

Generated mechanically from Table `tbl:odd-orders` of paper 1. -/

namespace Tsigma.Odd

inductive V where
  | N0 | N1 | N2 | N3 | P1 | P2 | F | G | H | U (i : ℕ) | W (i : ℕ)
  deriving DecidableEq

/-- The vertices: the fixed ones and `U i`, `W i` for `1 ≤ i ≤ k`. -/
def valid (k : ℕ) : V → Prop
  | .U i => 1 ≤ i ∧ i ≤ k
  | .W i => 1 ≤ i ∧ i ≤ k
  | _ => True

/-- The arcs of `H_{2k+9}` (Section sec:family-def): the zigzag path `P1, W1, U1, ..., Wk, Uk, H`,
the arcs at the hubs `N1` and `N2`, and eighteen more. -/
def garc (k : ℕ) : V → V → Prop
  | .N0, .N2 => True
  | .N0, .N3 => True
  | .N1, .N2 => True
  | .N1, .N3 => True
  | .N2, .N3 => True
  | .P1, .N0 => True
  | .N0, .P2 => True
  | .N2, .P2 => True
  | .P2, .N1 => True
  | .P2, .G => True
  | .N2, .F => True
  | .N3, .F => True
  | .F, .N0 => True
  | .F, .N1 => True
  | .N3, .G => True
  | .G, .N0 => True
  | .G, .N2 => True
  | .N3, .H => True
  | .N1, .P1 => True
  | .N2, .P1 => True
  | .H, .N1 => True
  | .H, .N2 => True
  | .N1, .U i => 1 ≤ i ∧ i ≤ k
  | .N2, .U i => 1 ≤ i ∧ i ≤ k
  | .W i, .N1 => 1 ≤ i ∧ i ≤ k
  | .W i, .N2 => 1 ≤ i ∧ i ≤ k
  | .P1, .W j => j = 1 ∧ 1 ≤ k
  | .P1, .H => k = 0
  | .U i, .W j => 1 ≤ i ∧ ((j = i ∧ i ≤ k) ∨ (j = i + 1 ∧ i + 1 ≤ k))
  | .U i, .H => i = k ∧ 1 ≤ k
  | _, _ => False

/-- The order along which `H_{2k+9}` is completed:
`N2, W1, ..., Wk, N3, F, H, G, N0, P1, P2, N1, U1, ..., Uk`. -/
def sigma (k : ℕ) : V → ℕ
  | .N2 => 0
  | .W i => i
  | .N3 => k + 1
  | .F => k + 2
  | .H => k + 3
  | .G => k + 4
  | .N0 => k + 5
  | .P1 => k + 6
  | .P2 => k + 7
  | .N1 => k + 8
  | .U i => k + 8 + i

/-- The arcs of the completion: those of the obstacle, and every other pair as in `sigma`. -/
def tarc (k : ℕ) (x y : V) : Prop :=
  valid k x ∧ valid k y ∧ x ≠ y ∧ (garc k x y ∨ (¬ garc k y x ∧ sigma k x < sigma k y))

/-- the order `h_1` of Table tbl:odd-orders -/
def r_h1 (k : ℕ) : V → ℕ
  | .N0 => 4 * (4 * k + 8) + (0)
  | .N1 => 5 * (4 * k + 8) + (0)
  | .N2 => 6 * (4 * k + 8) + (0)
  | .N3 => 7 * (4 * k + 8) + (0)
  | .P1 => 8 * (4 * k + 8) + (0)
  | .P2 => 9 * (4 * k + 8) + (0)
  | .F => 1 * (4 * k + 8) + (0)
  | .G => 3 * (4 * k + 8) + (0)
  | .H => 2 * (4 * k + 8) + (0)
  | .U i => 10 * (4 * k + 8) + (i)
  | .W i => 0 * (4 * k + 8) + (i)

/-- the order `h_2` of Table tbl:odd-orders -/
def r_h2 (k : ℕ) : V → ℕ
  | .N0 => 4 * (4 * k + 8) + (0)
  | .N1 => 5 * (4 * k + 8) + (0)
  | .N2 => 6 * (4 * k + 8) + (0)
  | .N3 => 7 * (4 * k + 8) + (0)
  | .P1 => 9 * (4 * k + 8) + (0)
  | .P2 => 2 * (4 * k + 8) + (0)
  | .F => 8 * (4 * k + 8) + (0)
  | .G => 3 * (4 * k + 8) + (0)
  | .H => 1 * (4 * k + 8) + (0)
  | .U i => 10 * (4 * k + 8) + (i)
  | .W i => 0 * (4 * k + 8) + (i)

/-- the order `R_1` of Table tbl:odd-orders -/
def r_R1 (k : ℕ) : V → ℕ
  | .N0 => 1 * (4 * k + 8) + (0)
  | .N1 => 7 * (4 * k + 8) + (0)
  | .N2 => 9 * (4 * k + 8) + (0)
  | .N3 => 4 * (4 * k + 8) + (0)
  | .P1 => 0 * (4 * k + 8) + (0)
  | .P2 => 6 * (4 * k + 8) + (0)
  | .F => 10 * (4 * k + 8) + (0)
  | .G => 8 * (4 * k + 8) + (0)
  | .H => 5 * (4 * k + 8) + (0)
  | .U i => 2 * (4 * k + 8) + (i)
  | .W i => 3 * (4 * k + 8) + (i)

/-- the order `R_2` of Table tbl:odd-orders -/
def r_R2 (k : ℕ) : V → ℕ
  | .N0 => 1 * (4 * k + 8) + (0)
  | .N1 => 9 * (4 * k + 8) + (0)
  | .N2 => 7 * (4 * k + 8) + (0)
  | .N3 => 3 * (4 * k + 8) + (0)
  | .P1 => 0 * (4 * k + 8) + (0)
  | .P2 => 5 * (4 * k + 8) + (0)
  | .F => 8 * (4 * k + 8) + (0)
  | .G => 6 * (4 * k + 8) + (0)
  | .H => 4 * (4 * k + 8) + (0)
  | .U i => 2 * (4 * k + 8) + (4 * i + 1)
  | .W i => 2 * (4 * k + 8) + (4 * i + 3)

/-- the order `R_3` of Table tbl:odd-orders -/
def r_R3 (k : ℕ) : V → ℕ
  | .N0 => 2 * (4 * k + 8) + (0)
  | .N1 => 0 * (4 * k + 8) + (0)
  | .N2 => 6 * (4 * k + 8) + (0)
  | .N3 => 4 * (4 * k + 8) + (0)
  | .P1 => 1 * (4 * k + 8) + (0)
  | .P2 => 8 * (4 * k + 8) + (0)
  | .F => 7 * (4 * k + 8) + (0)
  | .G => 9 * (4 * k + 8) + (0)
  | .H => 5 * (4 * k + 8) + (0)
  | .U i => 3 * (4 * k + 8) + (4 * i + 1)
  | .W i => 3 * (4 * k + 8) + (4 * i + 3)

/-- the order `R_4` of Table tbl:odd-orders -/
def r_R4 (k : ℕ) : V → ℕ
  | .N0 => 2 * (4 * k + 8) + (0)
  | .N1 => 9 * (4 * k + 8) + (0)
  | .N2 => 0 * (4 * k + 8) + (0)
  | .N3 => 4 * (4 * k + 8) + (0)
  | .P1 => 1 * (4 * k + 8) + (0)
  | .P2 => 7 * (4 * k + 8) + (0)
  | .F => 6 * (4 * k + 8) + (0)
  | .G => 8 * (4 * k + 8) + (0)
  | .H => 5 * (4 * k + 8) + (0)
  | .U i => 3 * (4 * k + 8) + (4 * i + 1)
  | .W i => 3 * (4 * k + 8) + (4 * i + 3)

/-- the order `R_5` of Table tbl:odd-orders -/
def r_R5 (k : ℕ) : V → ℕ
  | .N0 => 3 * (4 * k + 8) + (0)
  | .N1 => 1 * (4 * k + 8) + (0)
  | .N2 => 8 * (4 * k + 8) + (0)
  | .N3 => 5 * (4 * k + 8) + (0)
  | .P1 => 2 * (4 * k + 8) + (0)
  | .P2 => 0 * (4 * k + 8) + (0)
  | .F => 9 * (4 * k + 8) + (0)
  | .G => 7 * (4 * k + 8) + (0)
  | .H => 6 * (4 * k + 8) + (0)
  | .U i => 4 * (4 * k + 8) + (4 * i + 1)
  | .W i => 4 * (4 * k + 8) + (4 * i + 3)

/-- the order `R_6` of Table tbl:odd-orders -/
def r_R6 (k : ℕ) : V → ℕ
  | .N0 => 9 * (4 * k + 8) + (0)
  | .N1 => 1 * (4 * k + 8) + (0)
  | .N2 => 7 * (4 * k + 8) + (0)
  | .N3 => 2 * (4 * k + 8) + (0)
  | .P1 => 4 * (4 * k + 8) + (0)
  | .P2 => 0 * (4 * k + 8) + (0)
  | .F => 8 * (4 * k + 8) + (0)
  | .G => 3 * (4 * k + 8) + (0)
  | .H => 6 * (4 * k + 8) + (0)
  | .U i => 5 * (4 * k + 8) + (4 * i + 1)
  | .W i => 5 * (4 * k + 8) + (4 * i + 3)

/-- the order `R_7` of Table tbl:odd-orders -/
def r_R7 (k : ℕ) : V → ℕ
  | .N0 => 4 * (4 * k + 8) + (0)
  | .N1 => 7 * (4 * k + 8) + (0)
  | .N2 => 0 * (4 * k + 8) + (0)
  | .N3 => 1 * (4 * k + 8) + (0)
  | .P1 => 3 * (4 * k + 8) + (4 * k + 1)
  | .P2 => 5 * (4 * k + 8) + (0)
  | .F => 2 * (4 * k + 8) + (0)
  | .G => 6 * (4 * k + 8) + (0)
  | .H => 3 * (4 * k + 8) + (3)
  | .U i => 3 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => 3 * (4 * k + 8) + (4 * (k - i) + 7)

/-- the order `R_8` of Table tbl:odd-orders -/
def r_R8 (k : ℕ) : V → ℕ
  | .N0 => 5 * (4 * k + 8) + (0)
  | .N1 => 7 * (4 * k + 8) + (0)
  | .N2 => 0 * (4 * k + 8) + (0)
  | .N3 => 1 * (4 * k + 8) + (0)
  | .P1 => 4 * (4 * k + 8) + (4 * k + 1)
  | .P2 => 6 * (4 * k + 8) + (0)
  | .F => 2 * (4 * k + 8) + (0)
  | .G => 3 * (4 * k + 8) + (0)
  | .H => 4 * (4 * k + 8) + (3)
  | .U i => 4 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => 4 * (4 * k + 8) + (4 * (k - i) + 7)

/-- the order `R_9` of Table tbl:odd-orders -/
def r_R9 (k : ℕ) : V → ℕ
  | .N0 => 5 * (4 * k + 8) + (0)
  | .N1 => 1 * (4 * k + 8) + (0)
  | .N2 => 6 * (4 * k + 8) + (0)
  | .N3 => 2 * (4 * k + 8) + (0)
  | .P1 => 4 * (4 * k + 8) + (4 * k + 1)
  | .P2 => 0 * (4 * k + 8) + (0)
  | .F => 7 * (4 * k + 8) + (0)
  | .G => 3 * (4 * k + 8) + (0)
  | .H => 4 * (4 * k + 8) + (3)
  | .U i => 4 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => 4 * (4 * k + 8) + (4 * (k - i) + 7)

/-- the order `R_{10}` of Table tbl:odd-orders -/
def r_R10 (k : ℕ) : V → ℕ
  | .N0 => 7 * (4 * k + 8) + (0)
  | .N1 => 6 * (4 * k + 8) + (0)
  | .N2 => 0 * (4 * k + 8) + (0)
  | .N3 => 1 * (4 * k + 8) + (0)
  | .P1 => 5 * (4 * k + 8) + (4 * k + 1)
  | .P2 => 3 * (4 * k + 8) + (0)
  | .F => 2 * (4 * k + 8) + (0)
  | .G => 4 * (4 * k + 8) + (0)
  | .H => 5 * (4 * k + 8) + (3)
  | .U i => 5 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => 5 * (4 * k + 8) + (4 * (k - i) + 7)

/-- the order `R_{11}` of Table tbl:odd-orders -/
def r_R11 (k : ℕ) : V → ℕ
  | .N0 => 7 * (4 * k + 8) + (0)
  | .N1 => 5 * (4 * k + 8) + (0)
  | .N2 => 0 * (4 * k + 8) + (0)
  | .N3 => 1 * (4 * k + 8) + (0)
  | .P1 => 6 * (4 * k + 8) + (4 * k + 1)
  | .P2 => 3 * (4 * k + 8) + (0)
  | .F => 2 * (4 * k + 8) + (0)
  | .G => 4 * (4 * k + 8) + (0)
  | .H => 6 * (4 * k + 8) + (3)
  | .U i => 6 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => 6 * (4 * k + 8) + (4 * (k - i) + 7)

/-- the order `R_{12}` of Table tbl:odd-orders -/
def r_R12 (k : ℕ) : V → ℕ
  | .N0 => 7 * (4 * k + 8) + (0)
  | .N1 => 2 * (4 * k + 8) + (0)
  | .N2 => 0 * (4 * k + 8) + (0)
  | .N3 => 3 * (4 * k + 8) + (0)
  | .P1 => 6 * (4 * k + 8) + (4 * k + 1)
  | .P2 => 1 * (4 * k + 8) + (0)
  | .F => 4 * (4 * k + 8) + (0)
  | .G => 5 * (4 * k + 8) + (0)
  | .H => 6 * (4 * k + 8) + (3)
  | .U i => 6 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => 6 * (4 * k + 8) + (4 * (k - i) + 7)

/-- the order `R_{13}` of Table tbl:odd-orders -/
def r_R13 (k : ℕ) : V → ℕ
  | .N0 => 7 * (4 * k + 8) + (0)
  | .N1 => 1 * (4 * k + 8) + (0)
  | .N2 => 4 * (4 * k + 8) + (0)
  | .N3 => 2 * (4 * k + 8) + (0)
  | .P1 => 6 * (4 * k + 8) + (4 * k + 1)
  | .P2 => 0 * (4 * k + 8) + (0)
  | .F => 5 * (4 * k + 8) + (0)
  | .G => 3 * (4 * k + 8) + (0)
  | .H => 6 * (4 * k + 8) + (3)
  | .U i => 6 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => 6 * (4 * k + 8) + (4 * (k - i) + 7)

/-- the order `E_j` of Table tbl:odd-orders -/
def r_Ej (k : ℕ) (p : ℕ) : V → ℕ
  | .N0 => 1 * (4 * k + 8) + (0)
  | .N1 => 8 * (4 * k + 8) + (0)
  | .N2 => 2 * (4 * k + 8) + (4 * p + 4)
  | .N3 => 3 * (4 * k + 8) + (0)
  | .P1 => 0 * (4 * k + 8) + (0)
  | .P2 => 6 * (4 * k + 8) + (0)
  | .F => 4 * (4 * k + 8) + (0)
  | .G => 7 * (4 * k + 8) + (0)
  | .H => 5 * (4 * k + 8) + (0)
  | .U i => 2 * (4 * k + 8) + (4 * i + 1)
  | .W i => 2 * (4 * k + 8) + (4 * i + 3)

/-- the order `E'_j` of Table tbl:odd-orders -/
def r_Epj (k : ℕ) (p : ℕ) : V → ℕ
  | .N0 => 2 * (4 * k + 8) + (0)
  | .N1 => 4 * (4 * k + 8) + (4 * p + 4)
  | .N2 => 8 * (4 * k + 8) + (0)
  | .N3 => 5 * (4 * k + 8) + (0)
  | .P1 => 1 * (4 * k + 8) + (0)
  | .P2 => 3 * (4 * k + 8) + (0)
  | .F => 0 * (4 * k + 8) + (0)
  | .G => 7 * (4 * k + 8) + (0)
  | .H => 6 * (4 * k + 8) + (0)
  | .U i => 4 * (4 * k + 8) + (4 * i + 1)
  | .W i => 4 * (4 * k + 8) + (4 * i + 3)

/-- the order `O_s` of Table tbl:odd-orders -/
def r_Os (k : ℕ) (p : ℕ) : V → ℕ
  | .N0 => 5 * (4 * k + 8) + (0)
  | .N1 => 0 * (4 * k + 8) + (0)
  | .N2 => 3 * (4 * k + 8) + (4 * (k - p) + 4)
  | .N3 => 1 * (4 * k + 8) + (0)
  | .P1 => 3 * (4 * k + 8) + (4 * k + 1)
  | .P2 => 6 * (4 * k + 8) + (0)
  | .F => 4 * (4 * k + 8) + (0)
  | .G => 2 * (4 * k + 8) + (0)
  | .H => 3 * (4 * k + 8) + (3)
  | .U i => 3 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => 3 * (4 * k + 8) + (4 * (k - i) + 7)

/-- the order `O'_s` of Table tbl:odd-orders -/
def r_Ops (k : ℕ) (p : ℕ) : V → ℕ
  | .N0 => 6 * (4 * k + 8) + (0)
  | .N1 => 5 * (4 * k + 8) + (4 * (k - p) + 4)
  | .N2 => 0 * (4 * k + 8) + (0)
  | .N3 => 1 * (4 * k + 8) + (0)
  | .P1 => 5 * (4 * k + 8) + (4 * k + 1)
  | .P2 => 3 * (4 * k + 8) + (0)
  | .F => 2 * (4 * k + 8) + (0)
  | .G => 4 * (4 * k + 8) + (0)
  | .H => 5 * (4 * k + 8) + (3)
  | .U i => 5 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => 5 * (4 * k + 8) + (4 * (k - i) + 7)

/-- The load of `x → y`: the total weight of the orders that reverse it. -/
def load (k : ℕ) (x y : V) : ℕ :=
  (k + 7) * ind (r_h1 k) x y
  + (k + 1) * ind (r_h2 k) x y
  + 1 * ind (r_R1 k) x y
  + 1 * ind (r_R2 k) x y
  + 1 * ind (r_R3 k) x y
  + 1 * ind (r_R4 k) x y
  + 1 * ind (r_R5 k) x y
  + 1 * ind (r_R6 k) x y
  + 1 * ind (r_R7 k) x y
  + 1 * ind (r_R8 k) x y
  + 1 * ind (r_R9 k) x y
  + 1 * ind (r_R10 k) x y
  + 1 * ind (r_R11 k) x y
  + 1 * ind (r_R12 k) x y
  + 1 * ind (r_R13 k) x y
  + famsum (fun t => r_Ej k (t + 0)) (k + 1) x y
  + famsum (fun t => r_Epj k (t + 0)) (k + 1) x y
  + famsum (fun t => r_Os k (t + 1)) (k) x y
  + famsum (fun t => r_Ops k (t + 1)) (k) x y

theorem load_W_N0 (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.N0) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W i) (.N0) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W i) (.N0) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W i) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W i) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W i) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W i) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W i) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W i) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W i) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W i) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W i) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W i) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W i) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W i) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W i) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W i) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W i) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W i) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W i) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_W_N1 (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.N1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W i) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W i) (.N1) = (i) - (0) :=
    famsum_interval (0) (i) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W i) (.N1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W i) (.N1) = (k) - ((i) - (1)) :=
    famsum_interval ((i) - (1)) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W i) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W i) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W i) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W i) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W i) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W i) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W i) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W i) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W i) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W i) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W i) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W i) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W i) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W i) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W i) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_W_N2 (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.N2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W i) (.N2) = (i) - (0) :=
    famsum_interval (0) (i) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W i) (.N2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W i) (.N2) = (k) - ((i) - (1)) :=
    famsum_interval ((i) - (1)) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W i) (.N2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W i) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W i) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W i) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W i) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W i) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W i) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W i) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W i) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W i) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W i) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W i) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W i) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W i) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W i) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W i) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_W_N3 (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.N3) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W i) (.N3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W i) (.N3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W i) (.N3) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W i) (.N3) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W i) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W i) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W i) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W i) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W i) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W i) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W i) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W i) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W i) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W i) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W i) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W i) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W i) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W i) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W i) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_W_P2 (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.P2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W i) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W i) (.P2) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W i) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W i) (.P2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W i) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W i) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W i) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W i) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W i) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W i) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W i) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W i) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W i) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W i) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W i) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W i) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W i) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W i) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W i) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_W_F (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.F) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W i) (.F) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W i) (.F) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W i) (.F) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W i) (.F) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W i) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W i) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W i) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W i) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W i) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W i) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W i) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W i) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W i) (.F) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W i) (.F) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W i) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W i) (.F) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W i) (.F) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W i) (.F) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W i) (.F) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_W_G (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.G) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W i) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W i) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W i) (.G) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W i) (.G) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W i) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W i) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W i) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W i) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W i) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W i) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W i) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W i) (.G) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W i) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W i) (.G) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W i) (.G) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W i) (.G) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W i) (.G) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W i) (.G) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W i) (.G) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_W_H (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.H) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W i) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W i) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W i) (.H) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W i) (.H) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W i) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W i) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W i) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W i) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W i) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W i) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W i) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W i) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W i) (.H) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W i) (.H) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W i) (.H) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W i) (.H) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W i) (.H) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W i) (.H) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W i) (.H) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_W_P1 (k i : ℕ) (hk : 1 ≤ k) (hc : 2 ≤ i ∧ i ≤ k) :
    load k (.W i) (.P1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W i) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W i) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W i) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W i) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W i) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W i) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W i) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W i) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W i) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W i) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W i) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W i) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W i) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W i) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W i) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W i) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W i) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W i) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W i) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_P1_W1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.P1) (.W 1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.P1) (.W 1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.P1) (.W 1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.P1) (.W 1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.P1) (.W 1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.P1) (.W 1) = 1 :=
    ind_of_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.P1) (.W 1) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P1) (.W 1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N0_U (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.N0) (.U i) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N0) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N0) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N0) (.U i) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N0) (.U i) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N1_U (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.N1) (.U i) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N1) (.U i) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N1) (.U i) = (1 + k) - (i) :=
    famsum_interval (i) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N1) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N1) (.U i) = (i) - (0) :=
    famsum_interval (0) (i) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N2_U (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.N2) (.U i) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N2) (.U i) = (1 + k) - (i) :=
    famsum_interval (i) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N2) (.U i) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N2) (.U i) = (i) - (0) :=
    famsum_interval (0) (i) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N2) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N3_U (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.N3) (.U i) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N3) (.U i) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N3) (.U i) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N3) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N3) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N3) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N3) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N3) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N3) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N3) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N3) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N3) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N3) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N3) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N3) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N3) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N3) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N3) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N3) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N3) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_P1_U (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.P1) (.U i) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.P1) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.P1) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.P1) (.U i) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.P1) (.U i) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.P1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.P1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P1) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P1) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_P2_U (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.P2) (.U i) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.P2) (.U i) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.P2) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.P2) (.U i) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.P2) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.P2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.P2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P2) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P2) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_F_U (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.F) (.U i) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.F) (.U i) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.F) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.F) (.U i) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.F) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.F) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.F) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.F) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.F) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.F) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.F) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.F) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.F) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.F) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.F) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.F) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.F) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.F) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.F) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.F) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_G_U (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.G) (.U i) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.G) (.U i) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.G) (.U i) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.G) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.G) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.G) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.G) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.G) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.G) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.G) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.G) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.G) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.G) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.G) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.G) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.G) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.G) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.G) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.G) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.G) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_H_U (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i + 1 ≤ k) :
    load k (.H) (.U i) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.H) (.U i) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.H) (.U i) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.H) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.H) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.H) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.H) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.H) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.H) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.H) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.H) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.H) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.H) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.H) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.H) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.H) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.H) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.H) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.H) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.H) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_Uk_H (k : ℕ) (hk : 1 ≤ k) :
    load k (.U k) (.H) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.U k) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.U k) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.U k) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.U k) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.U k) (.H) = 1 :=
    ind_of_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.U k) (.H) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.U k) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_Wa_Wb (k a b : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ a ∧ a < b ∧ b ≤ k) :
    load k (.W a) (.W b) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W a) (.W b) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W a) (.W b) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W a) (.W b) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W a) (.W b) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W a) (.W b) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W a) (.W b) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W a) (.W b) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W a) (.W b) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W a) (.W b) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W a) (.W b) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W a) (.W b) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W a) (.W b) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W a) (.W b) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W a) (.W b) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W a) (.W b) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W a) (.W b) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W a) (.W b) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W a) (.W b) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W a) (.W b) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_Ua_Ub (k a b : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ a ∧ a < b ∧ b ≤ k) :
    load k (.U a) (.U b) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.U a) (.U b) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.U a) (.U b) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.U a) (.U b) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.U a) (.U b) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.U a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.U a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.U a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.U a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.U a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.U a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.U a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_Ui_Wi (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.U i) (.W i) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.U i) (.W i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.U i) (.W i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.U i) (.W i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.U i) (.W i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.U i) (.W i) = 1 :=
    ind_of_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.U i) (.W i) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.U i) (.W i) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_Ui_Wi1 (k i : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ i ∧ i + 1 ≤ k) :
    load k (.U i) (.W (i + 1)) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.U i) (.W (i + 1)) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.U i) (.W (i + 1)) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.U i) (.W (i + 1)) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.U i) (.W (i + 1)) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.U i) (.W (i + 1)) = 1 :=
    ind_of_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.U i) (.W (i + 1)) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.U i) (.W (i + 1)) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_Wa_Ub_far (k a b : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ b ∧ b + 2 ≤ a ∧ a ≤ k) :
    load k (.W a) (.U b) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W a) (.U b) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W a) (.U b) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W a) (.U b) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W a) (.U b) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_Wa_Ub_back (k a b : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ a ∧ a + 1 ≤ b ∧ b ≤ k) :
    load k (.W a) (.U b) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.W a) (.U b) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.W a) (.U b) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.W a) (.U b) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.W a) (.U b) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.W a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.W a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N0_N1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N0) (.N1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N0) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N0) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N0) (.N1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N0) (.N1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N0) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N0) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N0) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N0) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N0) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N0) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N0) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N0) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N0) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N0) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N0) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N0) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N0) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N0) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N0) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N0_N2 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N0) (.N2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N0) (.N2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N0) (.N2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N0) (.N2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N0) (.N2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N0) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N0) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N0) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N0) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N0) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N0) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N0) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N0) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N0) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N0) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N0) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N0) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N0) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N0) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N0) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N0_N3 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N0) (.N3) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N0) (.N3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N0) (.N3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N0) (.N3) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N0) (.N3) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N0) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N0) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N0) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N0) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N0) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N0) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N0) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N0) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N0) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N0) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N0) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N0) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N0) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N0) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N0) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N0_P2 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N0) (.P2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N0) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N0) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N0) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N0) (.P2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N0) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N0) (.P2) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N0) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N0) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N0) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N0) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N0) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N0) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N0) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N0) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N0) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N0) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N0) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N0) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N0) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N1_N2 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N1) (.N2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N1) (.N2) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N1) (.N2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N1) (.N2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N1) (.N2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N1) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N1) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N1) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N1) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N1) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N1) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N1) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N1) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N1) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N1) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N1) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N1) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N1) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N1) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N1) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N1_N3 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N1) (.N3) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N1) (.N3) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N1) (.N3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N1) (.N3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N1) (.N3) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N1) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N1) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N1) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N1) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N1) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N1) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N1) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N1) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N1) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N1) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N1) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N1) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N1) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N1) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N1) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N1_P1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N1) (.P1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N1) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N1) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N1) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N1) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N1) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N1) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N1) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N1) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N1) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N1) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N1) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N1) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N1) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N1) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N1) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N1) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N1) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N1) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N1) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N2_N3 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N2) (.N3) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N2) (.N3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N2) (.N3) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N2) (.N3) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N2) (.N3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N2) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N2) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N2) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N2) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N2) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N2) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N2) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N2) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N2) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N2) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N2) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N2) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N2) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N2) (.N3) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N2) (.N3) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N2_P1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N2) (.P1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N2) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N2) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N2) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N2) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N2_P2 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N2) (.P2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N2) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N2) (.P2) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N2) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N2) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N2) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N2) (.P2) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N2) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N2) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N2) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N2) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N2) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N2) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N2) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N2) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N2) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N2) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N2) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N2) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N2) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N2_F (k : ℕ) (hk : 1 ≤ k) :
    load k (.N2) (.F) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N2) (.F) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N2) (.F) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N2) (.F) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N2) (.F) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N2) (.F) = 1 :=
    ind_of_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N2) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N3_P1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N3) (.P1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N3) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N3) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N3) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N3) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N3) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N3) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N3) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N3) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N3) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N3_P2 (k : ℕ) (hk : 1 ≤ k) :
    load k (.N3) (.P2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N3) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N3) (.P2) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N3) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N3) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N3_F (k : ℕ) (hk : 1 ≤ k) :
    load k (.N3) (.F) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N3) (.F) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N3) (.F) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N3) (.F) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N3) (.F) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N3) (.F) = 1 :=
    ind_of_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N3) (.F) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N3_G (k : ℕ) (hk : 1 ≤ k) :
    load k (.N3) (.G) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N3) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N3) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N3) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N3) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N3) (.G) = 1 :=
    ind_of_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N3) (.G) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N3) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_N3_H (k : ℕ) (hk : 1 ≤ k) :
    load k (.N3) (.H) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.N3) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.N3) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.N3) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.N3) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.N3) (.H) = 1 :=
    ind_of_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.N3) (.H) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.N3) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_P1_N0 (k : ℕ) (hk : 1 ≤ k) :
    load k (.P1) (.N0) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.P1) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.P1) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.P1) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.P1) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.P1) (.N0) = 1 :=
    ind_of_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.P1) (.N0) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P1) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_P1_P2 (k : ℕ) (hk : 1 ≤ k) :
    load k (.P1) (.P2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.P1) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.P1) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.P1) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.P1) (.P2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_P2_N1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.P2) (.N1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.P2) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.P2) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.P2) (.N1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.P2) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.P2) (.N1) = 1 :=
    ind_of_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P2) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P2) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_P2_G (k : ℕ) (hk : 1 ≤ k) :
    load k (.P2) (.G) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.P2) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.P2) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.P2) (.G) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.P2) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.P2) (.G) = 1 :=
    ind_of_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P2) (.G) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P2) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_F_N0 (k : ℕ) (hk : 1 ≤ k) :
    load k (.F) (.N0) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.F) (.N0) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.F) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.F) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.F) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.F) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.F) (.N0) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.F) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.F) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.F) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.F) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.F) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.F) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.F) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.F) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.F) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.F) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.F) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.F) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.F) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_F_N1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.F) (.N1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.F) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.F) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.F) (.N1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.F) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.F) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.F) (.N1) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.F) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.F) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.F) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.F) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.F) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.F) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.F) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.F) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.F) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.F) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.F) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.F) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.F) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_F_P1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.F) (.P1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.F) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.F) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.F) (.P1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.F) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.F) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.F) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.F) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.F) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.F) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.F) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.F) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.F) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.F) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.F) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.F) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.F) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.F) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.F) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.F) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_F_P2 (k : ℕ) (hk : 1 ≤ k) :
    load k (.F) (.P2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.F) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.F) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.F) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.F) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.F) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.F) (.P2) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.F) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.F) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.F) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.F) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.F) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.F) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.F) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.F) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.F) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.F) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.F) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.F) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.F) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_F_G (k : ℕ) (hk : 1 ≤ k) :
    load k (.F) (.G) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.F) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.F) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.F) (.G) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.F) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.F) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.F) (.G) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.F) (.G) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.F) (.G) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.F) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.F) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.F) (.G) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.F) (.G) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.F) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.F) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.F) (.G) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.F) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.F) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.F) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.F) (.G) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_F_H (k : ℕ) (hk : 1 ≤ k) :
    load k (.F) (.H) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.F) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.F) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.F) (.H) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.F) (.H) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.F) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.F) (.H) = 1 :=
    ind_of_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.F) (.H) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.F) (.H) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.F) (.H) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.F) (.H) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.F) (.H) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.F) (.H) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.F) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.F) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.F) (.H) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.F) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.F) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.F) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.F) (.H) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_G_N0 (k : ℕ) (hk : 1 ≤ k) :
    load k (.G) (.N0) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.G) (.N0) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.G) (.N0) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.G) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.G) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.G) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.G) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.G) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.G) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.G) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.G) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.G) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.G) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.G) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.G) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.G) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.G) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.G) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.G) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.G) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_G_N1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.G) (.N1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.G) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.G) (.N1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.G) (.N1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.G) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.G) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.G) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.G) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.G) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.G) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.G) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.G) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.G) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.G) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.G) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.G) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.G) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.G) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.G) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.G) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_G_N2 (k : ℕ) (hk : 1 ≤ k) :
    load k (.G) (.N2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.G) (.N2) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.G) (.N2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.G) (.N2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.G) (.N2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.G) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.G) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.G) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.G) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.G) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.G) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.G) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.G) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.G) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.G) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.G) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.G) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.G) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.G) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.G) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_G_P1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.G) (.P1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.G) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.G) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.G) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.G) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.G) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.G) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.G) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.G) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.G) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.G) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.G) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.G) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.G) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.G) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.G) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.G) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.G) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.G) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.G) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_H_N0 (k : ℕ) (hk : 1 ≤ k) :
    load k (.H) (.N0) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.H) (.N0) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.H) (.N0) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.H) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.H) (.N0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.H) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.H) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.H) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.H) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.H) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.H) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.H) (.N0) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.H) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.H) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.H) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.H) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.H) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.H) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.H) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.H) (.N0) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_H_N1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.H) (.N1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.H) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.H) (.N1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.H) (.N1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.H) (.N1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.H) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.H) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.H) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.H) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.H) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.H) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.H) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.H) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.H) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.H) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.H) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.H) (.N1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.H) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.H) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.H) (.N1) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_H_N2 (k : ℕ) (hk : 1 ≤ k) :
    load k (.H) (.N2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.H) (.N2) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.H) (.N2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.H) (.N2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.H) (.N2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.H) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.H) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.H) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.H) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.H) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.H) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.H) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.H) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.H) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.H) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.H) (.N2) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.H) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.H) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.H) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.H) (.N2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_H_P1 (k : ℕ) (hk : 1 ≤ k) :
    load k (.H) (.P1) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.H) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.H) (.P1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.H) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.H) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.H) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.H) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.H) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.H) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.H) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.H) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.H) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.H) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.H) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.H) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.H) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.H) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.H) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.H) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.H) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_H_P2 (k : ℕ) (hk : 1 ≤ k) :
    load k (.H) (.P2) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.H) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.H) (.P2) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.H) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.H) (.P2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.H) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.H) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.H) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.H) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.H) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.H) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.H) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.H) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.H) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.H) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.H) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.H) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.H) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.H) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.H) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_H_G (k : ℕ) (hk : 1 ≤ k) :
    load k (.H) (.G) ≤ 2 * k + 8 := by
  have h0 : famsum (fun t => r_Ej k (t + 0)) (k + 1) (.H) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ej]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Epj k (t + 0)) (k + 1) (.H) (.G) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Epj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Os k (t + 1)) (k) (.H) (.G) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Os]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Ops k (t + 1)) (k) (.H) (.G) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ops]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h1 : ind (r_h1 k) (.H) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_h1]; (try split_ifs) <;> omega)
  have e_h2 : ind (r_h2 k) (.H) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_h2]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.H) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.H) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.H) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.H) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.H) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.H) (.G) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.H) (.G) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.H) (.G) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.H) (.G) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.H) (.G) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.H) (.G) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.H) (.G) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.H) (.G) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h1, e_h2, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13]
  omega

theorem load_le (k : ℕ) (hk : 1 ≤ k) (x y : V) (h : tarc k x y) :
    load k x y ≤ 2 * k + 8 := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_N0_N1 k hk
  · exact load_N0_N2 k hk
  · exact load_N0_N3 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_N0_P2 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_N0_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_N1_N2 k hk
  · exact load_N1_N3 k hk
  · exact load_N1_P1 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_N1_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_N2_N3 k hk
  · exact load_N2_P1 k hk
  · exact load_N2_P2 k hk
  · exact load_N2_F k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_N2_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_N3_P1 k hk
  · exact load_N3_P2 k hk
  · exact load_N3_F k hk
  · exact load_N3_G k hk
  · exact load_N3_H k hk
  · have hc : (1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_N3_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_P1_N0 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_P1_P2 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_P1_U k b hk hc
  · have hc : (b = 1) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with rfl
    · exact load_P1_W1 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_P2_N1 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_P2_G k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_P2_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_F_N0 k hk
  · exact load_F_N1 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_F_P1 k hk
  · exact load_F_P2 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_F_G k hk
  · exact load_F_H k hk
  · have hc : (1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_F_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_G_N0 k hk
  · exact load_G_N1 k hk
  · exact load_G_N2 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_G_P1 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_G_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_H_N0 k hk
  · exact load_H_N1 k hk
  · exact load_H_N2 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_H_P1 k hk
  · exact load_H_P2 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_H_G k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (1 ≤ b ∧ b + 1 ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_H_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (a = k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with rfl
    · exact load_Uk_H _ hk
  · have hc : (1 ≤ a ∧ a < b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_Ua_Ub k a b hk hc
  · have hc : (b = a ∧ 1 ≤ a ∧ a ≤ k) ∨ (b = a + 1 ∧ 1 ≤ a ∧ a + 1 ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · exact load_Ui_Wi k _ hk hc
    · exact load_Ui_Wi1 k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_N0 k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_N1 k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_N2 k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_N3 k a hk hc
  · have hc : (2 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_P1 k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_P2 k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_F k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_G k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_H k a hk hc
  · have hc : (1 ≤ b ∧ b + 2 ≤ a ∧ a ≤ k) ∨ (1 ≤ a ∧ a + 1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc | hc
    · exact load_Wa_Ub_far k a b hk hc
    · exact load_Wa_Ub_back k a b hk hc
  · have hc : (1 ≤ a ∧ a < b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_Wa_Wb k a b hk hc

theorem r_h1_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_h1 k x ≠ r_h1 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_h1, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_h2_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_h2 k x ≠ r_h2 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_h2, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R1_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R1 k x ≠ r_R1 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R1, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R2_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R2 k x ≠ r_R2 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R2, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R3_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R3 k x ≠ r_R3 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R3, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R4_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R4 k x ≠ r_R4 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R4, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R5_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R5 k x ≠ r_R5 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R5, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R6_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R6 k x ≠ r_R6 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R6, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R7_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R7 k x ≠ r_R7 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R7, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R8_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R8 k x ≠ r_R8 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R8, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R9_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R9 k x ≠ r_R9 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R9, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R10_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R10 k x ≠ r_R10 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R10, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R11_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R11 k x ≠ r_R11 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R11, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R12_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R12 k x ≠ r_R12 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R12, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R13_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R13 k x ≠ r_R13 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R13, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_Ej_inj (k : ℕ) (p : ℕ) (hk : 1 ≤ k) (hp : 0 ≤ p ∧ p ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_Ej k p x ≠ r_Ej k p y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_Ej, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_Epj_inj (k : ℕ) (p : ℕ) (hk : 1 ≤ k) (hp : 0 ≤ p ∧ p ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_Epj k p x ≠ r_Epj k p y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_Epj, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_Os_inj (k : ℕ) (p : ℕ) (hk : 1 ≤ k) (hp : 1 ≤ p ∧ p ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_Os k p x ≠ r_Os k p y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_Os, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_Ops_inj (k : ℕ) (p : ℕ) (hk : 1 ≤ k) (hp : 1 ≤ p ∧ p ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_Ops k p x ≠ r_Ops k p y := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_Ops, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

/-- The weighted orders of the table, as a list. -/
def certList (k : ℕ) : List (ℕ × (V → ℕ)) :=
  [((k + 7), r_h1 k),
   ((k + 1), r_h2 k),
   (1, r_R1 k),
   (1, r_R2 k),
   (1, r_R3 k),
   (1, r_R4 k),
   (1, r_R5 k),
   (1, r_R6 k),
   (1, r_R7 k),
   (1, r_R8 k),
   (1, r_R9 k),
   (1, r_R10 k),
   (1, r_R11 k),
   (1, r_R12 k),
   (1, r_R13 k)]
  ++ ((List.range (k + 1)).map fun t => (1, r_Ej k (t + 0)))
  ++ ((List.range (k + 1)).map fun t => (1, r_Epj k (t + 0)))
  ++ ((List.range (k)).map fun t => (1, r_Os k (t + 1)))
  ++ ((List.range (k)).map fun t => (1, r_Ops k (t + 1)))

/-- The vertices, as a list. -/
def vs (k : ℕ) : List V :=
  [.N0, .N1, .N2, .N3, .P1, .P2, .F, .G, .H] ++ (List.range k).map (fun t => .U (t + 1)) ++ (List.range k).map (fun t => .W (t + 1))

theorem mem_vs (k : ℕ) (x : V) : x ∈ vs k ↔ valid k x := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | i | i
  · simp [vs, valid]
  · simp [vs, valid]
  · simp [vs, valid]
  · simp [vs, valid]
  · simp [vs, valid]
  · simp [vs, valid]
  · simp [vs, valid]
  · simp [vs, valid]
  · simp [vs, valid]
  · simp only [vs, valid, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, reduceCtorEq,
      V.U.injEq, List.not_mem_nil, or_false, false_or, and_false, exists_false]
    constructor
    · rintro ⟨t, ht, h⟩
      omega
    · intro h
      exact ⟨i - 1, by omega, by omega⟩
  · simp only [vs, valid, List.mem_append, List.mem_map, List.mem_range, List.mem_cons, reduceCtorEq,
      V.W.injEq, List.not_mem_nil, or_false, false_or, and_false, exists_false]
    constructor
    · rintro ⟨t, ht, h⟩
      omega
    · intro h
      exact ⟨i - 1, by omega, by omega⟩

theorem revWeight_certList (k : ℕ) (x y : V) : revWeight (certList k) x y = load k x y := by
  simp only [revWeight, certList, load, famsum, List.map_append, List.sum_append, List.map_cons,
    List.sum_cons, List.map_nil, List.sum_nil, List.map_map, Function.comp_def, one_mul]
  ring

theorem certList_total (k : ℕ) (hk : 1 ≤ k) : ((certList k).map Prod.fst).sum = 6 * k + 23 := by
  simp only [certList, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil,
    List.sum_nil, List.map_map, Function.comp_def, sum_map_range_one]
  omega

theorem certList_inj (k : ℕ) (hk : 1 ≤ k) (x y : V) (hx : valid k x) (hy : valid k y) (hxy : x ≠ y) :
    ∀ p ∈ certList k, p.2 x ≠ p.2 y := by
  intro p hp
  unfold certList at hp
  rcases List.mem_append.1 hp with hp3 | hF3
  swap
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hF3
    have ht' := List.mem_range.1 ht
    exact r_Ops_inj k (t + 1) hk ⟨by omega, by omega⟩ x y hx hy hxy
  rcases List.mem_append.1 hp3 with hp2 | hF2
  swap
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hF2
    have ht' := List.mem_range.1 ht
    exact r_Os_inj k (t + 1) hk ⟨by omega, by omega⟩ x y hx hy hxy
  rcases List.mem_append.1 hp2 with hp1 | hF1
  swap
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hF1
    have ht' := List.mem_range.1 ht
    exact r_Epj_inj k (t + 0) hk ⟨by omega, by omega⟩ x y hx hy hxy
  rcases List.mem_append.1 hp1 with hp0 | hF0
  swap
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hF0
    have ht' := List.mem_range.1 ht
    exact r_Ej_inj k (t + 0) hk ⟨by omega, by omega⟩ x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_h1_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_h2_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R1_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R2_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R3_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R4_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R5_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R6_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R7_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R8_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R9_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R10_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R11_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R12_inj k hk x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R13_inj k hk x y hx hy hxy
  exact absurd hp0 List.not_mem_nil

/-- Bob's side: the weighted orders of the table make every arc of the completion forward with
weight at least `2n - 3`, out of a total of `3n - 4`. -/
theorem bob (k : ℕ) (hk : 1 ≤ k) : BobFwd (certList k) (tarc k) (vs k) (4 * k + 15) := by
  intro x _ y _ h
  have h1 := fwd_add_rev (certList k) x y (certList_inj k hk x y h.1 h.2.1 h.2.2.1)
  rw [revWeight_certList, certList_total k hk] at h1
  have h2 := load_le k hk x y h
  omega

end Tsigma.Odd
