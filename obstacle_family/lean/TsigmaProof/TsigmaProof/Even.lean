import TsigmaProof.Common

/-! # The even family: loads of the completion of `G_{2k+6}`, k ≥ 2

Generated mechanically from Table `tbl:even-orders` of paper 1. -/

namespace Tsigma.Even

inductive V where
  | T0 | T1 | T2 | T3 | P1 | P2 | U (i : ℕ) | W (i : ℕ)
  deriving DecidableEq

/-- The vertices: the fixed ones and `U i`, `W i` for `1 ≤ i ≤ k`. -/
def valid (k : ℕ) : V → Prop
  | .U i => 1 ≤ i ∧ i ≤ k
  | .W i => 1 ≤ i ∧ i ≤ k
  | _ => True

/-- The arcs of `G_{2k+6}` (Section sec:family-def): the zigzag path `T0, U1, W1, ..., Uk, Wk, T3`,
the arcs at the hubs `T1` and `T2`, and nine more. -/
def garc (k : ℕ) : V → V → Prop
  | .T0, .T3 => True
  | .T2, .P1 => True
  | .T3, .P1 => True
  | .P1, .T0 => True
  | .P1, .T1 => True
  | .T1, .P2 => True
  | .T3, .P2 => True
  | .P2, .T0 => True
  | .P2, .T2 => True
  | .T0, .T1 => True
  | .T0, .T2 => True
  | .T1, .T3 => True
  | .T2, .T3 => True
  | .T1, .U i => 1 ≤ i ∧ i ≤ k
  | .T2, .U i => 1 ≤ i ∧ i ≤ k
  | .W i, .T1 => 1 ≤ i ∧ i ≤ k
  | .W i, .T2 => 1 ≤ i ∧ i ≤ k
  | .U i, .W j => 1 ≤ j ∧ ((i = j ∧ j ≤ k) ∨ (i = j + 1 ∧ j + 1 ≤ k))
  | .U i, .T0 => i = 1
  | .T3, .W j => j = k
  | _, _ => False

/-- The order along which `G_{2k+6}` is completed:
`T2, W1, ..., Wk, T1, T0, P1, U2, ..., Uk, U1, T3, P2`. -/
def sigma (k : ℕ) : V → ℕ
  | .T2 => 0
  | .W i => i
  | .T1 => k + 1
  | .T0 => k + 2
  | .P1 => k + 3
  | .U i => if i = 1 then 2 * k + 3 else k + 2 + i
  | .T3 => 2 * k + 4
  | .P2 => 2 * k + 5

/-- The arcs of the completion: those of the obstacle, and every other pair as in `sigma`. -/
def tarc (k : ℕ) (x y : V) : Prop :=
  valid k x ∧ valid k y ∧ x ≠ y ∧ (garc k x y ∨ (¬ garc k y x ∧ sigma k x < sigma k y))

/-- the order `h` of Table tbl:even-orders -/
def r_h (k : ℕ) : V → ℕ
  | .T0 => 3 * (4 * k + 8) + (0)
  | .T1 => 5 * (4 * k + 8) + (0)
  | .T2 => 4 * (4 * k + 8) + (0)
  | .T3 => 8 * (4 * k + 8) + (0)
  | .P1 => 1 * (4 * k + 8) + (0)
  | .P2 => 2 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 7 * (4 * k + 8) + (0) else 6 * (4 * k + 8) + (i)
  | .W i => 0 * (4 * k + 8) + (i)

/-- the order `R_1` of Table tbl:even-orders -/
def r_R1 (k : ℕ) : V → ℕ
  | .T0 => 4 * (4 * k + 8) + (0)
  | .T1 => 6 * (4 * k + 8) + (0)
  | .T2 => 5 * (4 * k + 8) + (0)
  | .T3 => 9 * (4 * k + 8) + (0)
  | .P1 => 3 * (4 * k + 8) + (0)
  | .P2 => 1 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 8 * (4 * k + 8) + (0) else 7 * (4 * k + 8) + (i)
  | .W i => if i = 1 then 0 * (4 * k + 8) + (0) else 2 * (4 * k + 8) + (i)

/-- the order `R_2` of Table tbl:even-orders -/
def r_R2 (k : ℕ) : V → ℕ
  | .T0 => 1 * (4 * k + 8) + (0)
  | .T1 => 4 * (4 * k + 8) + (0)
  | .T2 => 2 * (4 * k + 8) + (0)
  | .T3 => 7 * (4 * k + 8) + (0)
  | .P1 => 3 * (4 * k + 8) + (0)
  | .P2 => 9 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 6 * (4 * k + 8) + (0) else 5 * (4 * k + 8) + (i)
  | .W i => if i = 1 then 8 * (4 * k + 8) + (0) else 0 * (4 * k + 8) + (i)

/-- the order `R_3` of Table tbl:even-orders -/
def r_R3 (k : ℕ) : V → ℕ
  | .T0 => 3 * (4 * k + 8) + (0)
  | .T1 => 5 * (4 * k + 8) + (0)
  | .T2 => 4 * (4 * k + 8) + (0)
  | .T3 => 9 * (4 * k + 8) + (0)
  | .P1 => 1 * (4 * k + 8) + (0)
  | .P2 => 2 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 7 * (4 * k + 8) + (0) else 6 * (4 * k + 8) + (i)
  | .W i => if i = 1 then 8 * (4 * k + 8) + (0) else 0 * (4 * k + 8) + (i)

/-- the order `R_4` of Table tbl:even-orders -/
def r_R4 (k : ℕ) : V → ℕ
  | .T0 => 5 * (4 * k + 8) + (0)
  | .T1 => 7 * (4 * k + 8) + (0)
  | .T2 => 6 * (4 * k + 8) + (0)
  | .T3 => 1 * (4 * k + 8) + (0)
  | .P1 => 3 * (4 * k + 8) + (0)
  | .P2 => 4 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 0 * (4 * k + 8) + (0) else 8 * (4 * k + 8) + (i)
  | .W i => 2 * (4 * k + 8) + (i)

/-- the order `R_5` of Table tbl:even-orders -/
def r_R5 (k : ℕ) : V → ℕ
  | .T0 => 1 * (4 * k + 8) + (0)
  | .T1 => 2 * (4 * k + 8) + (0)
  | .T2 => 4 * (4 * k + 8) + (0)
  | .T3 => 5 * (4 * k + 8) + (0)
  | .P1 => 6 * (4 * k + 8) + (0)
  | .P2 => 3 * (4 * k + 8) + (0)
  | .U i => 0 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => 0 * (4 * k + 8) + (4 * (k - i) + 3)

/-- the order `R_6` of Table tbl:even-orders -/
def r_R6 (k : ℕ) : V → ℕ
  | .T0 => 8 * (4 * k + 8) + (0)
  | .T1 => 1 * (4 * k + 8) + (0)
  | .T2 => 0 * (4 * k + 8) + (0)
  | .T3 => 2 * (4 * k + 8) + (0)
  | .P1 => 3 * (4 * k + 8) + (0)
  | .P2 => 6 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 5 * (4 * k + 8) + (0) else 4 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => if i = 1 then 7 * (4 * k + 8) + (0) else 4 * (4 * k + 8) + (4 * (k - i) + 3)

/-- the order `R_7` of Table tbl:even-orders -/
def r_R7 (k : ℕ) : V → ℕ
  | .T0 => 5 * (4 * k + 8) + (0)
  | .T1 => 6 * (4 * k + 8) + (0)
  | .T2 => 3 * (4 * k + 8) + (0)
  | .T3 => 7 * (4 * k + 8) + (0)
  | .P1 => 4 * (4 * k + 8) + (0)
  | .P2 => 2 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 0 * (4 * k + 8) + (0) else 8 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => if i = 1 then 1 * (4 * k + 8) + (0) else 8 * (4 * k + 8) + (4 * (k - i) + 3)

/-- the order `R_8` of Table tbl:even-orders -/
def r_R8 (k : ℕ) : V → ℕ
  | .T0 => 1 * (4 * k + 8) + (0)
  | .T1 => 2 * (4 * k + 8) + (0)
  | .T2 => 3 * (4 * k + 8) + (0)
  | .T3 => 4 * (4 * k + 8) + (0)
  | .P1 => 5 * (4 * k + 8) + (0)
  | .P2 => 7 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 8 * (4 * k + 8) + (0) else 6 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => if i = 1 then 0 * (4 * k + 8) + (0) else 6 * (4 * k + 8) + (4 * (k - i) + 3)

/-- the order `R_9` of Table tbl:even-orders -/
def r_R9 (k : ℕ) : V → ℕ
  | .T0 => 1 * (4 * k + 8) + (0)
  | .T1 => 4 * (4 * k + 8) + (0)
  | .T2 => 7 * (4 * k + 8) + (0)
  | .T3 => 5 * (4 * k + 8) + (0)
  | .P1 => 8 * (4 * k + 8) + (0)
  | .P2 => 6 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 0 * (4 * k + 8) + (0) else 2 * (4 * k + 8) + (4 * i + 1)
  | .W i => if i = k then 3 * (4 * k + 8) + (0) else 2 * (4 * k + 8) + (4 * i + 7)

/-- the order `R_{10}` of Table tbl:even-orders -/
def r_R10 (k : ℕ) : V → ℕ
  | .T0 => 7 * (4 * k + 8) + (0)
  | .T1 => 0 * (4 * k + 8) + (0)
  | .T2 => 8 * (4 * k + 8) + (0)
  | .T3 => 3 * (4 * k + 8) + (0)
  | .P1 => 5 * (4 * k + 8) + (0)
  | .P2 => 6 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 1 * (4 * k + 8) + (0) else 2 * (4 * k + 8) + (4 * i + 1)
  | .W i => if i = k then 4 * (4 * k + 8) + (0) else 2 * (4 * k + 8) + (4 * i + 7)

/-- the order `R_{11}` of Table tbl:even-orders -/
def r_R11 (k : ℕ) : V → ℕ
  | .T0 => 3 * (4 * k + 8) + (0)
  | .T1 => 8 * (4 * k + 8) + (0)
  | .T2 => 1 * (4 * k + 8) + (0)
  | .T3 => 5 * (4 * k + 8) + (0)
  | .P1 => 7 * (4 * k + 8) + (0)
  | .P2 => 0 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 2 * (4 * k + 8) + (0) else 4 * (4 * k + 8) + (4 * i + 1)
  | .W i => if i = k then 6 * (4 * k + 8) + (0) else 4 * (4 * k + 8) + (4 * i + 7)

/-- the order `R_{12}` of Table tbl:even-orders -/
def r_R12 (k : ℕ) : V → ℕ
  | .T0 => 3 * (4 * k + 8) + (0)
  | .T1 => 1 * (4 * k + 8) + (0)
  | .T2 => 8 * (4 * k + 8) + (0)
  | .T3 => 5 * (4 * k + 8) + (0)
  | .P1 => 0 * (4 * k + 8) + (0)
  | .P2 => 6 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 2 * (4 * k + 8) + (0) else 4 * (4 * k + 8) + (4 * i + 1)
  | .W i => if i = k then 7 * (4 * k + 8) + (0) else 4 * (4 * k + 8) + (4 * i + 7)

/-- the order `R_{13}` of Table tbl:even-orders -/
def r_R13 (k : ℕ) : V → ℕ
  | .T0 => 8 * (4 * k + 8) + (0)
  | .T1 => 5 * (4 * k + 8) + (0)
  | .T2 => 3 * (4 * k + 8) + (0)
  | .T3 => 1 * (4 * k + 8) + (0)
  | .P1 => 4 * (4 * k + 8) + (0)
  | .P2 => 7 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 6 * (4 * k + 8) + (0) else 0 * (4 * k + 8) + (4 * i + 1)
  | .W i => if i = k then 2 * (4 * k + 8) + (0) else 0 * (4 * k + 8) + (4 * i + 7)

/-- the order `R_{14}` of Table tbl:even-orders -/
def r_R14 (k : ℕ) : V → ℕ
  | .T0 => 0 * (4 * k + 8) + (0)
  | .T1 => 4 * (4 * k + 8) + (0)
  | .T2 => 6 * (4 * k + 8) + (0)
  | .T3 => 2 * (4 * k + 8) + (0)
  | .P1 => 7 * (4 * k + 8) + (0)
  | .P2 => 5 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 8 * (4 * k + 8) + (0) else 1 * (4 * k + 8) + (4 * i + 1)
  | .W i => if i = k then 3 * (4 * k + 8) + (0) else 1 * (4 * k + 8) + (4 * i + 7)

/-- the order `A_j` of Table tbl:even-orders -/
def r_Aj (k : ℕ) (p : ℕ) : V → ℕ
  | .T0 => 5 * (4 * k + 8) + (0)
  | .T1 => 3 * (4 * k + 8) + (4 * (k - p))
  | .T2 => 0 * (4 * k + 8) + (0)
  | .T3 => 1 * (4 * k + 8) + (0)
  | .P1 => 2 * (4 * k + 8) + (0)
  | .P2 => 4 * (4 * k + 8) + (0)
  | .U i => 3 * (4 * k + 8) + (4 * (k - i) + 1)
  | .W i => 3 * (4 * k + 8) + (4 * (k - i) + 3)

/-- the order `\tilde A_s` of Table tbl:even-orders -/
def r_Ast (k : ℕ) (p : ℕ) : V → ℕ
  | .T0 => 5 * (4 * k + 8) + (0)
  | .T1 => 3 * (4 * k + 8) + (4 * (k - p) + 2)
  | .T2 => 0 * (4 * k + 8) + (0)
  | .T3 => 1 * (4 * k + 8) + (0)
  | .P1 => 2 * (4 * k + 8) + (0)
  | .P2 => 4 * (4 * k + 8) + (0)
  | .U i => 3 * (4 * k + 8) + (if i = p then 4 * (k - i) + 3 else 4 * (k - i) + 1)
  | .W i => 3 * (4 * k + 8) + (if i = p then 4 * (k - i) + 1 else 4 * (k - i) + 3)

/-- the order `B_s` of Table tbl:even-orders -/
def r_Bs (k : ℕ) (p : ℕ) : V → ℕ
  | .T0 => 1 * (4 * k + 8) + (0)
  | .T1 => 2 * (4 * k + 8) + (4 * p + 4)
  | .T2 => 6 * (4 * k + 8) + (0)
  | .T3 => 3 * (4 * k + 8) + (0)
  | .P1 => 7 * (4 * k + 8) + (0)
  | .P2 => 4 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 0 * (4 * k + 8) + (0) else 2 * (4 * k + 8) + (4 * i + 1)
  | .W i => if i = k then 5 * (4 * k + 8) + (0) else 2 * (4 * k + 8) + (4 * i + 7)

/-- the order `\tilde B_j` of Table tbl:even-orders -/
def r_Bjt (k : ℕ) (p : ℕ) : V → ℕ
  | .T0 => 1 * (4 * k + 8) + (0)
  | .T1 => 2 * (4 * k + 8) + (4 * p + 6)
  | .T2 => 6 * (4 * k + 8) + (0)
  | .T3 => 3 * (4 * k + 8) + (0)
  | .P1 => 7 * (4 * k + 8) + (0)
  | .P2 => 4 * (4 * k + 8) + (0)
  | .U i => if i = 1 then 0 * (4 * k + 8) + (0) else 2 * (4 * k + 8) + (if i = p + 1 then 4 * p + 7 else 4 * i + 1)
  | .W i => if i = k then 5 * (4 * k + 8) + (0) else 2 * (4 * k + 8) + (if i = p then 4 * p + 5 else 4 * i + 7)

/-- The load of `x → y`: the total weight of the orders that reverse it. -/
def load (k : ℕ) (x y : V) : ℕ :=
  2 * k * ind (r_h k) x y
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
  + 1 * ind (r_R14 k) x y
  + famsum (fun t => r_Aj k (t + 0)) (k + 1) x y
  + famsum (fun t => r_Ast k (t + 1)) (k) x y
  + famsum (fun t => r_Bs k (t + 1)) (k) x y
  + famsum (fun t => r_Bjt k (t + 1)) (k - 1) x y

theorem load_W_T0 (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.T0) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) ∨ (i = k) by omega) with hs | hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.T0) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.T0) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.T0) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.T0) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.T0) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.T0) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.T0) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.T0) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.T0) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.T0) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.T0) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.T0) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.T0) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.T0) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_W_T1 (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.T1) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) ∨ (i = k) by omega) with hs | hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.T1) = (1 + k) - (1) :=
      famsum_interval (1) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.T1) = (k) - (1) :=
      famsum_interval (1) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.T1) = (1) - (0) :=
      famsum_interval (0) (1) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.T1) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.T1) = (1 + k) - (i) :=
      famsum_interval (i) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.T1) = (k) - (i) :=
      famsum_interval (i) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.T1) = (i) - (0) :=
      famsum_interval (0) (i) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.T1) = ((i) - (1)) - (0) :=
      famsum_interval (0) ((i) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.T1) = (1 + k) - (k) :=
      famsum_interval (k) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.T1) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.T1) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.T1) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.T1) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.T1) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_W_T2 (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.T2) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) ∨ (i = k) by omega) with hs | hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.T2) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.T2) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.T2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.T2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.T2) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.T2) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.T2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.T2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.T2) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.T2) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.T2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.T2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.T2) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.T2) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_W_P1 (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.P1) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) ∨ (i = k) by omega) with hs | hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.P1) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.P1) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.P1) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.P1) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.P1) = 1 :=
      ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.P1) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
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
    have e_R12 : ind (r_R12 k) (.W i) (.P1) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.P1) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.P1) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.P1) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.P1) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.P1) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.P1) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.P1) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.P1) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.P1) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.P1) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.P1) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.P1) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.P1) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.P1) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.P1) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.P1) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.P1) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_W_P2 (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.W i) (.P2) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) ∨ (i = k) by omega) with hs | hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.P2) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.P2) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_W_T3 (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i + 1 ≤ k) :
    load k (.W i) (.T3) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) by omega) with hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.T3) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.T3) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.T3) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.T3) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W i) (.T3) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W i) (.T3) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W i) (.T3) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W i) (.T3) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_T3_Wk (k : ℕ) (hk : 2 ≤ k) :
    load k (.T3) (.W k) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T3) (.W k) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T3) (.W k) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T3) (.W k) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T3) (.W k) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T3) (.W k) = 1 :=
    ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T3) (.W k) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T3) (.W k) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T3) (.W k) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T3) (.W k) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T3) (.W k) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T3) (.W k) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T3) (.W k) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T3) (.W k) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T3) (.W k) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T3) (.W k) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T3) (.W k) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T3) (.W k) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T3) (.W k) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T3) (.W k) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_T1_U (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.T1) (.U i) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) ∨ (i = k) by omega) with hs | hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T1) (.U i) = (1) - (0) :=
      famsum_interval (0) (1) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T1) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T1) (.U i) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T1) (.U i) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T1) (.U i) = (i) - (0) :=
      famsum_interval (0) (i) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T1) (.U i) = ((i) - (1)) - (0) :=
      famsum_interval (0) ((i) - (1)) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T1) (.U i) = (k) - ((i) - (1)) :=
      famsum_interval ((i) - (1)) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T1) (.U i) = ((k) - (1)) - ((i) - (1)) :=
      famsum_interval ((i) - (1)) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T1) (.U i) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T1) (.U i) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T1) (.U i) = (k) - ((k) - (1)) :=
      famsum_interval ((k) - (1)) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T1) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.T1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.T1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_T2_U (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.T2) (.U i) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) ∨ (i = k) by omega) with hs | hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T2) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T2) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T2) (.U i) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T2) (.U i) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T2) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T2) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T2) (.U i) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T2) (.U i) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T2) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T2) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T2) (.U i) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T2) (.U i) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.T2) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.T2) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_P1_U (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.P1) (.U i) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) ∨ (i = k) by omega) with hs | hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.P1) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.P1) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.P1) (.U i) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.P1) (.U i) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.P1) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.P1) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.P1) (.U i) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.P1) (.U i) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.P1) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.P1) (.U i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.P1) (.U i) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.P1) (.U i) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.P1) (.U i) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.P1) (.U i) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_T0_U (k i : ℕ) (hk : 2 ≤ k) (hc : 2 ≤ i ∧ i ≤ k) :
    load k (.T0) (.U i) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T0) (.U i) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T0) (.U i) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T0) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T0) (.U i) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T0) (.U i) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T0) (.U i) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_U1_T0 (k : ℕ) (hk : 2 ≤ k) :
    load k (.U 1) (.T0) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U 1) (.T0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U 1) (.T0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U 1) (.T0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U 1) (.T0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.U 1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.U 1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.U 1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.U 1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.U 1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.U 1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.U 1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.U 1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.U 1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.U 1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.U 1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.U 1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.U 1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.U 1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.U 1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_U_T3 (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.U i) (.T3) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) ∨ (i = k) by omega) with hs | hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U i) (.T3) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U i) (.T3) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U i) (.T3) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U i) (.T3) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U i) (.T3) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U i) (.T3) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U i) (.T3) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U i) (.T3) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U i) (.T3) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U i) (.T3) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U i) (.T3) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U i) (.T3) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.U i) (.T3) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.U i) (.T3) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_U_P2 (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.U i) (.P2) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) ∨ (i = k) by omega) with hs | hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U i) (.P2) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.U i) (.P2) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.U i) (.P2) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_Wa_Wb (k a b : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ a ∧ a < b ∧ b ≤ k) :
    load k (.W a) (.W b) ≤ 2 * k + 5 := by
  rcases (show (a = 1) ∨ (2 ≤ a ∧ a + 1 ≤ k) by omega) with hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W a) (.W b) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W a) (.W b) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W a) (.W b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W a) (.W b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W a) (.W b) = 1 :=
      ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W a) (.W b) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W a) (.W b) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W a) (.W b) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W a) (.W b) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W a) (.W b) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W a) (.W b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W a) (.W b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W a) (.W b) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W a) (.W b) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W a) (.W b) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W a) (.W b) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W a) (.W b) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_Ua_Ub (k a b : ℕ) (hk : 2 ≤ k) (hc : 2 ≤ a ∧ a < b ∧ b ≤ k) :
    load k (.U a) (.U b) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U a) (.U b) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U a) (.U b) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U a) (.U b) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U a) (.U b) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.U a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.U a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.U a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.U a) (.U b) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.U a) (.U b) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_Ua_U1 (k a : ℕ) (hk : 2 ≤ k) (hc : 2 ≤ a ∧ a ≤ k) :
    load k (.U a) (.U 1) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U a) (.U 1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U a) (.U 1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U a) (.U 1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U a) (.U 1) = ((k) - (1)) - (0) :=
    famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.U a) (.U 1) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.U a) (.U 1) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.U a) (.U 1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.U a) (.U 1) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.U a) (.U 1) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.U a) (.U 1) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.U a) (.U 1) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.U a) (.U 1) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.U a) (.U 1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.U a) (.U 1) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.U a) (.U 1) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.U a) (.U 1) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.U a) (.U 1) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.U a) (.U 1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.U a) (.U 1) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_Ui_Wi (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i ≤ k) :
    load k (.U i) (.W i) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) ∨ (i = k) by omega) with hs | hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U i) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U i) (.W i) = (1) - (0) :=
      famsum_interval (0) (1) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U i) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U i) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
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
    have e_R8 : ind (r_R8 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.U i) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.U i) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.U i) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.U i) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U i) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U i) (.W i) = (i) - ((i) - (1)) :=
      famsum_interval ((i) - (1)) (i) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U i) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U i) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
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
    have e_R14 : ind (r_R14 k) (.U i) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U i) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U i) (.W i) = (k) - ((k) - (1)) :=
      famsum_interval ((k) - (1)) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U i) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U i) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.U i) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
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
    have e_R14 : ind (r_R14 k) (.U i) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_Ui1_Wi (k i : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ i ∧ i + 1 ≤ k) :
    load k (.U (i + 1)) (.W i) ≤ 2 * k + 5 := by
  rcases (show (i = 1) ∨ (2 ≤ i ∧ i + 1 ≤ k) by omega) with hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U (i + 1)) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U (i + 1)) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U (i + 1)) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U (i + 1)) (.W i) = (1) - (0) :=
      famsum_interval (0) (1) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.U (i + 1)) (.W i) = 1 :=
      ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.U (i + 1)) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.U (i + 1)) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.U (i + 1)) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.U (i + 1)) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.U (i + 1)) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.U (i + 1)) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.U (i + 1)) (.W i) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.U (i + 1)) (.W i) = (i) - ((i) - (1)) :=
      famsum_interval ((i) - (1)) (i) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.U (i + 1)) (.W i) = 1 :=
      ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.U (i + 1)) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.U (i + 1)) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.U (i + 1)) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.U (i + 1)) (.W i) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.U (i + 1)) (.W i) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_Wa_Ub_fwd (k a b : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ a ∧ a + 2 ≤ b ∧ b ≤ k) :
    load k (.W a) (.U b) ≤ 2 * k + 5 := by
  rcases (show (a = 1) ∨ (2 ≤ a ∧ a + 1 ≤ k) by omega) with hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W a) (.U b) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W a) (.U b) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W a) (.U b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W a) (.U b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
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
    have e_R14 : ind (r_R14 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W a) (.U b) = (1 + k) - (0) :=
      famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W a) (.U b) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W a) (.U b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W a) (.U b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
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
    have e_R14 : ind (r_R14 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_Wa_Ub_bwd (k a b : ℕ) (hk : 2 ≤ k) (hc : 1 ≤ b ∧ b + 1 ≤ a ∧ a ≤ k) :
    load k (.W a) (.U b) ≤ 2 * k + 5 := by
  rcases (show (b = 1) ∨ (2 ≤ b ∧ b + 1 ≤ k) by omega) with hs | hs
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W a) (.U b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W a) (.U b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W a) (.U b) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W a) (.U b) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
    have e_R2 : ind (r_R2 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
    have e_R3 : ind (r_R3 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
    have e_R4 : ind (r_R4 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
    have e_R5 : ind (r_R5 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
    have e_R6 : ind (r_R6 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
    have e_R7 : ind (r_R7 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
    have e_R9 : ind (r_R9 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
    have e_R10 : ind (r_R10 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
    have e_R11 : ind (r_R11 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
    have e_R12 : ind (r_R12 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
    have e_R13 : ind (r_R13 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
    have e_R14 : ind (r_R14 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega
  · have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.W a) (.U b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.W a) (.U b) = (0) - (0) :=
      famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.W a) (.U b) = (k) - (0) :=
      famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.W a) (.U b) = ((k) - (1)) - (0) :=
      famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
        (fun _ => by omega)
    have e_h : ind (r_h k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
    have e_R1 : ind (r_R1 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
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
    have e_R7 : ind (r_R7 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
    have e_R8 : ind (r_R8 k) (.W a) (.U b) = 0 :=
      ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
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
    have e_R14 : ind (r_R14 k) (.W a) (.U b) = 1 :=
      ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
    simp only [load]
    rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
    omega

theorem load_T0_T1 (k : ℕ) (hk : 2 ≤ k) :
    load k (.T0) (.T1) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T0) (.T1) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T0) (.T1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T0) (.T1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T0) (.T1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T0) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T0) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T0) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T0) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T0) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T0) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T0) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T0) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T0) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T0) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T0) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T0) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T0) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T0) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T0) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_T0_T2 (k : ℕ) (hk : 2 ≤ k) :
    load k (.T0) (.T2) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T0) (.T2) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T0) (.T2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T0) (.T2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T0) (.T2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T0) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T0) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T0) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T0) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T0) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T0) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T0) (.T2) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T0) (.T2) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T0) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T0) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T0) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T0) (.T2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T0) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T0) (.T2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T0) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_T0_T3 (k : ℕ) (hk : 2 ≤ k) :
    load k (.T0) (.T3) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T0) (.T3) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T0) (.T3) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T0) (.T3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T0) (.T3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T0) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T0) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T0) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T0) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T0) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T0) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T0) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T0) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T0) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T0) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T0) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T0) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T0) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T0) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T0) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_T1_T3 (k : ℕ) (hk : 2 ≤ k) :
    load k (.T1) (.T3) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T1) (.T3) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T1) (.T3) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T1) (.T3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T1) (.T3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T1) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T1) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T1) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T1) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T1) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T1) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T1) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T1) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T1) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T1) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T1) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T1) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T1) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T1) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T1) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_T1_P2 (k : ℕ) (hk : 2 ≤ k) :
    load k (.T1) (.P2) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T1) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T1) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T1) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T1) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_T2_T1 (k : ℕ) (hk : 2 ≤ k) :
    load k (.T2) (.T1) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T2) (.T1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T2) (.T1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T2) (.T1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T2) (.T1) = ((k) - (1)) - (0) :=
    famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T2) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T2) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T2) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T2) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T2) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T2) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T2) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T2) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T2) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T2) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T2) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T2) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T2) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T2) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T2) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_T2_T3 (k : ℕ) (hk : 2 ≤ k) :
    load k (.T2) (.T3) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T2) (.T3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T2) (.T3) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T2) (.T3) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T2) (.T3) = ((k) - (1)) - (0) :=
    famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T2) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T2) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T2) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T2) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T2) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T2) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T2) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T2) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T2) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T2) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T2) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T2) (.T3) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T2) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T2) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T2) (.T3) = 1 :=
    ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_T2_P1 (k : ℕ) (hk : 2 ≤ k) :
    load k (.T2) (.P1) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T2) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T2) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T2) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T2) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T2) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T2) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_T3_P1 (k : ℕ) (hk : 2 ≤ k) :
    load k (.T3) (.P1) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T3) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T3) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T3) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T3) (.P1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T3) (.P1) = 1 :=
    ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T3) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T3) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T3) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T3) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T3) (.P1) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T3) (.P1) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_T3_P2 (k : ℕ) (hk : 2 ≤ k) :
    load k (.T3) (.P2) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.T3) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.T3) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.T3) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.T3) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.T3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.T3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.T3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.T3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.T3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.T3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.T3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.T3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.T3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.T3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.T3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.T3) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.T3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.T3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.T3) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_P1_T0 (k : ℕ) (hk : 2 ≤ k) :
    load k (.P1) (.T0) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.P1) (.T0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.P1) (.T0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.P1) (.T0) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.P1) (.T0) = ((k) - (1)) - (0) :=
    famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.P1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P1) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.P1) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_P1_T1 (k : ℕ) (hk : 2 ≤ k) :
    load k (.P1) (.T1) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.P1) (.T1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.P1) (.T1) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.P1) (.T1) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.P1) (.T1) = ((k) - (1)) - (0) :=
    famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.P1) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P1) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P1) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P1) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P1) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P1) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P1) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P1) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P1) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P1) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P1) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P1) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P1) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P1) (.T1) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.P1) (.T1) = 1 :=
    ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_P1_P2 (k : ℕ) (hk : 2 ≤ k) :
    load k (.P1) (.P2) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.P1) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.P1) (.P2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.P1) (.P2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.P1) (.P2) = ((k) - (1)) - (0) :=
    famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P1) (.P2) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.P1) (.P2) = 1 :=
    ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_P2_T0 (k : ℕ) (hk : 2 ≤ k) :
    load k (.P2) (.T0) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.P2) (.T0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.P2) (.T0) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.P2) (.T0) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.P2) (.T0) = ((k) - (1)) - (0) :=
    famsum_interval (0) ((k) - (1)) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.P2) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P2) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P2) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P2) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P2) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P2) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P2) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P2) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P2) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P2) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P2) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P2) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P2) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P2) (.T0) = 0 :=
    ind_of_not_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.P2) (.T0) = 1 :=
    ind_of_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_P2_T2 (k : ℕ) (hk : 2 ≤ k) :
    load k (.P2) (.T2) ≤ 2 * k + 5 := by
  have h0 : famsum (fun t => r_Aj k (t + 0)) (k + 1) (.P2) (.T2) = (1 + k) - (0) :=
    famsum_interval (0) (1 + k) (fun t ht => by simp only [r_Aj]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h1 : famsum (fun t => r_Ast k (t + 1)) (k) (.P2) (.T2) = (k) - (0) :=
    famsum_interval (0) (k) (fun t ht => by simp only [r_Ast]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h2 : famsum (fun t => r_Bs k (t + 1)) (k) (.P2) (.T2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bs]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have h3 : famsum (fun t => r_Bjt k (t + 1)) (k - 1) (.P2) (.T2) = (0) - (0) :=
    famsum_interval (0) (0) (fun t ht => by simp only [r_Bjt]; (try split_ifs) <;> omega)
      (fun _ => by omega)
  have e_h : ind (r_h k) (.P2) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_h]; (try split_ifs) <;> omega)
  have e_R1 : ind (r_R1 k) (.P2) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R1]; (try split_ifs) <;> omega)
  have e_R2 : ind (r_R2 k) (.P2) (.T2) = 1 :=
    ind_of_lt (by simp only [r_R2]; (try split_ifs) <;> omega)
  have e_R3 : ind (r_R3 k) (.P2) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R3]; (try split_ifs) <;> omega)
  have e_R4 : ind (r_R4 k) (.P2) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R4]; (try split_ifs) <;> omega)
  have e_R5 : ind (r_R5 k) (.P2) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R5]; (try split_ifs) <;> omega)
  have e_R6 : ind (r_R6 k) (.P2) (.T2) = 1 :=
    ind_of_lt (by simp only [r_R6]; (try split_ifs) <;> omega)
  have e_R7 : ind (r_R7 k) (.P2) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R7]; (try split_ifs) <;> omega)
  have e_R8 : ind (r_R8 k) (.P2) (.T2) = 1 :=
    ind_of_lt (by simp only [r_R8]; (try split_ifs) <;> omega)
  have e_R9 : ind (r_R9 k) (.P2) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R9]; (try split_ifs) <;> omega)
  have e_R10 : ind (r_R10 k) (.P2) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R10]; (try split_ifs) <;> omega)
  have e_R11 : ind (r_R11 k) (.P2) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R11]; (try split_ifs) <;> omega)
  have e_R12 : ind (r_R12 k) (.P2) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R12]; (try split_ifs) <;> omega)
  have e_R13 : ind (r_R13 k) (.P2) (.T2) = 1 :=
    ind_of_lt (by simp only [r_R13]; (try split_ifs) <;> omega)
  have e_R14 : ind (r_R14 k) (.P2) (.T2) = 0 :=
    ind_of_not_lt (by simp only [r_R14]; (try split_ifs) <;> omega)
  simp only [load]
  rw [h0, h1, h2, h3, e_h, e_R1, e_R2, e_R3, e_R4, e_R5, e_R6, e_R7, e_R8, e_R9, e_R10, e_R11, e_R12, e_R13, e_R14]
  omega

theorem load_le (k : ℕ) (hk : 2 ≤ k) (x y : V) (h : tarc k x y) :
    load k x y ≤ 2 * k + 5 := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_T0_T1 k hk
  · exact load_T0_T2 k hk
  · exact load_T0_T3 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (2 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_T0_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_T1_T3 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_T1_P2 k hk
  · have hc : (1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_T1_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_T2_T1 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_T2_T3 k hk
  · exact load_T2_P1 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_T2_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_T3_P1 k hk
  · exact load_T3_P2 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (b = k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with rfl
    · exact load_T3_Wk _ hk
  · exact load_P1_T0 k hk
  · exact load_P1_T1 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_P1_P2 k hk
  · have hc : (1 ≤ b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_P1_U k b hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_P2_T0 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · exact load_P2_T2 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (a = 1) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with rfl
    · exact load_U1_T0 k hk
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_U_T3 k a hk hc
  · simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_U_P2 k a hk hc
  · have hc : (2 ≤ a ∧ a < b ∧ b ≤ k) ∨ (b = 1 ∧ 2 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc | ⟨rfl, hc⟩
    · exact load_Ua_Ub k a b hk hc
    · exact load_Ua_U1 k a hk hc
  · have hc : (a = b ∧ 1 ≤ b ∧ b ≤ k) ∨ (a = b + 1 ∧ 1 ≤ b ∧ b + 1 ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
    · exact load_Ui_Wi k _ hk hc
    · exact load_Ui1_Wi k b hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_T0 k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_T1 k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_T2 k a hk hc
  · have hc : (1 ≤ a ∧ a + 1 ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_T3 k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_P1 k a hk hc
  · have hc : (1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_W_P2 k a hk hc
  · have hc : (1 ≤ a ∧ a + 2 ≤ b ∧ b ≤ k) ∨ (1 ≤ b ∧ b + 1 ≤ a ∧ a ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc | hc
    · exact load_Wa_Ub_fwd k a b hk hc
    · exact load_Wa_Ub_bwd k a b hk hc
  · have hc : (1 ≤ a ∧ a < b ∧ b ≤ k) := by
      simp [tarc, valid, garc, sigma] at h <;> (try split_ifs at h) <;> omega
    rcases hc with hc
    · exact load_Wa_Wb k a b hk hc

theorem r_h_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_h k x ≠ r_h k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_h, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R1_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R1 k x ≠ r_R1 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R1, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R2_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R2 k x ≠ r_R2 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R2, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R3_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R3 k x ≠ r_R3 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R3, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R4_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R4 k x ≠ r_R4 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R4, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R5_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R5 k x ≠ r_R5 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R5, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R6_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R6 k x ≠ r_R6 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R6, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R7_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R7 k x ≠ r_R7 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R7, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R8_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R8 k x ≠ r_R8 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R8, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R9_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R9 k x ≠ r_R9 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R9, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R10_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R10 k x ≠ r_R10 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R10, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R11_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R11 k x ≠ r_R11 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R11, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R12_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R12 k x ≠ r_R12 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R12, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R13_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R13 k x ≠ r_R13 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R13, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_R14_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_R14 k x ≠ r_R14 k y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_R14, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_Aj_inj (k : ℕ) (p : ℕ) (hk : 2 ≤ k) (hp : 0 ≤ p ∧ p ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_Aj k p x ≠ r_Aj k p y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_Aj, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_Ast_inj (k : ℕ) (p : ℕ) (hk : 2 ≤ k) (hp : 1 ≤ p ∧ p ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_Ast k p x ≠ r_Ast k p y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_Ast, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_Bs_inj (k : ℕ) (p : ℕ) (hk : 2 ≤ k) (hp : 1 ≤ p ∧ p ≤ k) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_Bs k p x ≠ r_Bs k p y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_Bs, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem r_Bjt_inj (k : ℕ) (p : ℕ) (hk : 2 ≤ k) (hp : 1 ≤ p ∧ p ≤ k - 1) (x y : V) (hx : valid k x)
    (hy : valid k y) (hxy : x ≠ y) : r_Bjt k p x ≠ r_Bjt k p y := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp only [valid, r_Bjt, ne_eq, V.U.injEq, V.W.injEq, reduceCtorEq, not_false_eq_true,
      not_true_eq_false] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

/-- The weighted orders of the table, as a list. -/
def certList (k : ℕ) : List (ℕ × (V → ℕ)) :=
  [(2 * k, r_h k),
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
   (1, r_R13 k),
   (1, r_R14 k)]
  ++ ((List.range (k + 1)).map fun t => (1, r_Aj k (t + 0)))
  ++ ((List.range (k)).map fun t => (1, r_Ast k (t + 1)))
  ++ ((List.range (k)).map fun t => (1, r_Bs k (t + 1)))
  ++ ((List.range (k - 1)).map fun t => (1, r_Bjt k (t + 1)))

/-- The vertices, as a list. -/
def vs (k : ℕ) : List V :=
  [.T0, .T1, .T2, .T3, .P1, .P2] ++ (List.range k).map (fun t => .U (t + 1)) ++ (List.range k).map (fun t => .W (t + 1))

theorem mem_vs (k : ℕ) (x : V) : x ∈ vs k ↔ valid k x := by
  rcases x with _ | _ | _ | _ | _ | _ | i | i
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

theorem certList_total (k : ℕ) (hk : 2 ≤ k) : ((certList k).map Prod.fst).sum = 6 * k + 14 := by
  simp only [certList, List.map_append, List.sum_append, List.map_cons, List.sum_cons, List.map_nil,
    List.sum_nil, List.map_map, Function.comp_def, sum_map_range_one]
  omega

theorem certList_inj (k : ℕ) (hk : 2 ≤ k) (x y : V) (hx : valid k x) (hy : valid k y) (hxy : x ≠ y) :
    ∀ p ∈ certList k, p.2 x ≠ p.2 y := by
  intro p hp
  unfold certList at hp
  rcases List.mem_append.1 hp with hp3 | hF3
  swap
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hF3
    have ht' := List.mem_range.1 ht
    exact r_Bjt_inj k (t + 1) hk ⟨by omega, by omega⟩ x y hx hy hxy
  rcases List.mem_append.1 hp3 with hp2 | hF2
  swap
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hF2
    have ht' := List.mem_range.1 ht
    exact r_Bs_inj k (t + 1) hk ⟨by omega, by omega⟩ x y hx hy hxy
  rcases List.mem_append.1 hp2 with hp1 | hF1
  swap
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hF1
    have ht' := List.mem_range.1 ht
    exact r_Ast_inj k (t + 1) hk ⟨by omega, by omega⟩ x y hx hy hxy
  rcases List.mem_append.1 hp1 with hp0 | hF0
  swap
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hF0
    have ht' := List.mem_range.1 ht
    exact r_Aj_inj k (t + 0) hk ⟨by omega, by omega⟩ x y hx hy hxy
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_h_inj k hk x y hx hy hxy
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
  rcases List.mem_cons.1 hp0 with h | hp0
  · subst h; exact r_R14_inj k hk x y hx hy hxy
  exact absurd hp0 List.not_mem_nil

/-- Bob's side: the weighted orders of the table make every arc of the completion forward with
weight at least `2n - 3`, out of a total of `3n - 4`. -/
theorem bob (k : ℕ) (hk : 2 ≤ k) : BobFwd (certList k) (tarc k) (vs k) (4 * k + 9) := by
  intro x _ y _ h
  have h1 := fwd_add_rev (certList k) x y (certList_inj k hk x y h.1 h.2.1 h.2.2.1)
  rw [revWeight_certList, certList_total k hk] at h1
  have h2 := load_le k hk x y h
  omega

end Tsigma.Even
