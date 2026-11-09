import TsigmaProof.Bridge
import TsigmaProof.OddMoves0
import TsigmaProof.OddMoves1
import TsigmaProof.OddMoves2
import TsigmaProof.OddMoves3

/-!
# Proposition `prop:family-dual` for odd `n ≥ 11`

Appendix `sec:family-dual-odd`: the hub chains give every arc between a hub and the ladder one weight
per hub, the ends tie the hubs to the arcs `N1 → P1`, `N2 → P1`, the 57 relations of Table
`tbl:odd-relations` give the 22 arcs between fixed vertices one weight `t`, and every arc of the zigzag
path weighs at least `t`.  The heavy order `A_1`, which makes `2n - 3` arcs of `H_n` forward and none of
the path, gives `t = 1/(3n - 4)`; the total `1` then gives every arc of the path the weight `t`.
-/

namespace Tsigma.Odd

/-- The hub chains: every arc between the hub `N2` (or `N1`) and the ladder has the weight of
`N2 → U1` (or `N1 → U1`). -/
theorem hubs (k : ℕ) (hk : 1 ≤ k) (y : V → V → ℚ) (hy : AliceOpt (vs k) (garc k) (rho k) y) :
    ∀ i, 1 ≤ i → i ≤ k →
      y .N2 (.U i) = y .N2 (.U 1) ∧ y (.W i) .N2 = y .N2 (.U 1) ∧
      y .N1 (.U i) = y .N1 (.U 1) ∧ y (.W i) .N1 = y .N1 (.U 1) := by
  intro i hi1 hik
  induction i with
  | zero => omega
  | succ j ih =>
    have a2 := mv_chE12a k (j + 1) hk ⟨by omega, hik⟩ y hy
    have b2 := mv_chE12b k (j + 1) hk ⟨by omega, hik⟩ y hy
    have a1 := mv_chE21a k (j + 1) hk ⟨by omega, hik⟩ y hy
    have b1 := mv_chE21b k (j + 1) hk ⟨by omega, hik⟩ y hy
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨rfl, by linarith, rfl, by linarith⟩
    · obtain ⟨p1, p2, p3, p4⟩ := ih hj (by omega)
      have d2a := mv_chD12a k j hk ⟨hj, hik⟩ y hy
      have d2b := mv_chD12b k j hk ⟨hj, hik⟩ y hy
      have d1a := mv_chD21a k j hk ⟨hj, hik⟩ y hy
      have d1b := mv_chD21b k j hk ⟨hj, hik⟩ y hy
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The 22 arcs between fixed vertices, the hub arcs and the ends all weigh `y(N0 → N2)`; every arc
of the zigzag path weighs at least as much. -/
theorem off_path (k : ℕ) (hk : 1 ≤ k) (y : V → V → ℚ) (hy : AliceOpt (vs k) (garc k) (rho k) y) :
    (∀ q ∈ fixedArcs, y q.1.1 q.1.2 = y .N0 .N2) ∧
    (∀ i, 1 ≤ i → i ≤ k → y .N2 (.U i) = y .N0 .N2 ∧ y (.W i) .N2 = y .N0 .N2 ∧
      y .N1 (.U i) = y .N0 .N2 ∧ y (.W i) .N1 = y .N0 .N2 ∧ y .N0 .N2 ≤ y (.U i) (.W i)) ∧
    (∀ i, 1 ≤ i → i + 1 ≤ k → y .N0 .N2 ≤ y (.U i) (.W (i + 1))) ∧
    y .N0 .N2 ≤ y .P1 (.W 1) ∧ y .N0 .N2 ≤ y (.U k) .H := by
  have H := hubs k hk y hy
  have R1 := mv_R1 k hk y hy
  have R2 := mv_R2 k hk y hy
  have R3 := mv_R3 k hk y hy
  have R4 := mv_R4 k hk y hy
  have R5 := mv_R5 k hk y hy
  have R6 := mv_R6 k hk y hy
  have R7 := mv_R7 k hk y hy
  have R8 := mv_R8 k hk y hy
  have R9 := mv_R9 k hk y hy
  have R10 := mv_R10 k hk y hy
  have R11 := mv_R11 k hk y hy
  have R12 := mv_R12 k hk y hy
  have R13 := mv_R13 k hk y hy
  have R14 := mv_R14 k hk y hy
  have R15 := mv_R15 k hk y hy
  have R16 := mv_R16 k hk y hy
  have R17 := mv_R17 k hk y hy
  have R18 := mv_R18 k hk y hy
  have R19 := mv_R19 k hk y hy
  have R20 := mv_R20 k hk y hy
  have R21 := mv_R21 k hk y hy
  have R22 := mv_R22 k hk y hy
  have R23 := mv_R23 k hk y hy
  have R24 := mv_R24 k hk y hy
  have R25 := mv_R25 k hk y hy
  have R26 := mv_R26 k hk y hy
  have R27 := mv_R27 k hk y hy
  have R28 := mv_R28 k hk y hy
  have R29 := mv_R29 k hk y hy
  have R30 := mv_R30 k hk y hy
  have R31 := mv_R31 k hk y hy
  have R32 := mv_R32 k hk y hy
  have R33 := mv_R33 k hk y hy
  have R34 := mv_R34 k hk y hy
  have R35 := mv_R35 k hk y hy
  have R36 := mv_R36 k hk y hy
  have R37 := mv_R37 k hk y hy
  have R38 := mv_R38 k hk y hy
  have R39 := mv_R39 k hk y hy
  have R40 := mv_R40 k hk y hy
  have R41 := mv_R41 k hk y hy
  have R42 := mv_R42 k hk y hy
  have R43 := mv_R43 k hk y hy
  have R44 := mv_R44 k hk y hy
  have R45 := mv_R45 k hk y hy
  have R46 := mv_R46 k hk y hy
  have R47 := mv_R47 k hk y hy
  have R48 := mv_R48 k hk y hy
  have R49 := mv_R49 k hk y hy
  have R50 := mv_R50 k hk y hy
  have R51 := mv_R51 k hk y hy
  have R52 := mv_R52 k hk y hy
  have R53 := mv_R53 k hk y hy
  have R54 := mv_R54 k hk y hy
  have R55 := mv_R55 k hk y hy
  have R56 := mv_R56 k hk y hy
  have R57 := mv_R57 k hk y hy
  have e2a := mv_endN2a k hk y hy
  have e2b := mv_endN2b k hk y hy
  have e1a := mv_endN1a k hk y hy
  have e1b := mv_endN1b k hk y hy
  have ep := mv_endP1W1 k hk y hy
  have eu := mv_endUkH k hk y hy
  obtain ⟨_, w2, _, w1⟩ := H 1 le_rfl hk
  have t1 : y .N1 (.U 1) = y .N0 .N2 := by linarith
  have t2 : y .N2 (.U 1) = y .N0 .N2 := by linarith
  refine ⟨?_, ?_, ?_, by linarith, ?_⟩
  · intro q hq
    simp only [fixedArcs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h <;> subst h <;> simp only <;> linarith
  · intro i hi hik
    obtain ⟨h1, h2, h3, h4⟩ := H i hi hik
    have c2 := mv_chE12c k i hk ⟨hi, hik⟩ y hy
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  · intro i hi hik
    have h1 := (H i hi (by omega)).1
    have c2 := mv_chD12c k i hk ⟨hi, hik⟩ y hy
    linarith
  · have := (H k hk le_rfl).2.2.1
    linarith

/-- **Proposition `prop:family-dual`, odd `n ≥ 11`**: every arc of `H_n` weighs `1/(3n - 4)`. -/
theorem dual_unique (k : ℕ) (hk : 1 ≤ k) (y : V → V → ℚ) (hy : AliceOpt (vs k) (garc k) (rho k) y) :
    ∀ q ∈ oarcs k, y q.1.1 q.1.2 = 1 / ((6 * k + 23 : ℕ) : ℚ) := by
  obtain ⟨hfix, hhub, hoff, hp1, huk⟩ := off_path k hk y hy
  set c := y .N0 .N2 with hc
  have hge : ∀ q ∈ oarcs k, c ≤ y q.1.1 q.1.2 := by
    intro q hq
    simp only [oarcs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
      List.not_mem_nil, or_false] at hq
    rcases hq with ((((((hq | (h | h)) | ⟨s, hs, h⟩) | ⟨s, hs, h⟩) | ⟨s, hs, h⟩) | ⟨s, hs, h⟩) |
      ⟨s, hs, h⟩) | ⟨s, hs, h⟩
    · exact le_of_eq (hfix q hq).symm
    all_goals subst h
    all_goals simp only
    · exact hp1
    · exact huk
    · exact le_of_eq (hhub (s + 1) (by omega) (by omega)).2.2.1.symm
    · exact le_of_eq (hhub (s + 1) (by omega) (by omega)).1.symm
    · exact le_of_eq (hhub (s + 1) (by omega) (by omega)).2.2.2.1.symm
    · exact le_of_eq (hhub (s + 1) (by omega) (by omega)).2.1.symm
    · exact (hhub (s + 1) (by omega) (by omega)).2.2.2.2
    · exact hoff (s + 1) (by omega) (by omega)
  -- the heavy order `A_1`: `2n - 3` arcs of `H_n` forward, none of them on the zigzag path
  have hth := tight_A1 k hk y hy
  have hhu := aliceWeight_tight k hk (r_A1 k) (tight_A1 k hk (unif k) (unif_opt k hk))
  have hfw : fwdQ (vs k) (r_A1 k) y = c * (aliceWeight (oarcs k) (r_A1 k) : ℚ) := by
    rw [fwdQ_garc k hk _ y hy.supp, aliceWeight]
    refine list_fwd_const _ _ _ _ (oarcs_snd k) (fun q hq hr => ?_)
    simp only [oarcs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
      List.not_mem_nil, or_false] at hq
    rcases hq with ((((((hq | (h | h)) | ⟨s, hs, h⟩) | ⟨s, hs, h⟩) | ⟨s, hs, h⟩) | ⟨s, hs, h⟩) |
      ⟨s, hs, h⟩) | ⟨s, hs, h⟩
    · exact hfix q hq
    all_goals subst h
    all_goals simp only at hr ⊢
    · simp only [r_A1] at hr; omega
    · simp only [r_A1] at hr; omega
    · exact (hhub (s + 1) (by omega) (by omega)).2.2.1
    · exact (hhub (s + 1) (by omega) (by omega)).1
    · exact (hhub (s + 1) (by omega) (by omega)).2.2.2.1
    · exact (hhub (s + 1) (by omega) (by omega)).2.1
    · simp only [r_A1] at hr; omega
    · simp only [r_A1] at hr; omega
  rw [hfw, hhu, rho] at hth
  have hN : ((6 * k + 23 : ℕ) : ℚ) ≠ 0 := by positivity
  have hcv : c = 1 / ((6 * k + 23 : ℕ) : ℚ) := by
    have h4 : ((4 * k + 15 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [eq_div_iff hN]
    have := hth
    rw [eq_div_iff hN] at this
    have h5 : ((4 * k + 15 : ℕ) : ℚ) * (c * ((6 * k + 23 : ℕ) : ℚ) - 1) = 0 := by linarith
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact absurd h6 h4
    · linarith
  have htot := hy.total
  rw [psum_garc k hk y hy.supp] at htot
  have hsum : ((oarcs k).map (fun q => y q.1.1 q.1.2)).sum =
      c * ((((oarcs k).map Prod.snd).sum : ℕ) : ℚ) := by
    rw [htot, oarcs_total k hk, hcv]
    field_simp
  have := list_eq_of_ge (oarcs k) y c (oarcs_snd k) hge hsum
  intro q hq
  rw [this q hq, hcv]

end Tsigma.Odd
