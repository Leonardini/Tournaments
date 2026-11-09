import TsigmaProof.Bridge
import TsigmaProof.EvenMoves0
import TsigmaProof.EvenMoves1
import TsigmaProof.EvenMoves2
import TsigmaProof.EvenMoves3

/-!
# Proposition `prop:family-dual` for even `n ≥ 10`, and the uniqueness half of Theorem `thm:family-value`

Appendix `sec:family-dual-even`: the moves of Table `tbl:even-moves` and their images under `φ`
(the lemmas `mv_*`, proved from `move_le`) force every arc of `G_n` other than `U1 → T0` to one weight
`c`; the order `h` of Table `tbl:even-dual-orders`, which makes `2n - 3` arcs of `G_n` forward but not
`U1 → T0`, gives `c = 1/(3n - 4)`, and the total `1` gives the same weight to `U1 → T0`.
-/

namespace Tsigma.Even

/-- Steps (i): every arc at the hub `T1` and every arc `U_i → W_i` has the weight of `T1 → U1`. -/
theorem hub_T1 (k : ℕ) (hk : 2 ≤ k) (y : V → V → ℚ) (hy : AliceOpt (vs k) (garc k) (rho k) y) :
    ∀ i, 1 ≤ i → i ≤ k → y .T1 (.U i) = y .T1 (.U 1) ∧ y (.W i) .T1 = y .T1 (.U 1) ∧
      y (.U i) (.W i) = y .T1 (.U 1) := by
  intro i hi1 hik
  induction i with
  | zero => omega
  | succ j ih =>
    have h1 := mv_H1 k (j + 1) hk ⟨by omega, hik⟩ y hy
    have h2 := mv_H2 k (j + 1) hk ⟨by omega, hik⟩ y hy
    have h3 := mv_H3 k (j + 1) hk ⟨by omega, hik⟩ y hy
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨rfl, by linarith, by linarith⟩
    · obtain ⟨a1, a2, a3⟩ := ih hj (by omega)
      have h4 := mv_H4 k j hk ⟨hj, hik⟩ y hy
      have h5 := mv_H5 k j hk ⟨hj, hik⟩ y hy
      have h6 := mv_H6 k j hk ⟨hj, hik⟩ y hy
      refine ⟨by linarith, by linarith, by linarith⟩

theorem hub_T2 (k : ℕ) (hk : 2 ≤ k) (y : V → V → ℚ) (hy : AliceOpt (vs k) (garc k) (rho k) y) :
    ∀ i, 1 ≤ i → i ≤ k → y .T2 (.U i) = y .T2 (.U 1) ∧ y (.W i) .T2 = y .T2 (.U 1) ∧
      y (.U i) (.W i) = y .T2 (.U 1) := by
  intro i hi1 hik
  induction i with
  | zero => omega
  | succ j ih =>
    have h1 := mv_H1_phi k (j + 1) hk ⟨by omega, hik⟩ y hy
    have h2 := mv_H2_phi k (j + 1) hk ⟨by omega, hik⟩ y hy
    have h3 := mv_H3_phi k (j + 1) hk ⟨by omega, hik⟩ y hy
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · exact ⟨rfl, by linarith, by linarith⟩
    · obtain ⟨a1, a2, a3⟩ := ih hj (by omega)
      have h4 := mv_H4_phi k j hk ⟨hj, hik⟩ y hy
      have h5 := mv_H5_phi k j hk ⟨hj, hik⟩ y hy
      have h6 := mv_H6_phi k j hk ⟨hj, hik⟩ y hy
      refine ⟨by linarith, by linarith, by linarith⟩

/-- Steps (i) to (iv): every arc of `G_n` other than `U1 → T0` has weight `y(T1 → U1)`. -/
theorem all_but_one (k : ℕ) (hk : 2 ≤ k) (y : V → V → ℚ) (hy : AliceOpt (vs k) (garc k) (rho k) y) :
    ∀ q ∈ oarcs k, q.1 ≠ (.U 1, .T0) → y q.1.1 q.1.2 = y .T1 (.U 1) := by
  have H1 := hub_T1 k hk y hy
  have H2 := hub_T2 k hk y hy
  have c12 : y .T2 (.U 1) = y .T1 (.U 1) := by
    have := (H1 1 le_rfl (by omega)).2.2
    have := (H2 1 le_rfl (by omega)).2.2
    linarith
  have off : ∀ i, 1 ≤ i → i + 1 ≤ k → y (.U (i + 1)) (.W i) = y .T1 (.U 1) := by
    intro i hi hik
    have h4 := mv_H4 k i hk ⟨hi, hik⟩ y hy
    have h6 := mv_H6 k i hk ⟨hi, hik⟩ y hy
    have := (H1 i hi (by omega)).2.1
    have := (H1 (i + 1) (by omega) hik).1
    linarith
  have hk1 := (H1 k (by omega) le_rfl).2.1
  have hk2 := (H2 k (by omega) le_rfl).2.1
  have hu1 := (H2 1 le_rfl (by omega)).1
  have e1 := mv_E1 k hk y hy
  have e2 := mv_E2 k hk y hy
  have e3 := mv_E3 k hk y hy
  have e2' := mv_E2_phi k hk y hy
  have fa := mv_Fa k hk y hy
  have fb := mv_Fb k hk y hy
  have fc := mv_Fc k hk y hy
  have fd := mv_Fd k hk y hy
  have fe := mv_Fe k hk y hy
  have ff := mv_Ff k hk y hy
  have fg := mv_Fg k hk y hy
  have fh := mv_Fh k hk y hy
  have fi := mv_Fi k hk y hy
  have fj := mv_Fj k hk y hy
  have fk := mv_Fk k hk y hy
  have fa' := mv_Fa_phi k hk y hy
  have fb' := mv_Fb_phi k hk y hy
  have fc' := mv_Fc_phi k hk y hy
  have fd' := mv_Fd_phi k hk y hy
  have ff' := mv_Ff_phi k hk y hy
  have fg' := mv_Fg_phi k hk y hy
  have fh' := mv_Fh_phi k hk y hy
  have fi' := mv_Fi_phi k hk y hy
  have fj' := mv_Fj_phi k hk y hy
  have fk' := mv_Fk_phi k hk y hy
  intro q hq hne
  simp only [oarcs, List.mem_append, List.mem_cons, List.mem_map, List.mem_range,
    List.not_mem_nil, or_false] at hq
  rcases hq with ((((((h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) | ⟨t, ht, h⟩) |
    ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩) | ⟨t, ht, h⟩ <;> subst h <;>
    simp only at hne ⊢
  all_goals first
    | linarith
    | exact absurd rfl hne
    | exact (H1 (t + 1) (by omega) (by omega)).1
    | (have := (H2 (t + 1) (by omega) (by omega)).1; linarith)
    | exact (H1 (t + 1) (by omega) (by omega)).2.1
    | (have := (H2 (t + 1) (by omega) (by omega)).2.1; linarith)
    | exact (H1 (t + 1) (by omega) (by omega)).2.2
    | exact off (t + 1) (by omega) (by omega)

/-- **Proposition `prop:family-dual`, even `n ≥ 10`**: the uniform distribution is the only optimal
Alice strategy for `G_n`. -/
theorem dual_unique (k : ℕ) (hk : 2 ≤ k) (y : V → V → ℚ) (hy : AliceOpt (vs k) (garc k) (rho k) y) :
    ∀ q ∈ oarcs k, y q.1.1 q.1.2 = 1 / ((6 * k + 14 : ℕ) : ℚ) := by
  have hk1 : 1 ≤ k := by omega
  have hall := all_but_one k hk y hy
  set c := y .T1 (.U 1) with hc
  -- step (v): the order `h` makes `2n - 3` arcs of `G_n` forward, not `U1 → T0`
  have hth := tight_h k hk y hy
  have hhu := aliceWeight_tight k hk1 (r_h k) (tight_h k hk (unif k) (unif_opt k hk1))
  have hback : ¬ r_h k (.U 1) < r_h k .T0 := by simp [r_h]
  have hfw : fwdQ (vs k) (r_h k) y = c * (aliceWeight (oarcs k) (r_h k) : ℚ) := by
    rw [fwdQ_garc k hk1 _ y hy.supp, aliceWeight]
    refine list_fwd_const _ _ _ _ (oarcs_snd k) (fun q hq hr => hall q hq (fun e => ?_))
    rw [e] at hr
    exact hback hr
  rw [hfw, hhu, rho] at hth
  have hN : ((6 * k + 14 : ℕ) : ℚ) ≠ 0 := by positivity
  have hcv : c = 1 / ((6 * k + 14 : ℕ) : ℚ) := by
    have h4 : ((4 * k + 9 : ℕ) : ℚ) ≠ 0 := by positivity
    rw [eq_div_iff hN]
    have := hth
    rw [eq_div_iff hN] at this
    have h5 : ((4 * k + 9 : ℕ) : ℚ) * (c * ((6 * k + 14 : ℕ) : ℚ) - 1) = 0 := by linarith
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact absurd h6 h4
    · linarith
  -- the total: `U1 → T0` gets the rest
  have htot := hy.total
  rw [psum_garc k hk1 y hy.supp, list_sum_split _ y c (.U 1, .T0) (oarcs_snd k) (hall),
    oarcs_total k hk1] at htot
  have hcount : ((oarcs k).map (fun q => if q.1 = ((.U 1, .T0) : V × V) then 1 else 0)).sum = 1 := by
    simp [oarcs, Function.comp_def]
  rw [hcount] at htot
  have hue : y (.U 1) .T0 = c := by
    have h1 : c * ((6 * k + 14 : ℕ) : ℚ) = 1 := by rw [hcv]; field_simp
    simp only [Nat.cast_one, mul_one] at htot
    linarith
  intro q hq
  by_cases he : q.1 = (.U 1, .T0)
  · rw [show q.1.1 = .U 1 from by rw [he], show q.1.2 = .T0 from by rw [he], hue, hcv]
  · rw [hall q hq he, hcv]

end Tsigma.Even
