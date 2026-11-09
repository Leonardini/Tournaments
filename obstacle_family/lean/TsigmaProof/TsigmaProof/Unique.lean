import TsigmaProof.UniqueEven
import TsigmaProof.UniqueOdd
import TsigmaProof.SmallUnique

/-!
# Theorem `thm:family-value`: the uniform distribution on the obstacle is the only optimal Alice strategy

An *optimal Alice strategy* for the completion `Ĝ_n` (`Ĥ_n`) is a nonnegative weighting `y` of its arcs,
of total `1`, under which every linear order of the vertices makes the arcs forward with total weight at
most `ρ_n = (2n - 3)/(3n - 4)`, the predictability of `Ĝ_n` (`Ĥ_n`) proved in `Main.lean`
(`AliceOpt (vs k) (tarc k) (rho k) y`).  The theorems `Even.unique` and `Odd.unique` state that the
uniform distribution `unif k` on the arcs of `G_n` (`H_n`) is one, and that every other one equals it.
In particular `G_n` (`H_n`) is the only minimal obstacle of the completion.
-/

namespace Tsigma

namespace Even

theorem unif_tarc (k : ℕ) (hk : 1 ≤ k) : AliceOpt (vs k) (tarc k) (rho k) (unif k) := by
  obtain ⟨h0, hs, ht, ho⟩ := unif_opt k hk
  refine ⟨h0, fun x z h => ?_, ht, ho⟩
  have hg := hs x z h
  obtain ⟨hx, hz⟩ := garc_valid k hk x z hg
  exact garc_tarc k x z hx hz hg

/-- **Theorem `thm:family-value`, uniqueness, even `n = 2k + 6 ≥ 8`.**  The uniform distribution on the
arcs of `G_n` is an optimal Alice strategy for `Ĝ_n`, and the only one. -/
theorem unique (k : ℕ) (hk : 1 ≤ k) :
    AliceOpt (vs k) (tarc k) (rho k) (unif k) ∧
    ∀ y : V → V → ℚ, AliceOpt (vs k) (tarc k) (rho k) y →
      ∀ x ∈ vs k, ∀ z ∈ vs k, y x z = unif k x z := by
  refine ⟨unif_tarc k hk, fun y hy => ?_⟩
  have hg := support k hk y hy
  have hq : ∀ q ∈ oarcs k, y q.1.1 q.1.2 = 1 / ((6 * k + 14 : ℕ) : ℚ) := by
    rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | h2
    · intro q hq
      rw [small_unique8 y hg q hq]
      norm_num
    · exact dual_unique k h2 y hg
  intro x hx z hz
  unfold unif
  by_cases hgx : garc k x z
  · rw [if_pos hgx]
    obtain ⟨⟨⟨a, b⟩, w⟩, hqm, hqe⟩ := List.mem_map.1
      (garc_mem k x z ((mem_vs k x).1 hx) ((mem_vs k z).1 hz) hgx)
    simp only [Prod.mk.injEq] at hqe
    obtain ⟨rfl, rfl⟩ := hqe
    exact hq _ hqm
  · rw [if_neg hgx]
    by_contra h0
    exact hgx (hg.supp x z h0)

end Even

namespace Odd

theorem oarcs0_snd : ∀ q ∈ oarcs0, q.2 = 1 := by decide

theorem unif_fwd0 (r : V → ℕ) :
    fwdQ (vs 0) r (unif 0) = (aliceWeight oarcs0 r : ℚ) / ((6 * 0 + 23 : ℕ) : ℚ) := by
  rw [fwdQ_garc0 r (unif 0) (unif_supp 0), aliceWeight, Nat.cast_list_sum, List.map_map,
    ← list_sum_div]
  apply congrArg
  apply List.map_congr_left
  intro q hq
  have hg := (oarcs0_arcs q hq).2.2
  have h1 := oarcs0_snd q hq
  simp only [Function.comp_apply, unif, if_pos hg, h1]
  split_ifs <;> simp

theorem unif_opt0 : AliceOpt (vs 0) (garc 0) (rho 0) (unif 0) := by
  have hN : (0 : ℚ) < ((6 * 0 + 23 : ℕ) : ℚ) := by positivity
  refine ⟨fun x z => by unfold unif; split_ifs <;> positivity, unif_supp 0, ?_, ?_⟩
  · rw [psum_garc0 (unif 0) (unif_supp 0)]
    have : (oarcs0.map (fun q => unif 0 q.1.1 q.1.2)) =
        (oarcs0.map (fun q => ((q.2 : ℕ) : ℚ) / ((6 * 0 + 23 : ℕ) : ℚ))) := by
      apply List.map_congr_left
      intro q hq
      simp [unif, (oarcs0_arcs q hq).2.2, oarcs0_snd q hq]
    have h2 : (oarcs0.map (fun q => ((q.2 : ℕ) : ℚ))).sum = ((oarcs0.map Prod.snd).sum : ℕ) := by
      rw [Nat.cast_list_sum, List.map_map]
      rfl
    rw [this, list_sum_div, h2, oarcs0_total]
    norm_num
  · intro r _
    rw [unif_fwd0 r, rho]
    apply div_le_div_of_nonneg_right _ hN.le
    exact_mod_cast alice0 r

theorem unif_tarc (k : ℕ) : AliceOpt (vs k) (tarc k) (rho k) (unif k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain ⟨h0, hs, ht, ho⟩ := unif_opt0
    refine ⟨h0, fun x z h => ?_, ht, ho⟩
    have hg := hs x z h
    have hv : valid 0 x ∧ valid 0 z := by
      rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;>
        rcases z with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;> simp [garc, valid] at hg ⊢ <;> omega
    exact garc_tarc 0 x z hv.1 hv.2 hg
  · obtain ⟨h0, hs, ht, ho⟩ := unif_opt k hk
    refine ⟨h0, fun x z h => ?_, ht, ho⟩
    have hg := hs x z h
    obtain ⟨hx, hz⟩ := garc_valid k hk x z hg
    exact garc_tarc k x z hx hz hg

/-- **Theorem `thm:family-value`, uniqueness, odd `n = 2k + 9 ≥ 9`.**  The uniform distribution on the
arcs of `H_n` is an optimal Alice strategy for `Ĥ_n`, and the only one. -/
theorem unique (k : ℕ) :
    AliceOpt (vs k) (tarc k) (rho k) (unif k) ∧
    ∀ y : V → V → ℚ, AliceOpt (vs k) (tarc k) (rho k) y →
      ∀ x ∈ vs k, ∀ z ∈ vs k, y x z = unif k x z := by
  refine ⟨unif_tarc k, fun y hy => ?_⟩
  have hg := support k y hy
  intro x hx z hz
  unfold unif
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · by_cases hgx : garc 0 x z
    · rw [if_pos hgx]
      have hm : ∀ x ∈ vs 0, ∀ z ∈ vs 0, garc 0 x z → (x, z) ∈ oarcs0.map Prod.fst := by decide
      obtain ⟨⟨⟨a, b⟩, w⟩, hqm, hqe⟩ := List.mem_map.1 (hm x hx z hz hgx)
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      rw [small_unique9 y hg _ hqm]
      norm_num
    · rw [if_neg hgx]
      by_contra h0
      exact hgx (hg.supp x z h0)
  · by_cases hgx : garc k x z
    · rw [if_pos hgx]
      obtain ⟨⟨⟨a, b⟩, w⟩, hqm, hqe⟩ := List.mem_map.1
        (garc_mem k hk x z ((mem_vs k x).1 hx) ((mem_vs k z).1 hz) hgx)
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨rfl, rfl⟩ := hqe
      exact dual_unique k hk y hg _ hqm
    · rw [if_neg hgx]
      by_contra h0
      exact hgx (hg.supp x z h0)

end Odd

end Tsigma
