import TsigmaProof.Main
import TsigmaProof.Duality

/-!
# Every optimal Alice strategy for a completion lives on the obstacle (Lemma `lem:family-loads`)

With the strict certificates of `bob_any` (Bob's weights of total `c(3n - 4)`, every arc of the
completion forward with weight at least `c(2n - 3)`, every arc outside the obstacle with weight at
least `c(2n - 3) + 1`), `support_of_strict` shows that an optimal Alice strategy for `Ĝ_n` (`Ĥ_n`)
puts no weight outside `G_n` (`H_n`).
-/

namespace Tsigma

namespace Even

/-- The value `ρ_n = (2n - 3)/(3n - 4)` for `n = 2k + 6`. -/
def rho (k : ℕ) : ℚ := ((4 * k + 9 : ℕ) : ℚ) / ((6 * k + 14 : ℕ) : ℚ)

theorem linOrd_of_inj (k : ℕ) (r : V → ℕ)
    (h : ∀ x y, valid k x → valid k y → x ≠ y → r x ≠ r y) : LinOrd (vs k) r :=
  fun x hx z hz hxz => h x z ((mem_vs k x).1 hx) ((mem_vs k z).1 hz) hxz

theorem tarc_valid {k : ℕ} {x y : V} (h : tarc k x y) : x ∈ vs k ∧ y ∈ vs k :=
  ⟨(mem_vs k x).2 h.1, (mem_vs k y).2 h.2.1⟩

/-- **Lemma `lem:family-loads`**, for `Ĝ_n`: an optimal Alice strategy for the completion is an
optimal Alice strategy for `G_n`, supported on its arcs. -/
theorem support (k : ℕ) (hk : 1 ≤ k) (y : V → V → ℚ) (hy : AliceOpt (vs k) (tarc k) (rho k) y) :
    AliceOpt (vs k) (garc k) (rho k) y := by
  obtain ⟨c, L, hc, hinj, htot, hbob, hstr⟩ := bob_any k hk
  have hzero := support_of_strict (vs k) L (c * (6 * k + 14)) (c * (4 * k + 9)) (rho k) htot
    (by unfold rho; push_cast; field_simp)
    (fun p hp => linOrd_of_inj k p.2 (fun x z hx hz hxz => hinj p hp x z hx hz hxz))
    (tarc k) (garc k) (fun x hx z hz h => hbob x hx z hz h) hstr y hy
  refine ⟨hy.nonneg, ?_, hy.total, hy.opt⟩
  intro x z h0
  have ht := hy.supp x z h0
  obtain ⟨hx, hz⟩ := tarc_valid ht
  by_contra hg
  exact h0 (hzero x hx z hz hg)

end Even

namespace Odd

/-- The value `ρ_n = (2n - 3)/(3n - 4)` for `n = 2k + 9`. -/
def rho (k : ℕ) : ℚ := ((4 * k + 15 : ℕ) : ℚ) / ((6 * k + 23 : ℕ) : ℚ)

theorem linOrd_of_inj (k : ℕ) (r : V → ℕ)
    (h : ∀ x y, valid k x → valid k y → x ≠ y → r x ≠ r y) : LinOrd (vs k) r :=
  fun x hx z hz hxz => h x z ((mem_vs k x).1 hx) ((mem_vs k z).1 hz) hxz

theorem tarc_valid {k : ℕ} {x y : V} (h : tarc k x y) : x ∈ vs k ∧ y ∈ vs k :=
  ⟨(mem_vs k x).2 h.1, (mem_vs k y).2 h.2.1⟩

/-- **Lemma `lem:family-loads`**, for `Ĥ_n`. -/
theorem support (k : ℕ) (y : V → V → ℚ) (hy : AliceOpt (vs k) (tarc k) (rho k) y) :
    AliceOpt (vs k) (garc k) (rho k) y := by
  obtain ⟨c, L, hc, hinj, htot, hbob, hstr⟩ := bob_any k
  have hzero := support_of_strict (vs k) L (c * (6 * k + 23)) (c * (4 * k + 15)) (rho k) htot
    (by unfold rho; push_cast; field_simp)
    (fun p hp => linOrd_of_inj k p.2 (fun x z hx hz hxz => hinj p hp x z hx hz hxz))
    (tarc k) (garc k) (fun x hx z hz h => hbob x hx z hz h) hstr y hy
  refine ⟨hy.nonneg, ?_, hy.total, hy.opt⟩
  intro x z h0
  have ht := hy.supp x z h0
  obtain ⟨hx, hz⟩ := tarc_valid ht
  by_contra hg
  exact h0 (hzero x hx z hz hg)

end Odd

end Tsigma
