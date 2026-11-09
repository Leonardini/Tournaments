import TsigmaProof.Even
import TsigmaProof.Odd

/-! # The completions are tournaments: exactly one arc between any two distinct vertices -/

namespace Tsigma

namespace Even

theorem tarc_total (k : ℕ) (x y : V) (hx : valid k x) (hy : valid k y) (hxy : x ≠ y) :
    tarc k x y ∨ tarc k y x := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp [tarc, garc, sigma, valid] at hx hy hxy ⊢ <;> (try split_ifs) <;> omega

theorem tarc_asymm (k : ℕ) (x y : V) (h : tarc k x y) : ¬ tarc k y x := by
  rcases x with _ | _ | _ | _ | _ | _ | a | a <;> rcases y with _ | _ | _ | _ | _ | _ | b | b <;>
    simp [tarc, garc, sigma, valid] at h ⊢ <;> (try split_ifs at h ⊢) <;> omega

end Even

namespace Odd

theorem tarc_total (k : ℕ) (x y : V) (hx : valid k x) (hy : valid k y) (hxy : x ≠ y) :
    tarc k x y ∨ tarc k y x := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;>
    rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp [tarc, garc, sigma, valid] at hx hy hxy ⊢ <;> omega

theorem tarc_asymm (k : ℕ) (x y : V) (h : tarc k x y) : ¬ tarc k y x := by
  rcases x with _ | _ | _ | _ | _ | _ | _ | _ | _ | a | a <;>
    rcases y with _ | _ | _ | _ | _ | _ | _ | _ | _ | b | b <;>
    simp [tarc, garc, sigma, valid] at h ⊢ <;> omega

end Odd

end Tsigma
