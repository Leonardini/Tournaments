import TsigmaProof

/-! Lists the axioms behind the main theorems; run with `lake env lean AxiomReport.lean`.
Only Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) may appear. -/

#print axioms Tsigma.Even.value
#print axioms Tsigma.Even.value_exact
#print axioms Tsigma.Odd.value
#print axioms Tsigma.Odd.value_exact
#print axioms Tsigma.Even.tarc_total
#print axioms Tsigma.Even.tarc_asymm
#print axioms Tsigma.Odd.tarc_total
#print axioms Tsigma.Odd.tarc_asymm
