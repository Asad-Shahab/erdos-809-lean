module
public import Erdos809.Certificate.CoefficientReflection

@[expose] public section

/-! Generated exact scaled table arithmetic. Certificate source SHA256 0499aff9fdffb2da406ef787d79a0f84cd38e3bbd338f2e7d21487db17ceba09.
Scope: stored local coefficient identities; graph enumeration, column semantics,
and PSD linkage are distinct proof obligations.
-/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Erdos809.Certificate.Coefficients
noncomputable def scale : ℕ := 7461504000000000
theorem scale_positive : 0 < scale := by decide
end Erdos809.Certificate.Coefficients
