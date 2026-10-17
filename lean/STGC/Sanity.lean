/-
  Sanity check that the hypothesis of the main theorem is not vacuous: `DDProperty 5` is proved outright, by
  exhaustive computation in the kernel.
-/
import STGC.Defs

namespace STGC

set_option synthInstance.maxHeartbeats 1000000 in
set_option synthInstance.maxSize 4096 in
set_option maxRecDepth 100000 in
theorem dd_five : DDProperty 5 := by
  unfold DDProperty IsFirstOcc IsConst NecklaceAdj
  decide

end STGC
