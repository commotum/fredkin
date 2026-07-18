import ConservativeLogic.Billiard.Interface
import ConservativeLogic.Billiard.Collision
import ConservativeLogic.Billiard.Discrete
import ConservativeLogic.Billiard.Geometry
import ConservativeLogic.Billiard.Figure14

/-!
# Opt-in constrained billiard-ball abstraction

This umbrella exports the exact unequal-width interaction and switch
interfaces, a selected four-channel collision permutation and its legal local
subset, independent finite scattering layers, directed sampled routes, mirror
turns, an equal-endpoint detour, sampled crossing checks, and a four-tick
Figure 14 reconstruction.

It is intentionally separate from `ConservativeLogic` and
`ConservativeLogic.API`.  The module supplies neither continuous hard-ball
mechanics nor Figures 17--18, arbitrary physical routing, P8 bounds, physical
time reversal, energy, dissipation, or thermodynamic conclusions.
-/

namespace ConservativeLogic.Billiard

end ConservativeLogic.Billiard
