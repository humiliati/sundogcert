import Sundogcert.Basic
import Sundogcert.Certificate
import Sundogcert.Instance
import Sundogcert.Scaling
import Sundogcert.Looseness
import Sundogcert.CertWall
import Sundogcert.Degradation
import Sundogcert.CheckCost
import Sundogcert.StraightLineCost
import Sundogcert.ShortestPathCert
-- The find/check ledger as a general certificate theory + its instances (N-3):
-- max-flow/min-cut and König (LP-duality optimization), 2-SAT (decision), Pratt (primality).
import Sundogcert.Certifies
import Sundogcert.MaxFlowMinCut
import Sundogcert.MatchingCover
import Sundogcert.TwoSat
import Sundogcert.PrattCert
import Sundogcert.ShadowDecay
import Sundogcert.ShadowDecayGeneral
import Sundogcert.ShadowDecayCauchy
import Sundogcert.HaloGeometry
import Sundogcert.FaradayAB
import Sundogcert.SortingCert
import Sundogcert.RSCertificate
import Sundogcert.DecodingNPHard
import Sundogcert.AxiomAudit
import Sundogcert.ShadowDecayLattice
import Sundogcert.AuditCost
-- Exact tropical-circuit → ReLU-network compilation (circuit-complexity / approx. theory).
import Sundogcert.CircuitNet
-- The cancellation-free (monotone) fragment: locating the monotone-vs-general wall.
import Sundogcert.CancellationFree
-- Depth separation: exponential linear regions from linear tropical depth.
import Sundogcert.DepthSeparation
-- Linear regions as an exact (realization-independent) tropical invariant.
import Sundogcert.RegionCount
-- Folding needs cancellation: the depth-separation witness is not cancellation-free (N-1).
import Sundogcert.FoldCancellation
-- Bounded piece certificate: monotone composition adds pieces (N-1 positive half, quantitative).
import Sundogcert.PieceCover
-- Cancellation-free circuits are convex; cut-based gate lemmas (N-1 circuit-level lift).
import Sundogcert.RegionPoly
-- The cancellation spine: cancellation-free ⇒ uniformly tame (N-2 synthesis anchor).
import Sundogcert.CancellationSpine
-- Exact representability (S3-1): every convex continuous-PL function IS a finite ReLU net.
import Sundogcert.ExactRepr
-- The 3SAT ≤ 3DM ≤ X3C ≤ Decodes Karp reduction (machine-checked correctness).
import Sundogcert.MatchingNPHard
import Sundogcert.SATNPHard
import Sundogcert.VarWheel
import Sundogcert.ClauseGadget
import Sundogcert.SATReduction
import Sundogcert.ThreeDMReindex
import Sundogcert.SATReductionIncidence
import Sundogcert.SATReductionReverse
import Sundogcert.SATReductionForward
import Sundogcert.SATReductionMain
import Sundogcert.Tauroctony
import Sundogcert.AgenticTrace
import Sundogcert.DiscreteHolonomy
import Sundogcert.ContextDecay
import Sundogcert.CuspGerm
import Sundogcert.RetrievalCusp
import Sundogcert.HierarchyHolonomy
import Sundogcert.StructuralSlot
-- Parity barrier (toy half): a finite-order partial parity is not a sufficient statistic
-- for the full-history total parity. Sarnak/Chowla named as the imported wall (P-1).
import Sundogcert.ParityNoSufficientStat
-- The Order-Relative Resolution Law: the slate's one statement (a schema, not a scalar) that the
-- axes (search / pressure / repertoire / determination / find-check) instantiate (B).
import Sundogcert.OrderRelative
