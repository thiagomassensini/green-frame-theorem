import GreenFrame.Arithmetic.AdmissiblePartition
import GreenFrame.Arithmetic.NormalizedWeights
import GreenFrame.Arithmetic.CarryWitness
import GreenFrame.Analysis.PythagoreanSplit
import GreenFrame.Analysis.GreenBounds
import GreenFrame.Analysis.FullFrame
import GreenFrame.Analysis.FrameOperator
import GreenFrame.Analysis.CanonicalParseval
import GreenFrame.Analysis.PoissonCompletion
import GreenFrame.Analysis.GraphRange
import GreenFrame.Analysis.NontrivialBulk
import GreenFrame.Finite.Sections
import GreenFrame.Finite.StrongLimit
import GreenFrame.Concrete.Arithmetic.PositionalDepth
import GreenFrame.Concrete.Analysis.InfinitePartition
import GreenFrame.Concrete.Analysis.GreenStencilComplex
import GreenFrame.Concrete.Analysis.GreenReindexing
import GreenFrame.Concrete.Analysis.GreenBesselConstants
import GreenFrame.Concrete.Analysis.GreenStateEnergy
import GreenFrame.Concrete.Analysis.GreenCurrentCameraBound
import GreenFrame.Concrete.Analysis.GreenCurrentBound
import GreenFrame.Concrete.Analysis.GreenParentBound
import GreenFrame.Concrete.Analysis.GreenGrandparentBound
import GreenFrame.Concrete.Analysis.GreenCoordinateMajorant

/-!
# Public API — All-Bases Green Frame Theorem

The public root currently exports the historical abstract layer and the new
remote-first concrete reconstruction. Concrete modules are added only after
their exact GitHub Actions SHA passes the pinned Lean audit.
-/
