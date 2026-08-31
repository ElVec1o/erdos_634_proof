import Erdos634.AnchoredChain
import Erdos634.AngleArithmetic
import Erdos634.AngleSumAssembled
import Erdos634.AngleSumDissection
import Erdos634.AngleSumScope
import Erdos634.ApexRigidity
import Erdos634.BAdjacency
import Erdos634.BaseAlphaBetaPrime
import Erdos634.BaseBetaCorners
import Erdos634.BaseBetaE1
import Erdos634.BaseBetaMod12
import Erdos634.BaseBetaWalkArith
import Erdos634.BaseBetaWalks
import Erdos634.Beeson3NotPrime
import Erdos634.CChord
import Erdos634.CevianSplit
import Erdos634.CevianTiling28
import Erdos634.CevianTiling63
import Erdos634.ChordDecomp
import Erdos634.ChordInterface
import Erdos634.Collar
import Erdos634.ConeScaling
import Erdos634.CongruentAngles
import Erdos634.Contiguity
import Erdos634.CorridorLowStop
import Erdos634.CosetPropagation
import Erdos634.DirectionGroup
import Erdos634.Dissection
import Erdos634.E2Join
import Erdos634.EdgeChain
import Erdos634.EquilateralConic
import Erdos634.FanKill
import Erdos634.FanPruneSound
import Erdos634.FanStep
import Erdos634.FibonacciFamilies
import Erdos634.ForcedRow
import Erdos634.Frontier
import Erdos634.Gamma2Alpha
import Erdos634.GammaC
import Erdos634.GeneralPillars
import Erdos634.Inflation
import Erdos634.Interface
import Erdos634.IntervalChain
import Erdos634.InvariantCore
import Erdos634.InvariantProduct
import Erdos634.IsoAlphaPrime
import Erdos634.LabelCalculus
import Erdos634.LadderInvariant
import Erdos634.LambdaFactor
import Erdos634.MarchAssembly
import Erdos634.MarchJunctions
import Erdos634.MarchRecurrence
import Erdos634.MasterLemmas
import Erdos634.MidTriangle
import Erdos634.Mod12
import Erdos634.OffsetForcing
import Erdos634.OrderForcing
import Erdos634.OrientBridge
import Erdos634.Pentagon
import Erdos634.PentagonLemma
import Erdos634.PgramTiling22
import Erdos634.PgramTiling52
import Erdos634.PinBuffer
import Erdos634.PinLemma
import Erdos634.PinPlumbing
import Erdos634.PinRay
import Erdos634.Primitives
import Erdos634.Rationality
import Erdos634.RationalityFree
import Erdos634.Rigidity
import Erdos634.RogueChord
import Erdos634.RogueContainment
import Erdos634.RogueFan
import Erdos634.RogueMirror
import Erdos634.RunOrientation
import Erdos634.ScaleBreak
import Erdos634.ScaleRigidity
import Erdos634.SecondEdge
import Erdos634.SectorArea
import Erdos634.SegmentDense
import Erdos634.SideNoB
import Erdos634.SupportFace
import Erdos634.SurplusLattice
import Erdos634.TangentCone
import Erdos634.Tiling28
import Erdos634.Tiling44
import Erdos634.Tiling77
import Erdos634.Tiling99
import Erdos634.TransverseChain
import Erdos634.TwoPiThirdCorners
import Erdos634.V1Assembly
import Erdos634.V1Gaps
import Erdos634.VertexSector
import Erdos634.W2Core
import Erdos634.WalkEquation
import Erdos634.WallChain
import Erdos634.Walls13
import Erdos634.Wedge
import Erdos634.ZhangTargets
-- All.lean — aggregator. Importing this module pulls in the entire corpus, so compiling it is a
-- single end-to-end check that every module elaborates and that their olean interfaces agree.
--
-- WHY THIS EXISTS. The library root `Erdos634.lean` is not an index: it is a substantive module (the
-- arithmetic layer of the prime case) that imports only Mathlib. Consequently `lake build`, whose
-- default target is that root, compiles one file and not the corpus. Modules here are otherwise
-- largely standalone — only `Dissection`, `E2Join`, `SecondEdge` and `Frontier` import a sibling —
-- so nothing forced them to be checked together until now.
--
-- To verify the whole corpus:
--     lean --root=. lean/All.lean
--
-- Verified 2026-08-11: all 67 modules elaborate clean, no `sorry`, no new axioms.
-- 2026-08-15: 69 modules — `EdgeChain` and `WallChain` (the G3 chain layer) added.
-- 2026-08-16: 70 modules — `ForcedRow` (the A4 forced-row arithmetic skeleton) added.
-- 2026-08-16: 72 modules — `VertexSector` and `AngleSumDissection` (the G2 payment:
--   `Dissection.hasAngleSums` is a theorem) added.
import Erdos634.MarchStep
import Erdos634.WedgeExtremal
import Erdos634.JunctionWedge
import Erdos634.EdgeDisjoint
import Erdos634.ChainOrder
import Erdos634.ChainInstance
import Erdos634.BaseSelection
import Erdos634.WallEdges
import Erdos634.ShadowCover
import Erdos634.ChainEnum
import Erdos634.BaseChain
import Erdos634.WallFace
import Erdos634.OrientWord
import Erdos634.Placement
import Erdos634.WallSide
import Erdos634.WallInjective
import Erdos634.BridgeC
import Erdos634.BaseCountsE1
import Erdos634.GammaCascade
import Erdos634.VertexFigureReal
import Erdos634.NonIntegrality
import Erdos634.StubGap
import Erdos634.Unsplittable
import Erdos634.NormForm
import Erdos634.FibExtremal
import Erdos634.SolvCore
import Erdos634.TilePlacement
import Erdos634.SideWall
import Erdos634.DissectionMap
import Erdos634.Subdivision
import Erdos634.ChainWalk
import Erdos634.EqSpecAlgebra
import Erdos634.MemberUniform
import Erdos634.AngleThreshold
