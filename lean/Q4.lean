import Q4.Candidate.ActualCatalogBounds
import Q4.Candidate.ActualCatalogParameters
import Q4.Candidate.ActualCatalogRegime
import Q4.Candidate.ActualDummyUnary
import Q4.Candidate.ActualProgramGeometry
import Q4.Candidate.ActualRecipe
import Q4.Candidate.ActualReductionValue
import Q4.Candidate.ActualSelectedUnary
import Q4.Candidate.ActualSideGeometry
import Q4.Candidate.AlternatingTriples
import Q4.Candidate.AlternationKernel
import Q4.Candidate.AnalyticVariance
import Q4.Candidate.AntiperiodicReplacement
import Q4.Candidate.AntiperiodicThreshold
import Q4.Candidate.BoxAverage
import Q4.Candidate.BoxDerivative
import Q4.Candidate.CandidateSize
import Q4.Candidate.CanonicalEnergy
import Q4.Candidate.CanonicalField
import Q4.Candidate.CatalogDominance
import Q4.Candidate.CatalogSupport
import Q4.Candidate.CatalogTargets
import Q4.Candidate.ComparisonEnergy
import Q4.Candidate.CompleteBackground
import Q4.Candidate.CompleteClassEnergy
import Q4.Candidate.CompleteDrawing
import Q4.Candidate.CompleteFanFields
import Q4.Candidate.CompleteGridEnergy
import Q4.Candidate.CompleteInput
import Q4.Candidate.CompleteProbeFreezing
import Q4.Candidate.ComputedBackground
import Q4.Candidate.ComputedCore
import Q4.Candidate.ConservativeGap
import Q4.Candidate.ConstructedReduction
import Q4.Candidate.ConvexBackground
import Q4.Candidate.ConvexSeparation
import Q4.Candidate.ConvexSeparationGrid
import Q4.Candidate.CoreEncoding
import Q4.Candidate.CoreExtension
import Q4.Candidate.CoreFixedPalette
import Q4.Candidate.CoreLocalGeometry
import Q4.Candidate.CorePaletteForcing
import Q4.Candidate.CoreReducedPairs
import Q4.Candidate.CoreValueBridge
import Q4.Candidate.DiagonalAverage
import Q4.Candidate.DiagonalCoordinates
import Q4.Candidate.DiagonalHalves
import Q4.Candidate.DiagonalRounding
import Q4.Candidate.DoubleCapGrid
import Q4.Candidate.DummyGeometry
import Q4.Candidate.DummyPaletteField
import Q4.Candidate.EnergyLipschitz
import Q4.Candidate.FreezingErrors
import Q4.Candidate.FreezingParameters
import Q4.Candidate.GeometryEncoding
import Q4.Candidate.GlobalGeometryScales
import Q4.Candidate.GridCounts
import Q4.Candidate.GridInitialConstants
import Q4.Candidate.GridLocalization
import Q4.Candidate.GridStepBridge
import Q4.Candidate.GridStepExtension
import Q4.Candidate.IndexedPaletteForcing
import Q4.Candidate.IntervalPoincare
import Q4.Candidate.MacroLayout
import Q4.Candidate.MainSourceEncoding
import Q4.Candidate.OneDimensionalStability
import Q4.Candidate.OperatorPerturbation
import Q4.Candidate.OrdinaryCoreField
import Q4.Candidate.OrdinaryFan
import Q4.Candidate.OrdinaryNonincident
import Q4.Candidate.OrdinaryResponse
import Q4.Candidate.OrdinarySoftRows
import Q4.Candidate.OrdinaryTablePreservation
import Q4.Candidate.OrientationPreservation
import Q4.Candidate.OriginalCapAlternation
import Q4.Candidate.OriginalCapCrossing
import Q4.Candidate.OriginalVertexLayout
import Q4.Candidate.PaletteBounds
import Q4.Candidate.PaletteCounting
import Q4.Candidate.PaletteExhaustion
import Q4.Candidate.PaletteForcing
import Q4.Candidate.ParentBlockExclusion
import Q4.Candidate.PlacedOrdinaryField
import Q4.Candidate.ProbeFreezing
import Q4.Candidate.ProbeFreezingReal
import Q4.Candidate.ProgramCatalog
import Q4.Candidate.ProgramCount
import Q4.Candidate.ProgramExclusion
import Q4.Candidate.ProgramField
import Q4.Candidate.ProgramGeometry
import Q4.Candidate.ProgramIndex
import Q4.Candidate.ProgramPlacement
import Q4.Candidate.ProposedPalette
import Q4.Candidate.RankCorrection
import Q4.Candidate.RankGap
import Q4.Candidate.RankGapPreservation
import Q4.Candidate.RankNonincident
import Q4.Candidate.RankNonselected
import Q4.Candidate.RankResponse
import Q4.Candidate.RankSoftRows
import Q4.Candidate.RankTablePreservation
import Q4.Candidate.RationalEncoding
import Q4.Candidate.ReductionGap
import Q4.Candidate.SideCatalog
import Q4.Candidate.SideDominance
import Q4.Candidate.SliceStability
import Q4.Candidate.SmoothingApproximation
import Q4.Candidate.SourceChordGeometry
import Q4.Candidate.SourceCutBridge
import Q4.Candidate.SourceSelectedEdges
import Q4.Candidate.SquareTranslation
import Q4.Candidate.StabilityConstants
import Q4.Candidate.ThresholdApproximation
import Q4.Candidate.ThresholdHalfSelection
import Q4.Candidate.ThresholdTranslation
import Q4.Candidate.TwoPhaseStability
import Q4.Candidate.UniformInsertion
import Q4.Candidate.UnitIntervalMeasure
import Q4.Candidate.VirtualColumnField
import Q4.Candidate.VirtualColumnMidpoint
import Q4.Candidate.VirtualColumnShape
import Q4.Candidate.VirtualColumnSoftRows
import Q4.Candidate.VirtualColumnSoftSupport
import Q4.CleanWire
import Q4.Counting
import Q4.JointProbe
import Q4.SimultaneousFlip

/-! Explicit entry point for the exact local import closure of ConstructedReduction.
Every original module is copied byte-for-byte. Its existing axiom queries are
rechecked per source by verify.py; historical root-only queries follow below. -/

#print axioms Q4.mono_add_cut
#print axioms Q4.mono_eq_total_sub_cut
#print axioms Q4.mono_le_iff_cut_le
#print axioms Q4.mono_lt_iff_cut_lt
#print axioms Q4.mono_minimizer_iff_cut_maximizer
#print axioms Q4.mono_threshold_iff_cut_threshold
#print axioms Q4.CleanWire.crossings6_exact
#print axioms Q4.CleanWire.crossings7_exact
#print axioms Q4.CleanWire.points6_distinct
#print axioms Q4.CleanWire.points7_distinct
#print axioms Q4.CleanWire.points6_general
#print axioms Q4.CleanWire.points7_general
#print axioms Q4.CleanWire.signals6_indices
#print axioms Q4.CleanWire.signals7_indices
#print axioms Q4.CleanWire.same6_upper
#print axioms Q4.CleanWire.diff6_upper
#print axioms Q4.CleanWire.same7_upper
#print axioms Q4.CleanWire.diff7_upper
#print axioms Q4.CleanWire.compressed6_lower
#print axioms Q4.CleanWire.compressed7_lower
#print axioms Q4.CleanWire.monoCount_xor
#print axioms Q4.CleanWire.normalized_zero
#print axioms Q4.CleanWire.normalization_preserves_score
#print axioms Q4.CleanWire.compression6_covers
#print axioms Q4.CleanWire.compression7_covers
#print axioms Q4.CleanWire.all_colorings6_lower
#print axioms Q4.CleanWire.all_colorings7_lower
#print axioms Q4.CleanWire.same6_exact
#print axioms Q4.CleanWire.diff6_exact
#print axioms Q4.CleanWire.same7_exact
#print axioms Q4.CleanWire.diff7_exact
#print axioms Q4.CleanWire.extendFiniteColoring_agrees
#print axioms Q4.SimultaneousFlip.intSum_zero
#print axioms Q4.SimultaneousFlip.intSum_add
#print axioms Q4.SimultaneousFlip.intSum_sub
#print axioms Q4.SimultaneousFlip.intSum_congr
#print axioms Q4.SimultaneousFlip.intSum_swap
#print axioms Q4.SimultaneousFlip.intSum_point_absent
#print axioms Q4.SimultaneousFlip.intSum_point
#print axioms Q4.SimultaneousFlip.edgeEnergy_eq_monoCount
#print axioms Q4.SimultaneousFlip.selected_add
#print axioms Q4.SimultaneousFlip.selected_sum
#print axioms Q4.SimultaneousFlip.selected_point
#print axioms Q4.SimultaneousFlip.edge_flip_identity
#print axioms Q4.SimultaneousFlip.edge_single_identity
#print axioms Q4.SimultaneousFlip.unary_single_identity
#print axioms Q4.SimultaneousFlip.singleDelta_local
#print axioms Q4.SimultaneousFlip.sum_singleDelta
#print axioms Q4.SimultaneousFlip.totalEnergy_flip_identity
#print axioms Q4.Candidate.ConstructedReduction.constructed_maxcut_instance
