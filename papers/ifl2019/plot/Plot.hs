
import Graphics.Gnuplot.Simple
import qualified Graphics.Gnuplot.Terminal.SVG as SVG


new :: [(Double,Double)]
new = zip [1,2,3,4,5,6,7,8,9,10,11] [193,391,626,875,1145,1242,1534,1677,1798,2080,2314]

old :: [(Double,Double)]
old = zip [1,2,3,4,5,6,7,8,9,10,11] [100,138,189,262,296,389,492,526,545,587,627]

main
  = plotPaths
      [Key (Just [])
      -- ,YRange (x,y)
      ,LineStyle 3 [PointSize 0.5]
      ,XLabel "grammar size"
      ,YLabel "time(ms)"
      ,Title "AspectAG Benchmark"
      ,Custom "grid" []
      , terminal (SVG.cons ("plot.svg"))
      ,Custom "style line" ["3","lc","3","lw","3"]
      ]  [old,new]
