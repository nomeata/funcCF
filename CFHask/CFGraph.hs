{- |
 Generates a visual representation of a control flow graph, by overlaying a
 pretty-printed syntax output with a graphviz-generated graph.

 This code uses the command line tools \"neato\", \"pdf2ps\" and \"pdftk\".
 -}
{-# LANGUAGE TypeOperators #-}
module CFGraph where

import Graphics.PDF
import Language.Dot
import Data.Map (keys,(!))
import Text.Printf
import System.Process
import System.Directory
import System.IO

import CPSScheme
import CPSPrint
import Common

-- | The font that is used to generate the code listings.
font :: PDFFont
font = PDFFont Courier 11

-- | Assuming a mono-spaced font, this is the width of a character.
theCharWidth :: PDFFloat
theCharWidth = charWidth font 'M'

-- | The height of a character.
theCharHeight :: PDFFloat
theCharHeight = getHeight font

-- | Creates a PDF file containing the given text, without any padding or
-- borders, using the font specified by 'font'
renderCodeToFile :: FilePath -> String -> IO ()
renderCodeToFile fn code = do
    runPdf fn standardDocInfo pageRect $ do
        page <- addPage Nothing
        drawWithPage page $ sequence $
            zipWith (\ln line -> drawText $ text font 0 (fromIntegral ln * theCharHeight) (toPDFString line))
                    [lineNumber-1,lineNumber-2..0] ls
  where ls = lines (removeLambdas code)
        lineLength = maximum (map length ls) 
        lineNumber = length ls
        pageWidth = ceiling (fromIntegral lineLength * theCharWidth)
        pageHeight = ceiling (fromIntegral lineNumber * theCharHeight)
        pageRect = PDFRect 0 0 pageWidth pageHeight

-- | Creates a 'Graph'
createDotFromGraph :: Integer  -- ^ number of lines
                   -> Integer  -- ^ number of columns
                   -> [Label :× Label] -- ^ the list of edges to draw
                   -> (Label :⇀ (Integer, Integer)) -- ^ the position of the
                                                    -- nodes, in characters
                   -> Graph
createDotFromGraph ls cs edges coords  = Graph UnstrictGraph DirectedGraph Nothing (settings ++ nodes ++ edges')
  where settings =
            [ AttributeStatement GraphAttributeStatement
                [ AttributeSetValue (NameId "bb")
                                    (StringId (printf "0,0,%.4f,%.4f" (width) (height)))
                , AttributeSetValue (NameId "pad") (StringId "0")
                , AttributeSetValue (NameId "splines") (StringId "true")
                ]
            , AttributeStatement NodeAttributeStatement
                [ AttributeSetValue (NameId "shape") (StringId "point")    
                , AttributeSetValue (NameId "height") (StringId "0.03") 
                ]
            , AttributeStatement EdgeAttributeStatement
                [ AttributeSetValue (NameId "penwidth") (StringId "0.4")
                , AttributeSetValue (NameId "arrowsize") (StringId "0.2")
                , AttributeSetValue (NameId "color") (StringId "#0000FF80")
                ]
            ]
        nodes = map (\l -> let (x,y) = charToPt (coords ! l) in NodeStatement (labelToId l)
                [ AttributeSetValue (NameId "pos")
                                    (StringId (printf "%.4f,%.4f" x y))
                ]
            ) (keys coords)
        edges' = map (\(l1,l2) -> EdgeStatement [
                ENodeId NoEdge (labelToId l1),
                ENodeId DirectedEdge (labelToId l2)
            ] []) edges
        labelToId (Label i) =  NodeId (IntegerId i) Nothing
        charToPt (r,c) = ( (fromIntegral c-0.5) * theCharWidth,
                           (fromIntegral (ls-r)+0.2) * theCharHeight )
        width = fromIntegral $ ceiling (fromIntegral cs * theCharWidth) :: Double
        height = fromIntegral $ ceiling (fromIntegral ls * theCharHeight) :: Double

-- | Creates a 'Graph' given a program and a function generating the required
-- graph
createDotFromCode :: (Prog -> [Label :× Label]) -> Prog -> Graph
createDotFromCode eval prog = createDotFromGraph lineNumber lineLength edges coords
  where edges = eval prog
        (coords, code) = labelPositions '*' $ renderProg True prog
        ls = lines (removeLambdas code)
        lineLength = fromIntegral $ maximum (map length ls) 
        lineNumber = fromIntegral $ length ls

-- | The main function of this module. Writes out a PDF file containing both
-- code and control flow graph
createCodeWithGraph :: (Prog -> [Label :× Label]) -- ^ Generating a graph from a program
                    -> FilePath -- ^ Wanted filename 
                    -> Prog -- ^ Program to draw
                    -> IO ()
createCodeWithGraph eval filename prog = do
    renderCodeToFile codeFileName code 
    let neato = (proc "neato" ["-n","-s","-Tps2"]) { std_in = CreatePipe, std_out = CreatePipe } 
    (Just input, Just pipe, _ ,_) <- createProcess neato
    hPutStr input graph
    hClose input
    let ps2pdf = (proc "ps2pdf" ["-", graphFileName]) { std_in = UseHandle pipe, std_out = CreatePipe }
    (_ , _ , _, ph) <- createProcess ps2pdf
    waitForProcess ph
    let pdftk = proc "pdftk" [graphFileName, "background", codeFileName, "output", filename]
    (_ , _ , _, ph) <- createProcess pdftk
    waitForProcess ph
    removeFile graphFileName
    removeFile codeFileName
  where code = removeLambdas $ snd $ labelPositions ' ' $ renderProg True prog
        codeFileName  = filename ++ ".tmp1.pdf"
        graphFileName = filename ++ ".tmp2.pdf"
        graph = renderDot $ createDotFromCode eval prog

