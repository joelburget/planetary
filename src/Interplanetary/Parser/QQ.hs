module Interplanetary.Parser.QQ where

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

tm :: QuasiQuoter
tm = QuasiQuoter { quoteExp = quoteTmExp }

quoteTmExp :: String -> TH.ExpQ
quoteTmExp = do
  loc <- TH.location
  let pos =  (TH.loc_filename loc,
             fst (TH.loc_start loc),
             snd (TH.loc_start loc))
  tm <- parseTm pos s
  dataToExpQ (const Nothing `extQ` antiTmExp) tm

antiTmExp :: Tm -> Maybe (TH.Q TH.Exp)
antiTmExp  (AntiIntTm v)  = Just $ TH.appE  (TH.conE (TH.mkName "IntTm"))
                                                (TH.varE (TH.mkName v))
antiTmExp  (AntiTm v)     = Just $ TH.varE  (TH.mkName v)
antiTmExp  _              = Nothing
