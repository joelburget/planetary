{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
module Interplanetary.Patterns where

import Data.Aeson
import Data.Aeson.Types (Parser)
import Data.Scientific (toBoundedInteger)
import Data.Text (Text)
import qualified Data.Vector as V
import Data.Vector (Vector)

-- The first couple patterns are for manipulating vectors

pattern V2 :: a -> a -> Vector a
pattern V2 a b <- (V.toList -> [a, b]) where
  V2 a b = V.fromList [a, b]

pattern Vx :: [a] -> Vector a
pattern Vx lst <- (V.toList -> lst) where
  Vx lst = V.fromList lst

-- The rest define the Aeson serialization format

tj :: ToJSON a => a -> Value
tj = toJSON

fj :: FromJSON a => Value -> Parser a
fj = parseJSON

pattern Arr :: [Value] -> Value
pattern Arr lst <- (Array (V.toList -> lst)) where
  Arr lst = Array (V.fromList lst)

pattern Domain'Atomic :: Value -> Value
pattern Domain'Atomic dom = Arr ["atomic", dom]

pattern Domain'Nominal :: Value -> Value
pattern Domain'Nominal dom = Arr ["nominal", dom]

pattern Domain'Positional :: Value -> Value
pattern Domain'Positional dom = Arr ["positional", dom]

pattern Location'Nominal :: Text -> Value
pattern Location'Nominal str <- Arr ["name", String str] where
  Location'Nominal str = Arr ["name", tj str]

pattern Location'Positional :: Int -> Value
pattern Location'Positional i
    <- Arr ["index", Number (toBoundedInteger -> Just i)] where
  Location'Positional i = Arr ["index", tj i]

pattern Location'Atomic :: Value
pattern Location'Atomic = "atom"

pattern Term_Computation :: Value -> Value -> Value
pattern Term_Computation val coval     = Arr ["computation", val  , coval]

pattern Term_Value :: Value -> Value
pattern Term_Value val                 = Arr ["value",       val         ]

pattern Term_Covalue :: Value -> Value
pattern Term_Covalue coval             = Arr ["covalue",     coval       ]

pattern Term_Bound :: Value -> Value -> Value
pattern Term_Bound level loc           = Arr ["bound",       level, loc  ]

pattern Term_Quote :: Value -> Value
pattern Term_Quote tm                  = Arr ["quote",       tm          ]

pattern Term_Splice :: Value -> Value
pattern Term_Splice tm                 = Arr ["splice",      tm          ]

pattern Term_External :: Text -> Value
pattern Term_External addr = Arr ["external", String addr]

pattern Value_Sum :: Value -> Value -> Value
pattern Value_Sum loc tm = Arr ["sum", loc, tm]

pattern Value_Product :: Value -> Value
pattern Value_Product dom = Arr ["product", dom]

pattern Covalue_Case :: Value -> Value
pattern Covalue_Case dom = Arr ["case", dom]

pattern Covalue_Match :: Value -> Value
pattern Covalue_Match tm = Arr ["match", tm]
