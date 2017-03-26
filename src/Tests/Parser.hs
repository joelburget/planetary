{-# LANGUAGE PackageImports #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE PatternSynonyms #-}
module Tests.Parser where

import qualified Data.IntMap as IntMap
import Test.Tasty
import Test.Tasty.HUnit
import Text.Trifecta
import "indentation-trifecta" Text.Trifecta.Indentation
import Bound

import Interplanetary.Syntax
import Interplanetary.Parser

-- "(\\x -> x : Unit -> [e]Unit)"
-- "(\\x -> x : Unit -> [o]Unit)"
-- "unit : Unit"

parserTest :: (Eq a, Show a) => String -> CoreParser Token Parser a -> a -> TestTree
parserTest input parser parsed = testCase input $
  case runTokenParse parser input of
    Right actual -> parsed @=? actual
    Left errMsg -> assertFailure errMsg

unitTests :: TestTree
unitTests = testGroup "checking"
  [ parserTest "X" identifier "X"

  , parserTest "X" parseValTy' (VTy"X")

  , parserTest "X | X Y" parseConstructors
    [ DataConstructor [VTy"X"]
    , DataConstructor [VTy"X", VTy"Y"]
    ]
  , parserTest "1 X" parseDataTy $
    DataTy 1 [TyArgVal (VTy"X")]

  -- also test with args
  -- Bool
  , parserTest "data = | " parseDataDecl $
    DataTypeInterface []
      [ DataConstructor []
      , DataConstructor []
      ]

  -- TODO: this syntax is deeply unintuitive
  -- TODO: also test with effect parameter
  -- Either
  , parserTest "data X Y = X | Y" parseDataDecl $
    DataTypeInterface [("X", ValTy), ("Y", ValTy)]
      [ DataConstructor [VTy"X"]
      , DataConstructor [VTy"Y"]
      ]

  -- also test effect ty, multiple instances
  , parserTest "1 X" parseInterfaceInstance $ (1, [TyArgVal (VTy"X")])

  , parserTest "1 [0]" parseInterfaceInstance $ (1, [
    TyArgAbility (Ability ClosedAbility IntMap.empty)
    ])

  , parserTest "1 []" parseInterfaceInstance $ (1, [
    TyArgAbility (Ability (OpenAbility "e") IntMap.empty)
    ])

  , parserTest "1" parseInterfaceInstance $ (1, [])

  , parserTest "0" parseAbilityBody closedAbility
  , parserTest "0|1" parseAbilityBody $
    Ability ClosedAbility (IntMap.fromList [(1, [])])
  , parserTest "e" parseAbilityBody emptyAbility
  , parserTest "e|1" parseAbilityBody $
    Ability (OpenAbility "e") (IntMap.fromList [(1, [])])

  -- TODO: parseAbility
  , parserTest "[0|1]" parseAbility $
    Ability ClosedAbility (IntMap.fromList [(1, [])])

  , parserTest "[]" parseAbility emptyAbility
  , parserTest "[0]" parseAbility closedAbility

  , parserTest "[] X" parsePeg $ Peg emptyAbility (VTy"X")
  , parserTest "[]X" parsePeg $ Peg emptyAbility (VTy"X")
  , parserTest "[] 1 X" parsePeg $
    Peg emptyAbility (DataTy 1 [TyArgVal (VTy"X")])

  , parserTest "X" parseCompTy $ CompTy [] (Peg emptyAbility (VTy"X"))
  , parserTest "X -> X" parseCompTy $
    CompTy [VTy"X"] (Peg emptyAbility (VTy"X"))
  , parserTest "X -> []X" parseCompTy $
    CompTy [VTy"X"] (Peg emptyAbility (VTy"X"))
  , parserTest "X -> X -> X" parseCompTy $
    CompTy [VTy"X", VTy"X"] (Peg emptyAbility (VTy"X"))

  , parserTest "{X -> X}" parseValTy $ SuspendedTy $
    CompTy [VTy"X"] (Peg emptyAbility (VTy"X"))
  , parserTest "X" parseValTy (VTy"X")
  , parserTest "(X)" parseValTy (VTy"X")

  , parserTest "X -> X" parseCommandDecl $ CommandDeclaration [VTy"X"] (VTy"X")

  , parserTest "interface X Y = X -> Y | Y -> X" parseInterface $
    EffectInterface [("X", ValTy), ("Y", ValTy)]
      [ CommandDeclaration [VTy"X"] (VTy"Y")
      , CommandDeclaration [VTy"Y"] (VTy"X")
      ]

  , parserTest "Z!" parseApplication $ OperatorApplication (V"Z") []
  , parserTest "Z Z Z" parseApplication $ OperatorApplication (V"Z") [V"Z", V"Z"]

  -- TODO: parseRawTm', parseRawTm, parseLetRec
  , parserTest "let Z : forall. X = W in Z" parseLet $
    Let (Polytype [] (VTy"X")) (V"W") (abstract1 "Z" (V"Z"))

  , let defn = unlines
          [ "let on : forall X Y. {X -> {X -> []Y} -> []Y} ="
          , "  \\x f -> f x in on n (\\x -> body)"
          ]
        compDomain = [VTy"X", SuspendedTy (CompTy [VTy"X"] (Peg emptyAbility (VTy"Y")))]
        compCodomain = Peg emptyAbility (VTy"Y")
        polyVal = SuspendedTy (CompTy {..})
        polyBinders = [("X", ValTy), ("Y", ValTy)]
        pty = Polytype {..}
        result = let_ "on" pty
          (lam ["x", "f"] (OperatorApplication (V"f") [V"x"]))
          (OperatorApplication (V"on") [V"n", lam ["x"] (V"body")])
    in parserTest defn parseLet result

  -- , let defn = unlines
  --         [ "catch : <Abort>X -> {X} -> X"
  --         , "  = \\x -> "
  --         -- , "x               _ = x"
  --         -- , "<aborting -> _> h = h!"
  --         ]
  --   in parserTest defn
  ]
