{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language PatternSynonyms #-}
{-# language RecordWildCards #-}
{-# language TypeApplications #-}
module Tests.Parser where

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

parserTest
  :: (Eq a, Show a)
  => String
  -> CoreParser Token Parser a
  -> a
  -> TestTree
parserTest input parser parsed = testCase input $
  case runTokenParse parser input of
    Right actual -> parsed @?= actual
    Left errMsg -> assertFailure errMsg

unitTests :: TestTree
unitTests = testGroup "checking"
  [ parserTest "X" identifier "X"

  , parserTest "X" parseValTy' (VTy"X")

  , parserTest "X | X Y" parseConstructors
    [ ConstructorDecl [VTy"X"]
    , ConstructorDecl [VTy"X", VTy"Y"]
    ]
  , parserTest "1 X" parseDataTy $
    DataTy oneUid [TyArgVal (VTy"X")]

  -- also test with args
  -- Bool
  , parserTest "data = | " parseDataDecl $
    DataTypeInterface []
      [ ConstructorDecl []
      , ConstructorDecl []
      ]

  -- TODO: this syntax is deeply unintuitive
  -- TODO: also test with effect parameter
  -- Either
  , parserTest "data X Y = X | Y" parseDataDecl $
    DataTypeInterface [("X", ValTy), ("Y", ValTy)]
      [ ConstructorDecl [VTy"X"]
      , ConstructorDecl [VTy"Y"]
      ]

  -- also test effect ty, multiple instances
  , parserTest "1 X" parseInterfaceInstance $ (oneUid, [TyArgVal (VTy"X")])

  , parserTest "1 [0]" parseInterfaceInstance $ (oneUid, [
    TyArgAbility (Ability ClosedAbility mempty)
    ])

  , parserTest "1 []" parseInterfaceInstance $ (oneUid, [
    TyArgAbility (Ability OpenAbility mempty)
    ])

  , parserTest "1" parseInterfaceInstance $ (oneUid, [])

  , parserTest "0" parseAbilityBody closedAbility
  , parserTest "0|1" parseAbilityBody $
    Ability ClosedAbility (uIdMapFromList [(oneUid, [])])
  , parserTest "e" parseAbilityBody emptyAbility
  , parserTest "e|1" parseAbilityBody $
    Ability OpenAbility (uIdMapFromList [(oneUid, [])])

  -- TODO: parseAbility
  , parserTest "[0|1]" parseAbility $
    Ability ClosedAbility (uIdMapFromList [(oneUid, [])])

  , parserTest "[]" parseAbility emptyAbility
  , parserTest "[0]" parseAbility closedAbility

  , parserTest "[] X" parsePeg $ Peg emptyAbility (VTy"X")
  , parserTest "[]X" parsePeg $ Peg emptyAbility (VTy"X")
  , parserTest "[] 1 X" parsePeg $
    Peg emptyAbility (DataTy oneUid [TyArgVal (VTy"X")])

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

  , parserTest "Z!" parseApplication $ Cut (Application []) (V"Z")
  , parserTest "Z Z Z" parseApplication $
      Cut (Application [V"Z", V"Z"]) (V"Z")

  -- TODO:
  -- * parseLetRec
  -- * parseCase
  -- * parseHandle
  -- * parseUseNoAp
  -- * parseConstruction
  -- * parseValue
  , parserTest "let Z : forall. X = W in Z" parseLet $
    -- TODO use `let_`
    Cut
      (Let (polytype [] (VTy"X")) (abstract1 "Z" (V"Z")))
      (V"W")

  , let defn = unlines
          [ "let on : forall X Y. {X -> {X -> []Y} -> []Y} ="
          , "  \\x f -> f x in on n (\\x -> body)"
          ]
        compDomain = [VTy"X", SuspendedTy (CompTy [VTy"X"] (Peg emptyAbility (VTy"Y")))]
        compCodomain = Peg emptyAbility (VTy"Y")
        polyVal = SuspendedTy (CompTy {..})
        polyBinders = [("X", ValTy), ("Y", ValTy)]
        pty = polytype polyBinders polyVal
        result = let_ "on" pty
          (Value $ lam ["x", "f"] (Cut (Application [V"x"]) (V"f")))
          -- Kind of a hack: use a no-argument lambda to convert from term to
          -- value
          (lam [] $
            Cut (Application [V"n", Value $ lam ["x"] (V"body")]) (V"on"))
    in parserTest defn parseLet result

  , let defn = unlines
          [ "case x of"
          , "  e829515d5"
          , "    | -> y"
          , "    | a b c -> z"
          ]
        cont = case_ (mkUid @Integer 0xe829515d5)
          [ ([], Variable "y")
          , (["a", "b", "c"], Variable "z")
          ]
        result = Cut cont (Variable "x")
    in parserTest defn parseCase result

  -- , let defn = unlines
  --         [ "catch : <Abort>X -> {X} -> X"
  --         , "  = \\x -> "
  --         -- , "x               _ = x"
  --         -- , "<aborting -> _> h = h!"
  --         ]
  --   in parserTest defn
  ]
