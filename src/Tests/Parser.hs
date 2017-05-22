{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language PatternSynonyms #-}
{-# language RecordWildCards #-}
module Tests.Parser where

import Test.Tasty
import Test.Tasty.HUnit
import Text.Trifecta hiding (expected)
import "indentation-trifecta" Text.Trifecta.Indentation

import Planetary.Core
import Planetary.Support.Parser

-- "(\\x -> x : Unit -> [e]Unit)"
-- "(\\x -> x : Unit -> [o]Unit)"
-- "unit : Unit"

parserTest
  :: (Eq a, Show a)
  => String
  -> CoreParser Token Parser a
  -> a
  -> TestTree
parserTest input parser expected = testCase input $
  case runTokenParse parser input of
    Right actual -> expected @=? actual
    Left errMsg -> assertFailure errMsg

unitTests :: TestTree
unitTests = testGroup "parsing"
  [ parserTest "X" identifier "X"

  , parserTest "X" parseValTy' (VTy"X")

  , parserTest "X | X Y" parseConstructors
    [ ConstructorDecl [VTy"X"]
    , ConstructorDecl [VTy"X", VTy"Y"]
    ]

  , parserTest "X" parseTyArg $ TyArgVal (VTy"X")

  , parserTest "X X X" (many parseTyArg) $
      let x = TyArgVal (VTy"X") in [x, x, x]

  , parserTest "1" parseUid "1"

  , parserTest "123" parseUid "123"

  , parserTest "d:1 X" parseDataTy $
    DataTy "1" [TyArgVal (VTy"X")]

  -- also test with args
  -- Bool
  , parserTest "data Bool = | " parseDataDecl $
    ("Bool", DataTypeInterface []
      [ ConstructorDecl []
      , ConstructorDecl []
      ])

  -- TODO: also test with effect parameter
  , parserTest "data Either X Y = X | Y" parseDataDecl $
    ("Either", DataTypeInterface [("X", ValTy), ("Y", ValTy)]
      [ ConstructorDecl [VTy"X"]
      , ConstructorDecl [VTy"Y"]
      ])

  -- also test effect ty, multiple instances
  , parserTest "1 X" parseInterfaceInstance ("1", [TyArgVal (VTy"X")])

  , parserTest "1 [0]" parseInterfaceInstance ("1", [
    TyArgAbility (Ability ClosedAbility mempty)
    ])

  , parserTest "1 []" parseInterfaceInstance ("1", [
    TyArgAbility (Ability OpenAbility mempty)
    ])

  , parserTest "1" parseInterfaceInstance ("1", [])

  , parserTest "0" parseAbilityBody closedAbility
  , parserTest "0|1" parseAbilityBody $
    Ability ClosedAbility (uIdMapFromList [("1", [])])
  , parserTest "e" parseAbilityBody emptyAbility
  , parserTest "e|1" parseAbilityBody $
    Ability OpenAbility (uIdMapFromList [("1", [])])

  -- TODO: parseAbility
  , parserTest "[0|1]" parseAbility $
    Ability ClosedAbility (uIdMapFromList [("1", [])])

  , parserTest "[]" parseAbility emptyAbility
  , parserTest "[0]" parseAbility closedAbility

  , parserTest "[] X" parsePeg $ Peg emptyAbility (VTy"X")
  , parserTest "[]X" parsePeg $ Peg emptyAbility (VTy"X")
  , parserTest "[] d:1 X" parsePeg $
    Peg emptyAbility (DataTy "1" [TyArgVal (VTy"X")])

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

  , parserTest "interface Iface X Y = X -> Y | Y -> X" parseInterfaceDecl $
    ("Iface", EffectInterface [("X", ValTy), ("Y", ValTy)]
      [ CommandDeclaration [VTy"X"] (VTy"Y")
      , CommandDeclaration [VTy"Y"] (VTy"X")
      ])

  , parserTest "Z!" parseApplication $ Cut (Application []) (V"Z")
  , parserTest "Z Z Z" parseApplication $
      Cut (Application [V"Z", V"Z"]) (V"Z")

  , parserTest "let Z: forall. X = W in Z" parseLet $
    let_ "Z" (polytype [] (VTy"X")) (V"W") (V"Z")

  , let defn = unlines
          [ "let on : forall X Y. {X -> {X -> []Y} -> []Y} ="
          , "    \\x f -> f x in on n (\\x -> body)"
          ]
        compDomain = [VTy"X", SuspendedTy (CompTy [VTy"X"] (Peg emptyAbility (VTy"Y")))]
        compCodomain = Peg emptyAbility (VTy"Y")
        polyVal = SuspendedTy CompTy {..}
        polyBinders = [("X", ValTy), ("Y", ValTy)]
        pty = polytype polyBinders polyVal
        expected = let_ "on" pty
          (Value $ lam ["x", "f"] (Cut (Application [V"x"]) (V"f")))
          (Cut (Application [V"n", Value $ lam ["x"] (V"body")]) (V"on"))
    in parserTest defn parseLet expected

  , let defn = "on n (\\x -> body)"
        expected = Cut
          (Application [V"n", Value (lam ["x"] (V"body"))])
          (V"on")
    in parserTest defn parseTm expected

  , let defn = "\\x f -> f x"
        expected = Value (lam ["x", "f"] (Cut (Application [V"x"]) (V"f")))
    in parserTest defn parseTm expected

  , let defn = unlines
          [ "case x of"
          , "  e829515d5"
          , "    | -> y"
          , "    | a b c -> z"
          ]
        cont = case_ "e829515d5"
          [ ([], Variable "y")
          , (["a", "b", "c"], Variable "z")
          ]
        expected = Cut cont (Variable "x")
    in testGroup "case"
         [ parserTest defn parseTm expected
         , parserTest defn parseCase expected
         ]

  , let defn = "data Maybe x = x |"
          -- "data Maybe x = Just x | Nothing"
        expected = ("Maybe", DataTypeInterface [("x", ValTy)]
          [ ConstructorDecl [VariableTy "x"]
          , ConstructorDecl []
          ])
    in parserTest defn parseDataDecl expected

  , let defn = "interface IFace = foo -> bar | baz"
        expected = ("IFace", EffectInterface []
          [ CommandDeclaration [VariableTy "foo"] (VariableTy "bar")
          , CommandDeclaration [] (VariableTy "baz")
          ])
    in parserTest defn parseInterfaceDecl expected

  , let defn = unlines
          [ "handle (i + Receive X) ([e | Abort] Y) y! with"
          , "  receive:"
          , "    | -> r -> abort!"
          , "  | y    -> y"
          ]
        target = Cut (Application []) (V"y")
        adj = Adjustment (uIdMapFromList
          [ ("i", [])
          , ("Receive", [TyArgVal (VariableTy"X")])
          ])
        peg = Peg (Ability OpenAbility (uIdMapFromList [("Abort", [])])) (VariableTy "Y")
        handlers =
          [ ("receive", [([], "r", Cut (Application []) (V"abort"))])
          ]
        fallthrough = ("y", V"y")
        cont = handle adj peg (uIdMapFromList handlers) fallthrough
        expected = Cut {cont, target}
    in parserTest defn parseHandle expected

  -- TODO:
  -- * parseLetRec
  -- * parseValue

  -- , let defn = unlines
  --         [ "catch : <Abort>X -> {X} -> X"
  --         , "  = \\x -> "
  --         -- , "x               _ = x"
  --         -- , "<aborting -> _> h = h!"
  --         ]
  --   in parserTest defn
  ]

runParserTests :: IO ()
runParserTests = defaultMain unitTests
