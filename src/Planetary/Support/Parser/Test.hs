{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language PatternSynonyms #-}
module Planetary.Support.Parser.Test where

import Data.Text (Text)
import qualified Data.Text as T
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
  => Text
  -> CoreParser Token Parser a
  -> a
  -> TestTree
parserTest input parser expected = testCase (T.unpack input) $
  case runTokenParse parser testLocation input of
    Right actual -> expected @=? actual
    Left errMsg -> assertFailure errMsg

unitTests :: TestTree
unitTests = testGroup "parsing"
  [ parserTest "X" identifier "X"

  , parserTest "X" parseValTy (VTy"X")

  , parserTest "<_ X> | <_ X Y>" (parseConstructors [])
    [ ConstructorDecl "_" [VTy"X"] []
    , ConstructorDecl "_" [VTy"X", VTy"Y"] []
    ]

  , parserTest "X" parseTyArg $ TyArgVal (VTy"X")

  , parserTest "X X X" (many parseTyArg) $
      let x = TyArgVal (VTy"X") in [x, x, x]

  , parserTest "1" parseUid "1"

  , parserTest "123" parseUid "123"

  , parserTest "<1 X>" parseDataTy $
    DataTy "1" [TyArgVal (VTy"X")]

  -- also test with args
  -- Bool
  , parserTest "data Bool = <true> | <false> " parseDataDecl
    (DataDecl "Bool" $ DataTypeInterface []
      [ ConstructorDecl "true" [] []
      , ConstructorDecl "false" [] []
      ])

  -- TODO: also test with effect parameter
  , let ctrResult = [TyArgVal (VariableTy "X"), TyArgVal (VariableTy "Y")]
    in parserTest "data Either X Y = <left X> | <right Y>" parseDataDecl
         (DataDecl "Either" $
           DataTypeInterface [("X", ValTyK), ("Y", ValTyK)]
             [ ConstructorDecl "left" [VTy"X"] ctrResult
             , ConstructorDecl "right" [VTy"Y"] ctrResult
             ])

  -- also test effect ty, multiple instances
  , parserTest "<1 X>" parseInterfaceInstance ("1", [TyArgVal (VTy"X")])

  , parserTest "<1 [0]>" parseInterfaceInstance ("1", [
    TyArgAbility (Ability ClosedAbility mempty)
    ])

  , parserTest "<1 []>" parseInterfaceInstance ("1", [
    TyArgAbility (Ability OpenAbility mempty)
    ])

  , parserTest "<1>" parseInterfaceInstance ("1", [])

  , parserTest "0" parseAbilityBody closedAbility
  , parserTest "0,<1>" parseAbilityBody $
    Ability ClosedAbility (uIdMapFromList [("1", [])])
  , parserTest "e" parseAbilityBody emptyAbility
  , parserTest "e,<1>" parseAbilityBody $
    Ability OpenAbility (uIdMapFromList [("1", [])])

  -- TODO: parseAbility
  , parserTest "[0,<1>]" parseAbility $
    Ability ClosedAbility (uIdMapFromList [("1", [])])

  , parserTest "[]" parseAbility emptyAbility
  , parserTest "[0]" parseAbility closedAbility

  , parserTest "[] X" parsePeg $ Peg emptyAbility (VTy"X")
  , parserTest "[]X" parsePeg $ Peg emptyAbility (VTy"X")
  , parserTest "[] <1 X>" parsePeg $
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

  , parserTest "foo : X -> X" parseCommandDecl $ CommandDeclaration [VTy"X"] (VTy"X")

  , parserTest "interface Iface X Y = foo : X -> Y | bar : Y -> X" parseInterfaceDecl
    (InterfaceDecl "Iface" (EffectInterface [("X", ValTyK), ("Y", ValTyK)]
      [ CommandDeclaration [VTy"X"] (VTy"Y")
      , CommandDeclaration [VTy"Y"] (VTy"X")
      ]))

  , parserTest "Z!" parseTm $ Cut (Application []) (V"Z")
  , parserTest "Z Z Z" parseTm $
      Cut (Application [V"Z", V"Z"]) (V"Z")

  , parserTest "let Z: forall. X = W in Z" parseLet $
    let_ "Z" (PolytypeP [] (VTy"X")) (V"W") (V"Z")

  , let defn = T.unlines
          [ "let on : forall X Y. {X -> {X -> []Y} -> []Y} ="
          , "    \\x f -> f x in on n (\\x -> body)"
          ]
        compDomain = [VTy"X", SuspendedTy (CompTy [VTy"X"] (Peg emptyAbility (VTy"Y")))]
        compCodomain = Peg emptyAbility (VTy"Y")
        polyVal = SuspendedTy (CompTy compDomain compCodomain)
        polyBinders = [("X", ValTyK), ("Y", ValTyK)]
        pty = PolytypeP polyBinders polyVal
        expected = let_ "on" pty
          (Value $ Lam ["x", "f"] (Cut (Application [V"x"]) (V"f")))
          (Cut (Application [V"n", Value $ Lam ["x"] (V"body")]) (V"on"))
    in parserTest defn parseLet expected

  , let defn = "on n (\\x -> body)"
        expected = Cut
          (Application [V"n", Value (Lam ["x"] (V"body"))])
          (V"on")
    in parserTest defn parseTm expected

  , let defn = "\\x f -> f x"
        expected = Value (Lam ["x", "f"] (Cut (Application [V"x"]) (V"f")))
    in parserTest defn parseTm expected

  , let defn = T.unlines
          [ "case x of"
          , "  e829515d5:"
          , "    | <_> -> y"
          , "    | <_ a b c> -> z"
          ]
        cont = CaseP "e829515d5"
          [ ([], Variable "y")
          , (["a", "b", "c"], Variable "z")
          ]
        expected = Cut cont (Variable "x")
    in testGroup "case"
         [ parserTest defn parseTm expected
         , parserTest defn parseCase expected
         ]

  , let defn = "data Maybe x = <just x> | <nothing>"
          -- "data Maybe x = Just x | Nothing"

        ctrResult = [TyArgVal (VariableTy "x")]
        expected = DataDecl "Maybe" (DataTypeInterface [("x", ValTyK)]
          [ ConstructorDecl "just" [VariableTy "x"] ctrResult
          , ConstructorDecl "nothing" [] ctrResult
          ])
    in parserTest defn parseDataDecl expected

  , let defn = "interface IFace = _ : foo -> bar | _ : baz"
        expected = InterfaceDecl "IFace" (EffectInterface []
          [ CommandDeclaration [VariableTy "foo"] (VariableTy "bar")
          , CommandDeclaration [] (VariableTy "baz")
          ])
    in parserTest defn parseInterfaceDecl expected

  , let defn = T.unlines
          [ "handle y! : [e , <Abort>] Y with"
          , "  Receive X:"
          , "    | <receive -> r> -> abort!"
          , "  | y -> y"
          ]
        scrutinee = Cut (Application []) (V"y")
        adj = Adjustment (uIdMapFromList
          [ ("Receive", [TyArgVal (VariableTy"X")])
          ])
        peg = Peg (Ability OpenAbility (uIdMapFromList [("Abort", [])])) (VariableTy "Y")
        handlers =
          [ ("Receive", [([], "r", Cut (Application []) (V"abort"))])
          ]
        fallthrough = ("y", V"y")
        cont = handle adj peg (uIdMapFromList handlers) fallthrough
        expected = Cut cont scrutinee
    in parserTest defn parseHandle expected

  , parserTest "X" parseTyVar ("X", ValTyK)
  , parserTest "[e]" parseTyVar ("e", EffTyK)

  -- , let defn = T.unlines
  --         [
  --         ]
  --   in parserTest defn parseLetrec expected

  -- TODO:
  -- * parseValue

  -- , let defn = T.unlines
  --         [ "catch : <Abort>X -> {X} -> X"
  --         , "  = \\x -> "
  --         -- , "x               _ = x"
  --         -- , "<aborting -> _> h = h!"
  --         ]
  --   in parserTest defn
  ]

runParserTests :: IO ()
runParserTests = defaultMain unitTests
