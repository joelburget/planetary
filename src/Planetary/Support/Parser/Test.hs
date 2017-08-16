{-# language NamedFieldPuns #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language PatternSynonyms #-}
{-# language TypeFamilies #-}
module Planetary.Support.Parser.Test (unitTests) where

import Data.Text (Text)
import qualified Data.Text as T
import EasyTest
import Text.Trifecta hiding (expected)
import "indentation-trifecta" Text.Trifecta.Indentation

import Planetary.Core
import Planetary.Support.Parser

-- "(\\x -> x : Unit -> [e]Unit)"
-- "(\\x -> x : Unit -> [o]Unit)"
-- "unit : Unit"

parserTest
  :: Eq a
  => Text
  -> CoreParser Token Parser a
  -> a
  -> Test ()
parserTest input parser expected = scope input $
  case runTokenParse parser testLocation input of
    Right actual -> expect $ expected == actual
    Left errMsg -> fail errMsg

data NestedList = NamedList Text [NestedList]
  deriving (Eq, Show)

unitTests :: Test ()
unitTests = scope "parsing" $ tests
  [ let defn = T.unlines
          [ "outer:"
          , "  node1:"
          , "    node2:"
          , "  node3:"
          ]
        expected = NamedList "outer"
                     [ NamedList "node1"
                       [ NamedList "node2" [] ]
                     , NamedList "node3" []
                     ]

        parseNested = NamedList
          <$> identifier <* colon
          <*> localIndentation Gt (many (absoluteIndentation parseNested))
    in parserTest defn parseNested expected

  , parserTest "X" identifier "X"

  , parserTest "X" parseValTy (VTy"X")

  , parserTest "<_ X> | <_ X Y>" (parseConstructor [] `sepBy` bar)
    [ ConstructorDecl "_" [VTy"X"] []
    , ConstructorDecl "_" [VTy"X", VTy"Y"] []
    ]

  , parserTest "X" parseTyArg $ TyArgVal (VTy"X")

  , parserTest "X X X" (many parseTyArg) $
      let x = TyArgVal (VTy"X") in [x, x, x]

  , parserTest "1" parseUid "1"

  , parserTest "123" parseUid "123"

  , parserTest "<1 X>" parseDataTy $
    DataTy (FreeVariableTy "1") [TyArgVal (VTy"X")]

  -- also test with args
  -- Bool
  , parserTest "data Bool =\n  | <true>\n  | <false> " parseDataDecl
    (DataDecl "Bool" $ DataTypeInterface []
      [ ConstructorDecl "true" [] []
      , ConstructorDecl "false" [] []
      ])

  -- TODO: also test with effect parameter
  , let ctrResult = [TyArgVal (FreeVariableTy "X"), TyArgVal (FreeVariableTy "Y")]
    in parserTest "data Either X Y =\n  | <left X>\n  | <right Y>" parseDataDecl
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
    Ability ClosedAbility [("1", [])]
  , parserTest "e" parseAbilityBody emptyAbility
  , parserTest "e,<1>" parseAbilityBody $
    Ability OpenAbility [("1", [])]

  -- TODO: parseAbility
  , parserTest "[0,<1>]" parseAbility $
    Ability ClosedAbility [("1", [])]

  , parserTest "[]" parseAbility emptyAbility
  , parserTest "[0]" parseAbility closedAbility

  , parserTest "[] X" parsePeg $ Peg emptyAbility (VTy"X")
  , parserTest "[]X" parsePeg $ Peg emptyAbility (VTy"X")
  , parserTest "[] <1 X>" parsePeg $
    Peg emptyAbility (DataTy (FreeVariableTy "1") [TyArgVal (VTy"X")])

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
  -- , parserTest "(X Y)" parseValTy (DataTy "X" (VTy"X"))

  , parserTest "| foo : X -> X" parseCommandDecl $
    CommandDeclaration "foo" [VTy"X"] (VTy"X")

  , let decl = T.unlines
          [ "interface Iface X Y ="
          , "  | foo : X -> Y"
          , "  | bar : Y -> X"
          ]
        expected =
          InterfaceDecl "Iface" (EffectInterface [("X", ValTyK), ("Y", ValTyK)]
            [ CommandDeclaration "foo" [VTy"X"] (VTy"Y")
            , CommandDeclaration "bar" [VTy"Y"] (VTy"X")
            ])
    in parserTest decl parseInterfaceDecl expected

  , parserTest "Z!" parseTm $ AppT (FV"Z") []
  , parserTest "Z Z Z" parseTm $
      AppT (FV"Z") [FV"Z", FV"Z"]

  , parserTest "let Z: forall. X = W in Z" parseLet $
    Let (FV"W") (Polytype [] (VTy"X")) "Z" (FV"Z")
    -- let_ "Z" (Polytype [] (VTy"X")) (FV"W") (FV"Z")

  , let defn = T.unlines
          [ "let on : forall X Y. {X -> {X -> []Y} -> []Y} ="
          , "    \\x f -> f x in on n (\\x -> body)"
          ]
        compDomain = [VTy"X", SuspendedTy (CompTy [VTy"X"] (Peg emptyAbility (VTy"Y")))]
        compCodomain = Peg emptyAbility (VTy"Y")
        polyVal = SuspendedTy (CompTy compDomain compCodomain)
        polyBinders = [("X", ValTyK), ("Y", ValTyK)]
        pty = Polytype polyBinders polyVal
        expected = Let
          (Lam ["x", "f"] (AppT (FV"f") [FV"x"]))
          pty "on"
          (AppT (FV"on") [FV"n", Lam ["x"] (FV"body")])
    in parserTest defn parseLet expected

  , let defn = "on n (\\x -> body)"
        expected = AppT (FV"on") [FV"n", Lam ["x"] (FV"body")]

    in parserTest defn parseTm expected

  , let defn = "\\x f -> f x"
        expected = Lam ["x", "f"] (AppT (FV"f") [FV"x"])
    in parserTest defn parseTm expected

  , let defn = T.unlines
          [ "case x of"
          , "  e829515d5:"
          , "    | <_> -> y"
          , "    | <_ a b c> -> z"
          ]
        expected = CaseP "e829515d5" (FV "x")
          [ ([], FV "y")
          , (["a", "b", "c"], FV "z")
          ]
    in scope "case" $ tests
         [ parserTest defn parseTm expected
         , parserTest defn parseCase expected
         ]

  -- "data Maybe x = Just x | Nothing"
  , let defn = "data Maybe x =\n  | <just x>\n  | <nothing>"


        ctrResult = [TyArgVal (FreeVariableTy "x")]
        expected = DataDecl "Maybe" (DataTypeInterface [("x", ValTyK)]
          [ ConstructorDecl "just" [FreeVariableTy "x"] ctrResult
          , ConstructorDecl "nothing" [] ctrResult
          ])
    in parserTest defn parseDataDecl expected

  , let defn = "interface IFace =\n  | _ : foo -> bar\n  | _ : baz"
        expected = InterfaceDecl "IFace" (EffectInterface []
          [ CommandDeclaration "_" [FreeVariableTy "foo"] (FreeVariableTy "bar")
          , CommandDeclaration "_" [] (FreeVariableTy "baz")
          ])
    in parserTest defn parseInterfaceDecl expected

  , let defn = T.unlines
          [ "handle y! : [e , <Abort>] Y with"
          , "  Receive X:"
          , "    | <receive -> r> -> abort!"
          , "  | y -> y"
          ]
        scrutinee = AppT (FV"y") []
        adj = Adjustment
          [ ("Receive", [TyArgVal (FreeVariableTy"X")])
          ]
        peg = Peg (Ability OpenAbility [("Abort", [])])
                  (FreeVariableTy "Y")
        handlers =
          [ ("Receive", [([], "r", AppT (FV"abort") [])])
          ]
        fallthrough = ("y", FV"y")
        expected = handle scrutinee adj peg (fromList handlers) fallthrough
    in parserTest defn parseHandle expected

  , parserTest "X" parseTyVar ("X", ValTyK)
  , parserTest "[e]" parseTyVar ("e", EffTyK)

  , parserTest "\\xs -> xs" parseLambda (Lam ["xs"] (FV"xs"))
  , parserTest "\\ -> xs"   parseLambda (Lam [] (FV"xs"))
  , parserTest "\\-> xs"    parseLambda (Lam [] (FV"xs"))

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
