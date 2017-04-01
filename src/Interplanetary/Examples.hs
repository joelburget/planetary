{-# language OverloadedLists #-}
module Interplanetary.Examples where

-- import qualified Data.IntMap as IntMap

-- import Interplanetary.Syntax

-- -- de bruijn:  2 1 0     1           1     2 0      2 0
-- -- on : forall e X Y. <i>X -> <i>{<i>X -> [e]Y} -> [e]Y
-- -- on : forall e X Y.    X ->    {   X -> [e]Y} -> [e]Y
-- onTy :: ValTy
-- onTy =
--   let x = VariableTy 1
--       y = VariableTy 0
--       eY = Peg emptyAbility y
--   in SuspendedTy (CompTy [x, SuspendedTy (CompTy [x] eY)] eY)

-- on :: Construction'
-- on =
--   let x = Variable 1
--       f = Variable 0
--   in Lambda 2 (ConstructUse (Application f [ConstructUse x]))

-- -- define:
-- -- send
-- -- unit
-- -- receive
-- -- abort

-- zeroUid, unitUid :: Uid
-- zeroUid = 0
-- unitUid = 1

-- zeroTy :: ValTy
-- zeroTy = DataTy zeroUid []

-- unitTy :: ValTy
-- unitTy = DataTy unitUid []

-- unitVal :: Construction'
-- unitVal = Construct unitUid 0 []

-- dataTypeTable :: DataTypeTable
-- dataTypeTable = IntMap.fromList
--   -- data Zero =
--   [ (zeroUid, [])

--   -- data Unit = unit
--   , (unitUid, [[]])
--   ]

-- sendId, receiveId, abortId :: Uid
-- sendId = 0
-- receiveId = 1
-- abortId = 2

-- interfaceTypeTable :: InterfaceTable
-- interfaceTypeTable =
--   let x = 0
--   in IntMap.fromList
--     -- Send X = send : X -> Unit
--     [ (sendId, EffectInterface [ValTy] [CommandDeclaration [VariableTy x] unitTy])

--     -- Receive X = receive : X
--     , (receiveId, EffectInterface [ValTy] [CommandDeclaration [] (VariableTy x)])

--     -- Abort = aborting : Zero
--     , (abortId, EffectInterface [ValTy] [CommandDeclaration [] (DataTy zeroUid [])])
--     ]

-- runCheckMBasic :: CheckM a -> Either CheckFailure a
-- runCheckMBasic action = runCheckM action (dataTypeTable, interfaceTypeTable)

-- -- core frank representation of the pipe multihandler
-- pipe :: Construction' -> Construction'
-- pipe body =
--   let xTy = VariableTy 1
--       yTy = VariableTy 0
--       x = Variable 1
--       y = Variable 0
--       pipeTy =
--         let valTy = SuspendedTy (CompTy [] (todo "pipeTy"))
--         -- written backwards because we're working at the head
--         --                 Y        X        eps
--         -- in Polytype [TyVar 0, TyVar 1, EffVar 2] valTy
--         in Polytype [ValTy, ValTy, EffTy] valTy
--       pipeDefn =
--         let sendAdj = Adjustment (IntMap.fromList [(sendId, [TyArgVal xTy])])
--             receiveAdj = Adjustment (IntMap.fromList [(receiveId, [TyArgVal yTy])])
--             scrutinee = x
--             sendHandler = todo "sendHandler"
--             handlers = AdjustmentHandlers (IntMap.fromList [
--               (0, [sendHandler])
--               ])
--             fallback =
--               let receiveHandler = todo "receiveHandler"
--                   handlers = AdjustmentHandlers (IntMap.fromList [
--                     (0, [receiveHandler])
--                     ])
--                   handleUnit = todo "handle" -- Handle y
--               in todo "case" -- Case x [handleUnit]
--         in Lambda 2 (Handle sendAdj scrutinee handlers fallback)
--   in Letrec [(pipeDefn, pipeTy)] body
