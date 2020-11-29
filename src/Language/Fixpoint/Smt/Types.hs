{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE UndecidableInstances      #-}

-- | This module contains the types defining an SMTLIB2 interface.

module Language.Fixpoint.Smt.Types (

    -- * Serialized Representation
    --    symbolBuilder

    -- * Commands
      Command  (..)

    -- * Responses
    , Response (..)

    -- * Typeclass for SMTLIB2 conversion
    , SMTLIB2 (..)
    , runSmt2

    -- * SMTLIB2 Process Context
    , Context (..)

    ) where

import           Language.Fixpoint.Types
import qualified Data.Text                as T
import qualified Data.Text.Lazy.Builder   as LT
import           Text.PrettyPrint.HughesPJ

import           System.IO                (Handle)
import           System.Process
-- import           Language.Fixpoint.Misc   (traceShow)

--------------------------------------------------------------------------------
-- | Types ---------------------------------------------------------------------
--------------------------------------------------------------------------------

-- symbolBuilder :: Symbol -> LT.Builder
-- symbolBuilder = LT.fromText . symbolSafeText

-- | Commands issued to SMT engine
data Command      = Push
                  | Pop
                  | CheckSat
                  | DeclData ![DataDecl]
                  | Declare  !Symbol [SmtSort] !SmtSort
                  | Define   !Sort
                  | Assert   !(Maybe Int) !Expr
                  | AssertAx !(Triggered Expr)
                  | Distinct [Expr] -- {v:[Expr] | 2 <= len v}
                  | GetValue [Symbol]
                  | CMany    [Command]
                  | GetUnsatCore
                  deriving (Eq, Show)

instance PPrint Command where
  pprintTidy _ = ppCmd

ppCmd :: Command -> Doc
ppCmd Push             = text "Push"
ppCmd Pop              = text "Pop"
ppCmd CheckSat         = text "CheckSat"
ppCmd (DeclData d)     = text "Data" <+> pprint d
ppCmd (Declare x [] t) = text "Declare" <+> pprint x <+> text ":" <+> pprint t
ppCmd (Declare x ts t) = text "Declare" <+> pprint x <+> text ":" <+> parens (pprint ts) <+> pprint t 
ppCmd (Define {})   = text "Define ..."
ppCmd (Assert _ e)  = text "Assert" <+> pprint e
ppCmd (AssertAx _)  = text "AssertAxiom ..."
ppCmd (Distinct {}) = text "Distinct ..."
ppCmd (GetValue {}) = text "GetValue ..."
ppCmd (CMany {})    = text "CMany ..."
ppCmd GetUnsatCore  = text "GetUnsatCore"

-- | Responses received from SMT engine
data Response     = Ok
                  | Sat
                  | Unsat
                  | Unknown
                  | Values [(Symbol, T.Text)]
                  | Asserts [Symbol]
                  | Error !T.Text
                  deriving (Eq, Show)

-- | Information about the external SMT process
data Context = Ctx
  { ctxPid     :: !ProcessHandle
  , ctxCin     :: !Handle
  , ctxCout    :: !Handle
  , ctxLog     :: !(Maybe Handle)
  , ctxVerbose :: !Bool
  , ctxSymEnv  :: !SymEnv
  }

--------------------------------------------------------------------------------
-- | AST Conversion: Types that can be serialized ------------------------------
--------------------------------------------------------------------------------

class SMTLIB2 a where
  smt2 :: SymEnv -> a -> LT.Builder

runSmt2 :: (SMTLIB2 a) => SymEnv -> a -> LT.Builder
runSmt2 = smt2
