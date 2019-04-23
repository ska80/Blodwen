module Compiler.CommonLisp.LispWorks

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline
import Compiler.CommonLisp.Common

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT

import Data.CMap
import Data.List
import Data.Vect
import System
import System.Info

%default covering

firstExists : List String -> IO (Maybe String)
firstExists [] = pure Nothing
firstExists (x :: xs) = if !(exists x) then pure (Just x) else firstExists xs

lspHeader : String
lspHeader = "\n\n(in-package #:cl-user)\n\n"

mutual
  lispworksPrim : Int -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  lispworksPrim i vs CCall [ret, fn, args, world]
      = throw (InternalError ("Can't compile C FFI calls to LispWorks yet"))
  lispworksPrim i vs prim args
      = lspExtCommon lispworksPrim i vs prim args

||| Compile a Blodwen expression to LispWorks
compileToLSP : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core annot ()
compileToLSP c tm outfile
    = do ds <- getDirectives LispWorks
         (ns, tags) <- findUsedNames tm
         defs <- get Ctxt
         compdefs <- traverse (getLisp lispworksPrim defs) ns
         let code = concat compdefs
         main <- lspExp lispworksPrim 0 [] !(compileExp tags tm)
         support <- readDataFile "lispworks/support.lisp"
         let lsp = support ++ lspHeader ++ code ++ main
         Right () <- coreLift $ writeFile outfile lsp
            | Left err => throw (FileErr outfile err)
         coreLift $ chmod outfile 0o755
         pure ()

||| LispWorks implementation of the `compileExpr` interface
compileExpr : Ref Ctxt Defs ->
              ClosedTerm -> (outfile : String) -> Core annot (Maybe String)
compileExpr c tm outfile
    = do let outn = outfile ++ ".lisp"
         compileToLSP c tm outn
         pure (Just outn)

||| LispWorks implementation of the `executeExpr` interface.  This implementation simply runs the
||| usual compiler, saving it to a temp file, then interpreting it
executeExpr : Ref Ctxt Defs -> ClosedTerm -> Core annot ()
executeExpr c tm
    = do tmp <- coreLift $ tmpName
         let outn = tmp ++ ".lisp"
         compileToLSP c tm outn
         pure ()

||| Codegen wrapper for LispWorks implementation
export
codegenLispWorks : Codegen annot
codegenLispWorks = MkCG compileExpr executeExpr
