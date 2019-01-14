module Compiler.CommonLisp.Common

import Compiler.Common
import Compiler.CompileExpr
import Compiler.Inline

import Core.Context
import Core.Name
import Core.TT

import Data.List
import Data.Vect

%default covering

lspString : String -> String
lspString s = concatMap okchar (unpack s)
  where
    okchar : Char -> String
    okchar c = if isAlphaNum c || c =='_'
                  then cast c
                  else "C-" ++ show (cast {to=Int} c)

mutual
  lspName : Name -> String
  lspName (UN n) = lspString n
  lspName (MN n i) = lspString n ++ "-" ++ show i
  lspName (NS ns n) = showSep "-" ns ++ "-" ++ lspName n
  lspName (HN n i) = lspString n ++ "--" ++ show i
  lspName (PV n d) = "pat--" ++ lspName n
  lspName (DN _ n) = lspName n
  lspName (GN g) = lspGName g

  lspGName : GenName -> String
  lspGName (Nested o i) = lspName i ++ "--in--" ++ lspName o
  lspGName (CaseBlock n i) = "case--" ++ lspName n ++ "-" ++ show i
  lspGName (WithBlock n i) = "with--" ++ lspName n ++ "-" ++ show i

-- local variable names as CL names - we need to invent new names for the locals
-- because there might be shadows in the original expression which can't be resolved
-- by the same scoping rules. (e.g. something that computes \x, x => x + x where the
-- names are the same but refer to different bindings in the scope)
public export
data SVars : List Name -> Type where
     Nil : SVars []
     (::) : (svar : String) -> SVars ns -> SVars (n :: ns)

extendSVars : (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
extendSVars {ns} xs vs = extSVars' (cast (length ns)) xs vs
  where
    extSVars' : Int -> (xs : List Name) -> SVars ns -> SVars (xs ++ ns)
    extSVars' i [] vs = vs
    extSVars' i (x :: xs) vs = lspName (MN "v" i) :: extSVars' (i + 1) xs vs

initSVars : (xs : List Name) -> SVars xs
initSVars xs = rewrite sym (appendNilRightNeutral xs) in extendSVars xs []

lookupSVar : Elem x xs -> SVars xs -> String
lookupSVar Here (n :: ns) = n
lookupSVar (There p) (n :: ns) = lookupSVar p ns

export
lspConstructor : Int -> List String -> String
lspConstructor t args = "(vector " ++ show t ++ " " ++ showSep " " args ++ ")"

op : String -> List String -> String
op o args = "(" ++ o ++ " " ++ showSep " " args ++ ")"

boolop : String -> List String -> String
boolop o args = "(or (and " ++ op o args ++ " 1) 0)"

lspOp : PrimFn arity -> Vect arity String -> String
lspOp (Add IntType) [x, y] = op "b+" [x, y, "63"]
lspOp (Sub IntType) [x, y] = op "b-" [x, y, "63"]
lspOp (Mul IntType) [x, y] = op "b*" [x, y, "63"]
lspOp (Div IntType) [x, y] = op "b/" [x, y, "63"]
lspOp (Add ty) [x, y] = op "+" [x, y]
lspOp (Sub ty) [x, y] = op "-" [x, y]
lspOp (Mul ty) [x, y] = op "*" [x, y]
lspOp (Div ty) [x, y] = op "/" [x, y]
lspOp (Mod ty) [x, y] = op "mod" [x, y]
lspOp (Neg ty) [x] = op "-" [x]
lspOp (LT CharType) [x, y] = boolop "char<" [x, y]
lspOp (LTE CharType) [x, y] = boolop "char<=" [x, y]
lspOp (EQ CharType) [x, y] = boolop "char=" [x, y]
lspOp (GTE CharType) [x, y] = boolop "char>=" [x, y]
lspOp (GT CharType) [x, y] = boolop "char>" [x, y]
lspOp (LT ty) [x, y] = boolop "<" [x, y]
lspOp (LTE ty) [x, y] = boolop "<=" [x, y]
lspOp (EQ ty) [x, y] = boolop "=" [x, y]
lspOp (GTE ty) [x, y] = boolop ">=" [x, y]
lspOp (GT ty) [x, y] = boolop ">" [x, y]
lspOp StrLength [x] = op "length" [x]
lspOp StrHead [x] = op "char" [x, "0"]
lspOp StrTail [x] = op "subseq" [x, "1", op "length" [x]]
lspOp StrIndex [x, i] = op "char" [x, i]
lspOp StrCons [x, y] = op "blodwen-rts:string-cons" [x, y]
lspOp StrAppend [x, y] = op "blodwen-rts:string-append" [x, y]
lspOp StrReverse [x] = op "blodwen-rts:string-reverse" [x]
lspOp StrSubstr [x, y, z] = op "blodwen-rts:string-substr" [x, y, z]

lspOp (Cast IntType StringType) [x] = op "princ-to-string" [x]
lspOp (Cast IntegerType StringType) [x] = op "princ-to-string" [x]
lspOp (Cast DoubleType StringType) [x] = op "princ-to-string" [x]
lspOp (Cast CharType StringType) [x] = op "string" [x]

lspOp (Cast IntType IntegerType) [x] = x
lspOp (Cast DoubleType IntegerType) [x] = op "floor" [x]
lspOp (Cast CharType IntegerType) [x] = op "char-code" [x]
lspOp (Cast StringType IntegerType) [x] = op "blodwen-rts:cast-string-int" [x]

lspOp (Cast IntegerType IntType) [x] = x
lspOp (Cast DoubleType IntType) [x] = op "floor" [x]
lspOp (Cast StringType IntType) [x] = op "blodwen-rts:cast-string-int" [x]
lspOp (Cast CharType IntType) [x] = op "char-code" [x]

lspOp (Cast IntegerType DoubleType) [x] = op "float" [x, "1.0d0"]
lspOp (Cast IntType DoubleType) [x] = op "float" [x, "1.0d0"]
lspOp (Cast StringType DoubleType) [x] = op "blodwen-rts:cast-string-double" [x]

lspOp (Cast IntType CharType) [x] = op "code-char" [x]

lspOp (Cast from to) [x] = "(error \"Invalid cast " ++ show from ++ "->" ++ show to ++ "\")"

public export
data ExtPrim = CCall | LispCall | PutStr | GetStr
             | FileOpen | FileClose | FileReadLine | FileWriteLine | FileEOF
             | NewIORef | ReadIORef | WriteIORef
             | Unknown Name

export
Show ExtPrim where
  show CCall = "CCall"
  show LispCall = "LispCall"
  show PutStr = "PutStr"
  show GetStr = "GetStr"
  show FileOpen = "FileOpen"
  show FileClose = "FileClose"
  show FileReadLine = "FileReadLine"
  show FileWriteLine = "FileWriteLine"
  show FileEOF = "FileEOF"
  show NewIORef = "NewIORef"
  show ReadIORef = "ReadIORef"
  show WriteIORef = "WriteIORef"
  show (Unknown n) = "Unknown " ++ show n

toPrim : Name -> ExtPrim
toPrim pn@(NS _ n)
    = cond [(n == UN "prim__lispCall", LispCall),
            (n == UN "prim__cCall", CCall),
            (n == UN "prim__putStr", PutStr),
            (n == UN "prim__getStr", GetStr),
            (n == UN "prim__open", FileOpen),
            (n == UN "prim__close", FileClose),
            (n == UN "prim__readLine", FileReadLine),
            (n == UN "prim__writeLine", FileWriteLine),
            (n == UN "prim__eof", FileEOF),
            (n == UN "prim__newIORef", NewIORef),
            (n == UN "prim__readIORef", ReadIORef),
            (n == UN "prim__writeIORef", WriteIORef)
            ]
           (Unknown pn)
toPrim pn = Unknown pn

export
mkWorld : String -> String
mkWorld res = lspConstructor 0 ["NIL", res, "NIL"] -- MkIORes

lspConstant : Constant -> String
lspConstant (I x) = show x
lspConstant (BI x) = show x
lspConstant (Str x) = show x
lspConstant (Ch x) = "#\\" ++ cast x
lspConstant (Db x) = show x
lspConstant WorldVal = "NIL"
lspConstant IntType = "T"
lspConstant IntegerType = "T"
lspConstant StringType = "T"
lspConstant CharType = "T"
lspConstant DoubleType = "T"
lspConstant WorldType = "T"

lspCaseDef : Maybe String -> String
lspCaseDef Nothing = ""
lspCaseDef (Just tm) = "(otherwise " ++ tm ++ ")"

parameters (lspExtPrim : {vars : _} -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String)
  mutual
    lspConAlt : SVars vars -> String -> CConAlt vars -> Core annot String
    lspConAlt {vars} vs target (MkConAlt n tag args sc)
        = let vs' = extendSVars args vs in
              pure $ "((" ++ show tag ++ ") "
                          ++ bindArgs 1 args vs' !(lspExp vs' sc) ++ ")"
      where
        bindArgs : Int -> (ns : List Name) -> SVars (ns ++ vars) -> String -> String
        bindArgs i [] vs body = body
        bindArgs i (n :: ns) (v :: vs) body
            = "(let ((" ++ v ++ " " ++ "(svref " ++ target ++ " " ++ show i ++ "))) "
                    ++ bindArgs (i + 1) ns vs body ++ ")"

    lspConstAlt : SVars vars -> String -> CConstAlt vars -> Core annot String
    lspConstAlt vs target (MkConstAlt c exp)
        = pure $ "((equal " ++ target ++ " " ++ lspConstant c ++ ") " ++ !(lspExp vs exp) ++ ")"

    -- oops, no traverse for Vect in Core
    lspArgs : SVars vars -> Vect n (CExp vars) -> Core annot (Vect n String)
    lspArgs vs [] = pure []
    lspArgs vs (arg :: args) = pure $ !(lspExp vs arg) :: !(lspArgs vs args)

    export
    lspExp : SVars vars -> CExp vars -> Core annot String
    lspExp vs (CLocal el) = pure $ lookupSVar el vs
    lspExp vs (CRef n) = pure $ lspName n
    lspExp vs (CLam x sc)
       = do let vs' = extendSVars [x] vs
            sc' <- lspExp vs' sc
            pure $ "#'(lambda (" ++ lookupSVar Here vs' ++ ") " ++ sc' ++ ")"
    lspExp vs (CLet x val sc)
       = do let vs' = extendSVars [x] vs
            val' <- lspExp vs val
            sc' <- lspExp vs' sc
            pure $ "(let ((" ++ lookupSVar Here vs' ++ " " ++ val' ++ ")) " ++ sc' ++ ")"
    lspExp vs (CApp x [])
        = pure $ "(" ++ !(lspExp vs x) ++ ")"
    lspExp vs (CApp x args)
        = pure $ "(" ++ !(lspExp vs x) ++ " " ++ showSep " " !(traverse (lspExp vs) args) ++ ")"
    lspExp vs (CCon x tag args)
        = pure $ lspConstructor tag !(traverse (lspExp vs) args)
    lspExp vs (COp op args)
        = pure $ lspOp op !(lspArgs vs args)
    lspExp vs (CExtPrim p args)
        = lspExtPrim vs (toPrim p) args
    lspExp vs (CForce t) = pure $ "(blodwen-rts:force " ++ !(lspExp vs t) ++ ")"
    lspExp vs (CDelay t) = pure $ "(blodwen-rts:delay " ++ !(lspExp vs t) ++ ")"
    lspExp vs (CConCase sc alts def)
        = do tcode <- lspExp vs sc
             defc <- maybe (pure Nothing) (\v => pure (Just !(lspExp vs v))) def
             pure $ "(let ((sc " ++ tcode ++ ")) (case (get-tag sc) "
                     ++ showSep " " !(traverse (lspConAlt vs "sc") alts)
                     ++ lspCaseDef defc ++ "))"
    lspExp vs (CConstCase sc alts def)
        = do defc <- maybe (pure Nothing) (\v => pure (Just !(lspExp vs v))) def
             tcode <- lspExp vs sc
             pure $ "(let ((sc " ++ tcode ++ ")) (cond " -- ++ !(lspExp vs sc) ++ " "
                      ++ showSep " " !(traverse (lspConstAlt vs "sc") alts)
                      ++ lspCaseDef defc ++ "))"
    lspExp vs (CPrimVal c) = pure $ lspConstant c
    lspExp vs CErased = pure "'()"
    lspExp vs (CCrash msg) = pure $ "(error " ++ show msg ++ ")"

  -- Need to convert the argument (a list of CL arguments that may
  -- have been constructed at run time) to a CL list to be passed to apply
  readArgs : SVars vars -> CExp vars -> Core annot String
  readArgs vs tm = pure $ "(blodwen-rts:blodwen-read-args " ++ !(lspExp vs tm) ++ ")"

  fileOp : String -> String
  fileOp op = "(blodwen-rts:blodwen-file-op #'(lambda () " ++ op ++ "))"

  -- External primitives which are common to the CL codegens (they can be
  -- overridden)
  export
  lspExtCommon : SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String
  lspExtCommon vs LispCall [ret, CPrimVal (Str fn), args, world]
     = pure $ mkWorld ("(apply " ++ fn ++" "
                  ++ !(readArgs vs args) ++ ")")
  lspExtCommon vs LispCall [ret, fn, args, world]
       = pure $ mkWorld ("(apply (eval (make-symbol " ++ !(lspExp vs fn) ++")) "
                    ++ !(readArgs vs args) ++ ")")
  lspExtCommon vs PutStr [arg, world]
      = pure $ "(princ " ++ !(lspExp vs arg) ++ ") " ++ mkWorld (lspConstructor 0 []) -- code for MkUnit
  lspExtCommon vs GetStr [world]
      = pure $ mkWorld "(read-line)"
  lspExtCommon vs FileOpen [file, mode, bin, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-rts:blodwen-open-stream "
                                      ++ !(lspExp vs file) ++ " "
                                      ++ !(lspExp vs mode) ++ " "
                                      ++ !(lspExp vs bin) ++ ")"
  lspExtCommon vs FileClose [file, world]
      = pure $ "(blodwen-rts:blodwen-close-stream " ++ !(lspExp vs file) ++ ") " ++ mkWorld (lspConstructor 0 [])
  lspExtCommon vs FileReadLine [file, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-rts:blodwen-get-line " ++ !(lspExp vs file) ++ ")"
  lspExtCommon vs FileWriteLine [file, str, world]
      = pure $ mkWorld $ fileOp $ "(blodwen-rts:blodwen-putstring "
                                        ++ !(lspExp vs file) ++ " "
                                        ++ !(lspExp vs str) ++ ")"
  lspExtCommon vs FileEOF [file, world]
      = pure $ mkWorld $ "(blodwen-rts:blodwen-eof " ++ !(lspExp vs file) ++ ")"
  lspExtCommon vs NewIORef [_, val, world]
      = pure $ mkWorld $ "(blodwen-rts:box " ++ !(lspExp vs val) ++ ")"
  lspExtCommon vs ReadIORef [_, ref, world]
      = pure $ mkWorld $ "(blodwen-rts:unbox " ++ !(lspExp vs ref) ++ ")"
  lspExtCommon vs WriteIORef [_, ref, val, world]
      = pure $ mkWorld $ "(blodwen-rts:set-box "
                           ++ !(lspExp vs ref) ++ " "
                           ++ !(lspExp vs val) ++ ")"
  lspExtCommon vs (Unknown n) args
      = throw (InternalError ("Can't compile unknown external primitive " ++ show n))
  lspExtCommon vs prim args
      = throw (InternalError ("Badly formed external primitive " ++ show prim
                                ++ " " ++ show args))

  lspArglist : SVars ns -> String
  lspArglist [] = ""
  lspArglist [x] = x
  lspArglist (x :: xs) = x ++ " " ++ lspArglist xs

  lspDef : Name -> CDef -> Core annot String
  lspDef n (MkFun args exp)
     = let vs = initSVars args in
           pure $ "(defun " ++ lspName n ++ " (" ++ lspArglist vs ++ ") "
                      ++ !(lspExp vs exp) ++ ")\n"
  lspDef n (MkError exp)
     = pure $ "(define (" ++ lspName n ++ " . any-args) " ++ !(lspExp [] exp) ++ ")\n"
  lspDef n (MkCon t a) = pure "" -- Nothing to compile here

-- Convert the name to CL code
-- (There may be no code generated, for example if it's a constructor)
export
getLisp : (lspExtPrim : {vars : _} -> SVars vars -> ExtPrim -> List (CExp vars) -> Core annot String) ->
          Defs -> Name -> Core annot String
getLisp lspExtPrim defs n
    = case lookupGlobalExact n (gamma defs) of
           Nothing => throw (InternalError ("Compiling undefined name " ++ show n))
           Just d => case compexpr d of
                          Nothing =>
                             throw (InternalError ("No compiled definition for " ++ show n))
                          Just d => lspDef lspExtPrim n d
