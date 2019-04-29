module Core.Options

import Core.Core
import Core.Name
import Core.TTC
import Utils.Binary

public export
record LazyNames where
  constructor MkLazy
  active : Bool
  delayType : Name
  delay : Name
  force : Name
  infinite : Name

public export
record PairNames where
  constructor MkPairNs
  pairType : Name
  fstName : Name
  sndName : Name

public export
record RewriteNames where
  constructor MkRewriteNs
  equalType : Name
  rewriteName : Name

public export
record PrimNames where
  constructor MkPrimNs
  fromIntegerName : Maybe Name
  fromStringName : Maybe Name
  fromCharName : Maybe Name

public export
data LangExt = Borrowing

export
Eq LangExt where
  Borrowing == Borrowing = True

export
TTC annot LazyNames where
  toBuf b l
      = do toBuf b (delayType l)
           toBuf b (delay l)
           toBuf b (force l)
           toBuf b (infinite l)
  fromBuf s b
      = do ty <- fromBuf s b
           d <- fromBuf s b
           f <- fromBuf s b
           i <- fromBuf s b
           pure (MkLazy True ty d f i)

export
TTC annot PairNames where
  toBuf b l
      = do toBuf b (pairType l)
           toBuf b (fstName l)
           toBuf b (sndName l)
  fromBuf s b
      = do ty <- fromBuf s b
           d <- fromBuf s b
           f <- fromBuf s b
           pure (MkPairNs ty d f)

export
TTC annot RewriteNames where
  toBuf b l
      = do toBuf b (equalType l)
           toBuf b (rewriteName l)
  fromBuf s b
      = do ty <- fromBuf s b
           l <- fromBuf s b
           pure (MkRewriteNs ty l)

export
TTC annot PrimNames where
  toBuf b l
      = do toBuf b (fromIntegerName l)
           toBuf b (fromStringName l)
           toBuf b (fromCharName l)
  fromBuf s b
      = do i <- fromBuf s b
           str <- fromBuf s b
           c <- fromBuf s b
           pure (MkPrimNs i str c)

export
TTC annot LangExt where
  toBuf b Borrowing = tag 0

  fromBuf s b
      = case !getTag of
             0 => pure Borrowing
             _ => corrupt "LangExt"

public export
record Dirs where
  constructor MkDirs
  working_dir : String
  build_dir : String -- build directory, relative to working directory
  dir_prefix : String -- installation prefix, for finding data files (e.g. run time support)
  extra_dirs : List String -- places to look for import files
  data_dirs : List String -- places to look for data file

public export
toString : Dirs -> String
toString (MkDirs wdir bdir dfix edirs ddirs) =
  unlines [ "+ Working Directory   :: " ++ show wdir
          , "+ Build Directory     :: " ++ show bdir
          , "+ Installation Prefix :: " ++ show dfix
          , "+ Extra Directories :: " ++ show edirs
          , "+ Data Directories :: " ++ show ddirs]

public export
record PPrinter where
  constructor MkPPOpts
  showImplicits : Bool
  showFullEnv : Bool
  fullNamespace : Bool

public export
data CG = Chez
        | Chicken
        | Racket
        | LispWorks

export
Eq CG where
  Chez == Chez = True
  Chicken == Chicken = True
  Racket == Racket = True
  LispWorks == LispWorks = True
  _ == _ = False

export
TTC annot CG where
  toBuf b Chez = tag 0
  toBuf b Chicken = tag 1
  toBuf b Racket = tag 2
  toBuf b LispWorks = tag 3

  fromBuf s b
      = case !getTag of
             0 => pure Chez
             1 => pure Chicken
             2 => pure Racket
             3 => pure LispWorks
             _ => corrupt "CG"

export
availableCGs : List (String, CG)
availableCGs = [("chez", Chez), ("chicken", Chicken), ("racket", Racket), ("lispworks", LispWorks)]

export
getCG : String -> Maybe CG
getCG cg = lookup (toLower cg) availableCGs

-- Other options relevant to the current session (so not to be saved in a TTC)
public export
record Session where
  constructor MkSessionOpts
  noprelude : Bool
  codegen : CG

-- NOTE: If adding options, remember to save any relevant ones in the TTC
-- implementation for Defs in Context.idr
public export
record Options where
  constructor MkOptions
  dirs : Dirs
  printing : PPrinter
  session : Session
  laziness : Maybe LazyNames
  pairnames : Maybe PairNames
  rewritenames : Maybe RewriteNames
  primnames : PrimNames
  namedirectives : List (Name, List String)
  extensions : List LangExt

defaultDirs : Dirs
defaultDirs = MkDirs "." "build" "/usr/local" ["."] []

defaultPPrint : PPrinter
defaultPPrint = MkPPOpts False True False

defaultSession : Session
defaultSession = MkSessionOpts False Chez

export
defaults : Options
defaults = MkOptions defaultDirs defaultPPrint defaultSession
                     Nothing Nothing Nothing
                     (MkPrimNs Nothing Nothing Nothing)
                     [] []

-- Reset the options which are set by source files
export
clearNames : Options -> Options
clearNames = record { laziness = Nothing,
                      pairnames = Nothing,
                      rewritenames = Nothing,
                      primnames = MkPrimNs Nothing Nothing Nothing,
                      namedirectives = []
                    }

-- Some relevant options get stored in TTC; merge in the options from
-- a TTC file
export
mergeOptions : (ttcopts : Options) -> Options -> Options
mergeOptions ttcopts opts
  = record { laziness = laziness ttcopts <+> laziness opts,
             pairnames = pairnames ttcopts <+> pairnames opts,
             rewritenames = rewritenames ttcopts <+> rewritenames opts,
             primnames = mergePrims (primnames ttcopts) (primnames opts),
             namedirectives = namedirectives ttcopts ++ namedirectives opts
           } opts
  where
    mergePrims : PrimNames -> PrimNames -> PrimNames
    mergePrims (MkPrimNs i s c) (MkPrimNs i' s' c')
        = MkPrimNs (i <+> i') (s <+> s') (c <+> c')

export
setLazy : (delayType : Name) -> (delay : Name) -> (force : Name) ->
          (infinite : Name) -> Options -> Options
setLazy ty d f i = record { laziness = Just (MkLazy True ty d f i) }

export
setPair : (pairType : Name) -> (fstn : Name) -> (sndn : Name) ->
          Options -> Options
setPair ty f s = record { pairnames = Just (MkPairNs ty f s) }

export
setRewrite : (eq : Name) -> (rwlemma : Name) -> Options -> Options
setRewrite eq rw = record { rewritenames = Just (MkRewriteNs eq rw) }

export
setFromInteger : Name -> Options -> Options
setFromInteger n = record { primnames->fromIntegerName = Just n }

export
setFromString : Name -> Options -> Options
setFromString n = record { primnames->fromStringName = Just n }

export
setFromChar : Name -> Options -> Options
setFromChar n = record { primnames->fromCharName = Just n }

export
addNameDirective : (Name, List String) -> Options -> Options
addNameDirective nd = record { namedirectives $= (nd ::) }

export
setExtension : LangExt -> Options -> Options
setExtension e = record { extensions $= (e ::) }

export
isExtension : LangExt -> Options -> Bool
isExtension e opts = e `elem` extensions opts
