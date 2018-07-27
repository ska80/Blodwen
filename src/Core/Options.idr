module Core.Options

import Core.Core
import Core.Name
import Core.TTC
import Utils.Binary

public export
record LazyNames where
  constructor MkLazy
  delayType : Name
  delay : Name
  force : Name

public export
record PairNames where
  constructor MkPairNs
  pairType : Name
  fstName : Name
  sndName : Name

export
TTC annot LazyNames where
  toBuf b l
      = do toBuf b (delayType l)
           toBuf b (delay l)
           toBuf b (force l)
  fromBuf s b
      = do ty <- fromBuf s b
           d <- fromBuf s b
           f <- fromBuf s b
           pure (MkLazy ty d f)

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

public export
record Dirs where
  constructor MkDirs
  build_dir : String -- build directory, relative to working directory
  dir_prefix : String -- installation prefix, for finding data files (e.g. run time support)
  extra_dirs : List String -- places to look for import files

public export
record PPrinter where
  constructor MkPPOpts
  showImplicits : Bool

-- Other options relevant to the current session (so not to be saved in a TTC)
public export
record Session where
  constructor MkSessionOpts
  quiet : Bool
  noprelude : Bool

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

defaultDirs : Dirs
defaultDirs = MkDirs "build" "/usr/local" ["."]

defaultPPrint : PPrinter
defaultPPrint = MkPPOpts False

defaultSession : Session
defaultSession = MkSessionOpts False False

export
defaults : Options
defaults = MkOptions defaultDirs defaultPPrint defaultSession Nothing Nothing

-- Some relevant options get stored in TTC; merge in the options from
-- a TTC file
export
mergeOptions : (ttcopts : Options) -> Options -> Options
mergeOptions ttcopts opts
  = record { laziness = laziness ttcopts <+> laziness opts,
             pairnames = pairnames ttcopts <+> pairnames opts } opts

export
setLazy : (delayType : Name) -> (delay : Name) -> (force : Name) ->
          Options -> Options
setLazy ty d f = record { laziness = Just (MkLazy ty d f) }

export
setPair : (pairType : Name) -> (fstn : Name) -> (sndn : Name) ->
          Options -> Options
setPair ty f s = record { pairnames = Just (MkPairNs ty f s) }
