import Lake
open Lake DSL System

def tag : String := "nightly-2024-06-14-08"
def releaseRepo : String := "leanprover-community/mathport"
def oleanTarName : String := "lean3-binport.tar.gz"

def untar (file : FilePath) : JobM PUnit := Lake.proc
  { cmd := "tar",
    args := #["-xzf", file.fileName.getD "."] -- really should throw an error if `file.fileName = none`
    cwd := file.parent }

def getReleaseArtifact (repo tag artifact : String) (to : FilePath) : JobM PUnit :=
  download s!"https://github.com/{repo}/releases/download/{tag}/{artifact}" to

def untarReleaseArtifact (repo tag artifact : String) (to : FilePath) : JobM PUnit := do
  getReleaseArtifact repo tag artifact to
  untar (to / artifact)

package lean3port where
  extraDepTargets := #[`fetchOleans]

target fetchOleans (_pkg) : Unit := Job.async do
  let libDir : FilePath := __dir__ / ".lake" / "build" / "lib"
  IO.FS.createDirAll libDir
  let oldTrace := Hash.ofString tag
  let _ ← buildFileUnlessUpToDate (libDir / oleanTarName) oldTrace do
    logInfo "Fetching oleans for Leanbin"
    untarReleaseArtifact releaseRepo tag oleanTarName libDir
  return ((), .nil)

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"06caa19e4a06959ae9a661b3a6e6234ade055376"

@[default_target]
lean_lib Leanbin where
  roots := #[]
  globs := #[`Leanbin]
