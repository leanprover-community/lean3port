import Lake
open Lake DSL System

def tag : String := "nightly-2023-08-25-13"
def releaseRepo : String := "leanprover-community/mathport"
def oleanTarName : String := "lean3-binport.tar.gz"

def download (url : String) (to : FilePath) : BuildM PUnit := Lake.proc
{ -- We use `curl -O` to ensure we clobber any existing file.
  cmd := "curl",
  args := #["-L", "-O", url]
  cwd := to }

def untar (file : FilePath) : BuildM PUnit := Lake.proc
{ cmd := "tar",
  args := #["-xzf", file.fileName.getD "."] -- really should throw an error if `file.fileName = none`
  cwd := file.parent }

def getReleaseArtifact (repo tag artifact : String) (to : FilePath) : BuildM PUnit :=
download s!"https://github.com/{repo}/releases/download/{tag}/{artifact}" to

def untarReleaseArtifact (repo tag artifact : String) (to : FilePath) : BuildM PUnit := do
  getReleaseArtifact repo tag artifact to
  untar (to / artifact)

package lean3port where
  extraDepTargets := #[`fetchOleans]

target fetchOleans (_pkg) : Unit := do
  let libDir : FilePath := __dir__ / "build" / "lib"
  IO.FS.createDirAll libDir
  let oldTrace := Hash.ofString tag
  let _ ← buildFileUnlessUpToDate (libDir / oleanTarName) oldTrace do
    logInfo "Fetching oleans for Leanbin"
    untarReleaseArtifact releaseRepo tag oleanTarName libDir
  return .nil

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"891adb329938ca3cd49a1d1208f691a98fb0896f"

@[default_target]
lean_lib Leanbin where
  roots := #[]
  globs := #[`Leanbin]
