import Lake
open Lake DSL System

def tag : String := "nightly-2022-07-18"
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

def fetchOleans : OpaqueTarget := { info := (), task := fetch } where
  fetch := async (m := BuildM) do
    IO.FS.createDirAll libDir
    let oldTrace := Hash.ofString tag
    buildFileUnlessUpToDate (libDir / oleanTarName) oldTrace do
      untarReleaseArtifact releaseRepo tag oleanTarName libDir

  libDir : FilePath := __dir__ / "build" / "lib"

package lean3port where
  extraDepTarget := Target.collectOpaqueList [fetchOleans]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"aa176e5da516f57b502ebdfb633f39b392dda333"

@[defaultTarget]
lean_lib Leanbin where
  roots := #[]
  globs := #[`Leanbin]
