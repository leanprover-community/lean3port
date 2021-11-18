import Lake
open Lake DSL System

def tag : String := "nightly-2021-11-17"
def releaseRepo : String := "leanprover-community/mathport"
def oleanTarName : String := "lean3-binport.tar.gz"
def leanTarName : String := "lean3-synport.tar.gz"

-- Should be two tasks, one for oleans, one for leans. See https://github.com/leanprover/lake/issues/30
def fetchStuff (dir : FilePath) : OpaqueTarget := { info := (), task := fetch } where
  fetch := async do
    IO.FS.createDirAll libDir
    let oldTrace := Hash.ofString (← Git.headRevision dir)
    let trace ← buildFileUnlessUpToDate (libDir / oleanTarName) oldTrace do
      downloadOleans
      untarOleans
    IO.FS.createDirAll srcDir
    buildFileUnlessUpToDate (srcDir / leanTarName) trace do
      downloadLeans
      untarLeans

  downloadOleans : BuildM PUnit := Lake.proc {
      cmd := "wget",
      args := #[s!"https://github.com/{releaseRepo}/releases/download/{tag}/{oleanTarName}"]
      cwd := libDir.toString
    }

  untarOleans : BuildM PUnit := Lake.proc {
      cmd := "tar",
      args := #["-xzvf", oleanTarName]
      cwd := libDir.toString
    }

  libDir : FilePath := dir / "build" / "lib"

  downloadLeans : BuildM PUnit := Lake.proc {
      cmd := "wget",
      args := #[s!"https://github.com/{releaseRepo}/releases/download/{tag}/{leanTarName}"]
      cwd := srcDir.toString
    }

  untarLeans : BuildM PUnit := Lake.proc {
      cmd := "tar",
      args := #["-xzvf", leanTarName]
      cwd := srcDir.toString
    }

  srcDir : FilePath := dir

package lean3port (dir) {
  libRoots := #[]
  libGlobs := #[`Leanbin]
  extraDepTarget := fetchStuff dir
  defaultFacet := PackageFacet.oleans
  dependencies := #[{
    name := "mathlib",
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "64f9c43eb9a75fb4c5989ac711623d06e9696e60"
  }]
}
