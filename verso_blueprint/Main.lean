import VersoManual
import VersoBlueprint.PreviewManifest
import LMLBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual Verso.Output.Html


def extraHead : Array Verso.Output.Html := #[
  {{<link rel="icon" type="image/x-icon" href="static/favicon.svg"/>}},
  {{<link rel="stylesheet" href="static/style.css"/>}},
]

def config : RenderConfig := {
  extraHead := extraHead,
  sourceLink := some "https://github.com/anhhuyalex/LML",
  issueLink := some "https://github.com/anhhuyalex/LML/issues",
}

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.manualMainWithSharedPreviewManifest
    (%doc LMLBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
    (config := config)
