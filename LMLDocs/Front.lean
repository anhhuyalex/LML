import LMLDocs.Pages.BasicProbability
import VersoManual

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option pp.rawOnError true
set_option verso.code.warnLineLength 100

open Verso.Genre Manual Verso.Genre.Manual.InlineLean Verso.Code.External

#doc (Manual) "Lean Machine Learning" =>
%%%
authors := []
shortTitle := "Lean Machine Learning"
%%%

These documentation pages are a manual prototype for definition certification pages for the [Lean Machine Learning](https://leanmachinelearning.org) library.

Some of it should be automatically generated from the code, but for now it is mostly written by hand.

{include 0 LMLDocs.Pages.BasicProbability}
