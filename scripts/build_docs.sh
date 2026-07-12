set -x -e

# Build the main library and the tutorial library. The tutorial library must be
# built here (rather than via `defaultTargets`, which would pull it into the lint
# scope) so that its aggregator olean exists for `lake exe checkdecls`, which the
# docgen-action runs later and which imports the root module of every lean_lib.
lake build LeanMachineLearning LMLTutorial

# Build tutorial
lake exe tutorial --output LMLTutorial/_out/site
mkdir -p LMLTutorial/_out/site/html-multi/static
cp LMLTutorial/static_files/* LMLTutorial/_out/site/html-multi/static

# Copy outputs to home_page
mkdir -p home_page/tutorial
cp -r LMLTutorial/_out/site/html-multi/* home_page/tutorial
