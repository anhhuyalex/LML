# Blueprinting
Read Chapters 1 of /jukebox/norman/qanguyen/autoform/docs/Renormalization.md and create a plan to build a new library for formalized machine learning in /jukebox/norman/qanguyen/autoform/LML/LeanMachineLearning/Optimization/Renormalization. The library should accord with the principles of the broader LML (Lean Machine Learning) project, which you can see by reading the README in the LeanMachineLearning folder at /jukebox/norman/qanguyen/autoform/LML/README.md. It should also reuse the existing infrastructure of LML if possible and propose refactors when appropriate to give the Lean code more generality, concision, and elegance.

Then add to the blueprint document /jukebox/norman/qanguyen/autoform/LML/blueprint/src/chapters/renormalization.tex as in /jukebox/norman/qanguyen/autoform/LML/blueprint/src/chapters. The blueprint should be more explicit and formal and should be used as a guide for building the library. Look at other files, e.g. /jukebox/norman/qanguyen/autoform/LML/blueprint/src/chapters/approximation.tex for how to do this.

Be rigorous and truth-seeking in your work. You will be rewarded for accuracy.               
consult    /jukebox/norman/qanguyen/autoform/docs/lessons_learned.md                         
/jukebox/norman/qanguyen/autoform/docs/useful_mathlib.md    for what to do and               
/jukebox/norman/qanguyen/autoform/docs/hallucinated_mathlib.md     for what not to do Explain
how the error violated lessons_learned.md, be specific which lessons, explain how your new   
plan totally complies with lessons_learned.md                                                
Also develop reusable API to help with proving. Ideally our proofs won't be too long but  
will build from reusable and readable lemmas. Make sure to pay attention to code quality and 
model yourself on writing code that can be merged into Mathlib. You can run tests on your    
edits with `lake env lean [filename]`. If you develop API as reusable lemmas to help you with
your proof, it's OK to leave them as a sorry *only if* you cite where we can find an informal
proof (e.g. a URL or some other link) and also provide an informal proof in your own words.  
The library should accord with the principles of the broader LML (Lean Machine Learning)     
project, which you can see by reading the README in the LeanMachineLearning folder. It should
also reuse the existing infrastructure of LML if possible and propose refactors when         
appropriate to give the Lean code more generality, concision, and elegance.                  
**Do NOT** use git to revert commits. Edit the code that you have in front of you.    
You can use this tool to check the goal at a certain line: /jukebox/norman/qanguyen/autoform/.venv/bin/python /jukebox/norman/qanguyen/autoform/agent/get_goal.py <ABSOLUTE_FILE_PATH> <LINE_NUMBER> --project-path /jukebox/norman/qanguyen/autoform/LML
For example, to test it on line 67 of the MirrorFlow.lean file:
/jukebox/norman/qanguyen/autoform/.venv/bin/python /jukebox/norman/qanguyen/autoform/agent/get_goal.py /jukebox/norman/qanguyen/autoform/LML/LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean 67 --project-path /jukebox/norman/qanguyen/autoform/LML


# Checking faithfulness of blueprinting
Read the files in /jukebox/norman/qanguyen/autoform/LML/LeanMachineLearning/Optimization/Approximation and make sure we are not missing any substantial theorems or ideas from chapters 2 and 3 of 

Deep learning theory lecture notes.md
  Write a detailed report explaining what was faithfully translated and what was not

# Once report written, add in missing parts
Add in all the parts that are missing. 
Be rigorous and truth-seeking in your work. You will be rewarded for accuracy.               
consult    /jukebox/norman/qanguyen/autoform/docs/lessons_learned.md                         
/jukebox/norman/qanguyen/autoform/docs/useful_mathlib.md    for what to do and               
/jukebox/norman/qanguyen/autoform/docs/hallucinated_mathlib.md     for what not to do Explain
how the error violated lessons_learned.md, be specific which lessons, explain how your new   
plan totally complies with lessons_learned.md                                                
Also develop reusable API to help with proving. Ideally our proofs won't be too long but  
will build from reusable and readable lemmas. Make sure to pay attention to code quality and 
model yourself on writing code that can be merged into Mathlib. You can run tests on your    
edits with `lake env lean [filename]`. If you develop API as reusable lemmas to help you with
your proof, it's OK to leave them as a sorry *only if* you cite where we can find an informal
proof (e.g. a URL or some other link) and also provide an informal proof in your own words.  
The library should accord with the principles of the broader LML (Lean Machine Learning)     
project, which you can see by reading the README in the LeanMachineLearning folder. It should
also reuse the existing infrastructure of LML if possible and propose refactors when         
appropriate to give the Lean code more generality, concision, and elegance.                  
**Do NOT** use git to revert commits. Edit the code that you have in front of you.    
Then add to the blueprint document /jukebox/norman/qanguyen/autoform/LML/blueprint/src/chapters/lasso.tex as in /jukebox/norman/qanguyen/autoform/LML/blueprint/src/chapters. The blueprint should be more explicit and formal and should be used as a guide for building the library. Look at other files, e.g. /jukebox/norman/qanguyen/autoform/LML/blueprint/src/chapters/approximation.tex for how to do this.
You can use this tool to check the goal at a certain line: /jukebox/norman/qanguyen/autoform/.venv/bin/python /jukebox/norman/qanguyen/autoform/agent/get_goal.py <ABSOLUTE_FILE_PATH> <LINE_NUMBER> --project-path /jukebox/norman/qanguyen/autoform/LML
For example, to test it on line 67 of the MirrorFlow.lean file:
/jukebox/norman/qanguyen/autoform/.venv/bin/python /jukebox/norman/qanguyen/autoform/agent/get_goal.py /jukebox/norman/qanguyen/autoform/LML/LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean 67 --project-path /jukebox/norman/qanguyen/autoform/LML

# Aligning blueprint with formalization after proving 
Modify [ntk.tex](file;vscode-remote://ssh-remote%2B7b22686f73744e616d65223a2273636f7474792e706e692e7072696e6365746f6e2e656475227d/jukebox/norman/qanguyen/autoform/LML/blueprint/src/chapters/ntk.tex)  to align with the formal proofs in /jukebox/norman/qanguyen/autoform/LML/LeanMachineLearning/Optimization/NTK. Add all the sublemmas and explain how they build together to prove the big theorems.

# Introduction
Work on the sorries in /jukebox/norman/qanguyen/autoform/LML/LeanMachineLearning/Optimization/Renormalization/Finpartition.lean
First think mathematically to provide an informal proof of the theorems before translating   
the informal argument into lean code.                                                        
If there are missing hypotheses then you can modify the file.                                
make sure that the theorems are faithful to the intentions of         /jukebox/norman/qanguyen/autoform/LML/blueprint/src/chapters/renormalization.tex             
and  /jukebox/norman/qanguyen/autoform/docs/Renormalization.md Search the current file, repository, and the `.lake/packages` directory for relevant         
definitions                                                                                  
and theorems. Create a ranked list of the relevant results found in the current              
file or in the directory or in Mathlib to help future agents, the theorem / definition name  
and where they can be found.                                                                 
                                                                                              
Consult the provided reference documentation in docs/ if it is available.                    
                                                                                              
Use `WebSearch` and `WebFetch` to research the mathematics behind this file from a           
variety of independent sources — textbooks, lecture notes, arXiv papers, nLab,               
Wikipedia, MathOverflow/Math.SE, and Mathlib documentation. Do not rely on a single          
result: cross-check any non-trivial claim, definition, or proof strategy against at          
least two independent sources where feasible, and note it explicitly if sources              
disagree. Prefer primary or authoritative references (textbooks, papers, nLab) over          
forum answers when they conflict.                                                            
                                                                                              
Be scholarly: every fact, definition, or proof idea drawn from the web must be cited         
inline next to the point it supports, e.g. "(Source: <title>, <url>)", so the claim          
can be independently verified. Do not assert something you found online without              
attributing it.                                                                              
                                                                                              
Be rigorous and truth-seeking in your work. You will be rewarded for accuracy.               
consult    /jukebox/norman/qanguyen/autoform/docs/lessons_learned.md                         
/jukebox/norman/qanguyen/autoform/docs/useful_mathlib.md    for what to do and               
/jukebox/norman/qanguyen/autoform/docs/hallucinated_mathlib.md     for what not to do Explain
how the error violated lessons_learned.md, be specific which lessons, explain how your new   
plan totally complies with lessons_learned.md                                                
Also develop reusable API to help with your proof. Ideally your proof won't be too long but  
will build from reusable and readable lemmas. Make sure to pay attention to code quality and 
model yourself on writing code that can be merged into Mathlib. You can run tests on your    
edits with `lake env lean [filename]`. If you develop API as reusable lemmas to help you with
your proof, it's OK to leave them as a sorry *only if* you cite where we can find an informal
proof (e.g. a URL or some other link) and also provide an informal proof in your own words.  
The library should accord with the principles of the broader LML (Lean Machine Learning)     
project, which you can see by reading the README in the LeanMachineLearning folder. It should
also reuse the existing infrastructure of LML if possible and propose refactors when         
appropriate to give the Lean code more generality, concision, and elegance.                  
**Do NOT** use git to revert commits. Edit the code that you have in front of you.        
When you encounter linters that are not declaration uses `sorry`, do not change my linter options, but fix the code to comply with the linter. 
You can use this tool to check the goal at a certain line: /jukebox/norman/qanguyen/autoform/.venv/bin/python /jukebox/norman/qanguyen/autoform/agent/get_goal.py <ABSOLUTE_FILE_PATH> <LINE_NUMBER> --project-path /jukebox/norman/qanguyen/autoform/LML
For example, to test it on line 67 of the MirrorFlow.lean file:
/jukebox/norman/qanguyen/autoform/.venv/bin/python /jukebox/norman/qanguyen/autoform/agent/get_goal.py /jukebox/norman/qanguyen/autoform/LML/LeanMachineLearning/Optimization/Lasso/MirrorFlow.lean 67 --project-path /jukebox/norman/qanguyen/autoform/LML

# Steering, incrementalism
I'd prefer if you edit the file more often because you are using up your context window very fast and we might   
lose your thinking. Also if you have a theorem that you believe is true, you should add it into the file with a  sorry but with a detailed informal comment explaining how to prove it. That way we can come back and prove it later.   

# Refactor and golf
create a plan to refactor and golf                                                                    
    /jukebox/norman/qanguyen/autoform/LML/LeanMachineLearning/Optimization/Approximation/Sampling.lean    
    consult /jukebox/norman/qanguyen/autoform/docs/GOLF_REFACTOR.md and                                   
    /jukebox/norman/qanguyen/autoform/docs/GOLF.md 