% Generated by roxygen2: do not edit by hand
% Please edit documentation in R/blocks.R
\name{\%=\%}
\alias{\%=\%}
\title{We have to track dependency_names and dependency_hashes because knowing
  the names of the dependencies of a given dynamic object lets us infer 
  the dependencies of the current dynamic object if the expressions are 
  identical.  
  
  "codehash" is a digest() of the literal expression
  "hash" is a digest() of the codehash plus the "hash"es of the dependency variables}
\usage{
sym \%=\% expr
}
\description{
Proof of Correctness:
  0) Axioms: 
       a) Blocks can only contain dynamic variables and functions that act 
       like true mathmatical functions (No state and will always return 
       same result if arguments are unchanged).  
       b) We rerun a block iff its hash has changed.  
  1) A block's current hash, h', will differ from the hash h when previously 
  run iff either the literal expression has changed or the 
  hash attribute of one of the dependent dynamic variables has changed.
  2) *The value of variable only changes if it's code, or the code of a 
  dependent variable changes.*  This change in code flows through to a change
  in the h' hash.  To see this, suppose that the value of a variable changes,
  but there were no code changes in the tree of variable dependencies.  That
  means that either one of the dependent blocks included a non-dynamic variable (contradiction)
  or there was a function that returned a different value given the same values (non-functional, contradiction).
}
\details{
The hash of an object changes if a) its code changes or b) the hash of a dependent variable changes.
  This logic recurses back to the ends of the dependency tree.
  The dependency tree always ends at a block with no dependent variables.
}
