library(digest)

# Rerun a block of code if 
# 1) The block of code has changed
# 2) The block of code contains dynamic variables that have changed since last being run

# The key to figuring out dependencies is that the dynamic variables snitch
# when they are being accessed, via add_depends().

globals <- new.env(parent=emptyenv())
globals$collecting_dependency_syms <- FALSE
globals$discovered_dependency_syms <- character(0)
globals$only_allow_dynamic_objects <- FALSE
globals$.dynamics <- list()

# Call this within the environment that should be forced to only use dynamic
# objects.  This can be helpful to prevent accidental creation of dynamic objects
# without using assign_dynamic
#only_allow_dynamic_objects <- function(flag)
#{
#    if (globals$only_allow_dynamic_objects)
#        return()
#
#    lockEnvironment(parent.frame())
#    globals$only_allow_dynamic_objects <- TRUE
#}


#print.dynamic <- function(x) {
#    dependency_syms <- attr(x, 'dependency_syms')
#    attributes(x) <- NULL
#    print(x)
#    if (length(dependency_names) == 0)
#        cat('No Dependencies.\n')
#    else
#        cat('Dependencies:', paste(dependency_names, collapse=', '), '\n')
#
#}

assign_dynamic <- function(sym, dyn, env)
{
    globals$.dynamics[[sym]] <- dyn

    fun <- local({
        function(x) {
            if (missing(x)) {
                add_depends(sym)
                dependencies <- globals$.dynamics[[sym]]$dependency_syms
                if (length(dependencies) > 0) cat('Depends on: ', paste(dependencies, collapse = ', '), '.\n', sep = '')
                globals$.dynamics[[sym]]$obj
            } else {
                stop('Dynamic objects can only be overwritten using assign_dynamic("', sym, '".')
            }
        }
    })

    makeActiveBinding(sym=sym, fun=fun, env=env)
}

hash <- function(...) digest::digest(list(...))

collect_dependency_syms <- function()
{
    globals$collecting_dependency_syms <- TRUE
}

deposit_dependency_syms <- function()
{
    globals$collecting_dependency_syms <- FALSE
    out <- globals$discovered_dependency_syms
    globals$discovered_dependency_syms <- character(0)

    unique(out)
}

add_depends <- function(x)
{
    if (globals$collecting_dependency_syms) 
        globals$discovered_dependency_syms <- c(x, globals$discovered_dependency_syms)
}

extract <- function(lst, name) sapply(lst, function(a) get(name, a))

get_candidates <- function(code)
{
    code_list <- extract(globals$.dynamics, 'code')
    matches <- as.logical(sapply(code_list, function(x) x == code))
    globals$.dynamics[matches]
}

#'   We have to track dependency_names and dependency_hashes because knowing
#'   the names of the dependencies of a given dynamic object lets us infer 
#'   the dependencies of the current dynamic object if the expressions are 
#'   identical.  
#'   
#'   "codehash" is a digest() of the literal expression
#'   "hash" is a digest() of the codehash plus the "hash"es of the dependency variables
#'
#'   Proof of Correctness:
#'   0) Axioms: 
#'        a) Blocks can only contain dynamic variables and functions that act 
#'        like true mathmatical functions (No state and will always return 
#'        same result if arguments are unchanged).  
#'        b) We rerun a block iff its hash has changed.  
#'   1) A block's current hash, h', will differ from the hash h when previously 
#'   run iff either the literal expression has changed or the 
#'   hash attribute of one of the dependent dynamic variables has changed.
#'   2) *The value of variable only changes if it's code, or the code of a 
#'   dependent variable changes.*  This change in code flows through to a change
#'   in the h' hash.  To see this, suppose that the value of a variable changes,
#'   but there were no code changes in the tree of variable dependencies.  That
#'   means that either one of the dependent blocks included a non-dynamic variable (contradiction)
#'   or there was a function that returned a different value given the same values (non-functional, contradiction).
#'
#'   The hash of an object changes if a) its code changes or b) the hash of a dependent variable changes.
#'   This logic recurses back to the ends of the dependency tree.
#'   The dependency tree always ends at a block with no dependent variables.
#' @export
`%=%` <- function(sym, expr)
{
    code <- substitute(expr)
    sym <- deparse(substitute(sym))

    # Find any dynamic data objects in evaluation environment that have the 
    # same expression
    candidates <- get_candidates(code)

    if (length(candidates) > 0) {

        # Now check if the dependencies have changed since any of these
        # potentially matching dynamic data objects were created
        for (can in candidates) {
            dependency_syms_old <- can$dependency_syms
            dependency_hashes_old <- can$dependency_hashes
            dependency_hashes_new <- extract(globals$.dynamics[dependency_syms_old], 'hash')

            if (all(dependency_hashes_old == dependency_hashes_new)) {
                if (can$sym == sym) {
                    message('Dependencies and code unchanged.')
                    return(invisible())
                } else {
                    can$sym <- sym
                    assign_dynamic(sym=sym, dyn=can, env=parent.frame())
                    message('Dependencies and code unchanged.')
                    return(invisible())
                }
            }
        }
    }

    collect_dependency_syms()
    on.exit(invisible(deposit_dependency_syms()))

    # Do the damn thing
    message('Running expression')
    obj <- expr

    dependency_syms <- deposit_dependency_syms()
    dependency_hashes <- extract(globals$.dynamics[dependency_syms], 'hash')

    dynamic <- list(
        obj = obj,
        sym = sym,
        code = code,
        dependency_syms = dependency_syms, 
        dependency_hashes = dependency_hashes,
        hash = hash(code, dependency_hashes))

    assign_dynamic(sym=sym, dyn=dynamic, env=parent.frame())

    invisible()
}

