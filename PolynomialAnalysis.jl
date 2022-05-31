module PolynomialAnalysis

export dedup, to_wolfram, has_real_root, is_positive_definite

using DZPolynomials
using Graphs
using MathLink

################################################################################

function dedup(polys::Vector{Polynomial{T, N, I}},
               ::Type{I}, # needed to disambiguate when N = 0
               verbose::Bool=false) where {T, N, I}
    if verbose
        println("Deduplicating $(length(polys)) polynomials.")
        flush(stdout)
    end
    index_dict = Dict{Polynomial{T, N, I}, Int}()
    for (i, p) in enumerate(polys)
        index_dict[sort(p)] = i
    end
    if verbose
        println("Constructing symmetry map.")
        flush(stdout)
    end
    last_print = time_ns()
    g = SimpleGraph(index_dict.count)
    for (i, p_original) in enumerate(polys)
        p = copy(p_original)
        add_edge!(g, i, index_dict[sort!(apply_transposition!(p))])
        apply_transposition!(p)
        add_edge!(g, i, index_dict[sort!(apply_negation!(p))])
        apply_negation!(p)
        add_edge!(g, i, index_dict[sort!(apply_signflip!(p))])
        apply_signflip!(p)
        add_edge!(g, i, index_dict[sort!(apply_cycle!(p))])
        if verbose && (time_ns() >= last_print + 1000000000)
            println("Computed symmetries of $i polynomials.")
            flush(stdout)
            last_print += 1000000000
        end
    end
    if verbose
        println("Finding connected components of symmetry graph.")
        flush(stdout)
    end
    result = Polynomial{T, N, I}[]
    @inbounds for comp in connected_components(g)
        push!(result, polys[comp[1]])
    end
    if verbose
        println("Finished deduplicating.")
        flush(stdout)
    end
    return result
end

################################################################################

const WOLFRAM_VARIABLES = Dict(
    k => MathLink.WSymbol.(v)
    for (k, v) in DZPolynomials.CANONICAL_VARIABLES
)

function to_wolfram(p::Polynomial{T, N, I}) where {T, N, I}
    vars = WOLFRAM_VARIABLES[N]
    terms = Any[]
    for (m, c) in p
        factors = Any[]
        if !isone(c)
            push!(factors, Int(c))
        end
        for (i, n) in enumerate(m)
            if isone(n)
                push!(factors, vars[i])
            elseif !iszero(n)
                push!(factors, W"Power"(vars[i], Int(n)))
            end
        end
        if isempty(factors)
            push!(terms, 1)
        elseif length(factors) == 1
            push!(terms, factors[1])
        else
            push!(terms, W"Times"(factors...))
        end
    end
    if isempty(terms)
        return 0
    elseif length(terms) == 1
        return terms[1]
    else
        return W"Plus"(terms...)
    end
end

################################################################################

function has_real_root(p::Polynomial{T, N, I}) where {T, N, I}
    result = weval(W"Reduce"(
        W"Exists"(WOLFRAM_VARIABLES[N], W"Equal"(to_wolfram(p), 0)),
        W"Reals"
    ))
    if result == W"True"
        return true
    elseif result == W"False"
        return false
    else
        error()
    end
end

function is_positive_definite(p::Polynomial{T, N, I}) where {T, N, I}
    result = weval(W"Reduce"(
        W"ForAll"(WOLFRAM_VARIABLES[N], W"Greater"(to_wolfram(p), 0)),
        W"Reals"
    ))
    if result == W"True"
        return true
    elseif result == W"False"
        return false
    else
        error()
    end
end

################################################################################

end # module PolynomialAnalysis
