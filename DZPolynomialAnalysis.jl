module DZPolynomialAnalysis

export dedup, to_wolfram, has_real_root, is_positive_definite

using DZPolynomials
using MathLink

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

end # module DZPolynomialAnalysis
