module SymbolicAnalysis

using MathLink: @W_str, WSymbol, WExpr
using DiophantinePolynomials: DiophantinePolynomial

export has_compact_projection_expr

const IntExpr = Union{Int,WSymbol,WExpr}

const WOLFRAM_ALPHABET = [
    W"a", W"b", W"c", W"d", W"e", W"f", W"g", W"h", W"i",
    W"j", W"k", W"l", W"m", W"n", W"o", W"p", W"q", W"r",
    W"s", W"t", W"u", W"v", W"w", W"x", W"y", W"z"
]

const WOLFRAM_RADIUS = W"R"
const WOLFRAM_NEGATIVE_RADIUS = W"Times"(-1, WOLFRAM_RADIUS)

function wolfram_product(factors::Vector{IntExpr})
    if isempty(factors)
        return 1
    elseif length(factors) == 1
        return only(factors)
    else
        return W"Times"(factors...)
    end
end

function wolfram_polynomial(
    p::DiophantinePolynomial{N},
    variables::NTuple{N,WSymbol}
) where {N}
    terms = IntExpr[]
    for (c, m) in p.terms
        if !iszero(c)
            factors = IntExpr[]
            if !isone(c)
                push!(factors, c)
            end
            for i = 1:N
                if !iszero(m[i])
                    if isone(m[i])
                        push!(factors, variables[i])
                    else
                        push!(factors, W"Power"(variables[i], m[i]))
                    end
                end
            end
            push!(terms, wolfram_product(factors))
        end
    end
    return W"Plus"(terms...)
end

function has_compact_projection_expr(p::DiophantinePolynomial{N}) where {N}
    @assert 1 <= N <= 26
    base = (1 <= N <= 26) ? 23 : 0
    vars = ntuple(i -> (@inbounds WOLFRAM_ALPHABET[base+i]), Val{N}())
    clauses = ntuple(
        i -> W"LessEqual"(WOLFRAM_NEGATIVE_RADIUS, vars[i], WOLFRAM_RADIUS),
        Val{N}()
    )
    return W"Exists"(WOLFRAM_RADIUS, W"ForAll"(W"List"(vars...),
        W"Implies"(W"Equal"(wolfram_polynomial(p, vars), 0), W"Or"(clauses...))
    ))
end

end # module SymbolicAnalysis
