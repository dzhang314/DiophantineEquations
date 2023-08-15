module SymbolicAnalysis

using MathLink: @W_str, WSymbol, WExpr, weval
using DiophantinePolynomials: DiophantinePolynomial

################################################################################

const IntExpr = Union{Int,WSymbol,WExpr}

const WOLFRAM_ALPHABET = [
    W"a", W"b", W"c", W"d", W"e", W"f", W"g", W"h", W"i",
    W"j", W"k", W"l", W"m", W"n", W"o", W"p", W"q", W"r",
    W"s", W"t", W"u", W"v", W"w", W"x", W"y", W"z"
]

const WOLFRAM_RADIUS = W"R"
const WOLFRAM_NEGATIVE_RADIUS = W"Times"(-1, WOLFRAM_RADIUS)

################################################################################

function wolfram_variables(::Val{N}) where {N}
    @assert 1 <= N <= 26
    base = (1 <= N <= 26) ? 23 : 0
    return ntuple(i -> (@inbounds WOLFRAM_ALPHABET[base+i]), Val{N}())
end

function wolfram_bool(s::WSymbol)
    if s.name == "True"
        return true
    else
        @assert s.name == "False"
        return false
    end
end

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

################################################################################

export has_real_root

function has_real_root_expr(p::DiophantinePolynomial{N}) where {N}
    vars = wolfram_variables(Val{N}())
    return W"Exists"(W"List"(vars...),
        W"Equal"(wolfram_polynomial(p, vars), 0)
    )
end

has_real_root(p::DiophantinePolynomial{N}) where {N} =
    wolfram_bool(weval(W"Resolve"(has_real_root_expr(p), W"Reals")))

################################################################################

export has_compact_locus

function has_compact_locus_expr(p::DiophantinePolynomial{N}) where {N}
    vars = wolfram_variables(Val{N}())
    clauses = ntuple(
        i -> W"LessEqual"(WOLFRAM_NEGATIVE_RADIUS, vars[i], WOLFRAM_RADIUS),
        Val{N}()
    )
    return W"Exists"(WOLFRAM_RADIUS, W"ForAll"(W"List"(vars...),
        W"Implies"(W"Equal"(wolfram_polynomial(p, vars), 0), W"And"(clauses...))
    ))
end

function has_compact_locus_expr(
    p::DiophantinePolynomial{N}, radius::Int
) where {N}
    vars = wolfram_variables(Val{N}())
    clauses = ntuple(
        i -> W"LessEqual"(-radius, vars[i], radius),
        Val{N}()
    )
    return W"ForAll"(W"List"(vars...),
        W"Implies"(W"Equal"(wolfram_polynomial(p, vars), 0), W"And"(clauses...))
    )
end

has_compact_locus(p::DiophantinePolynomial{N}) where {N} =
    wolfram_bool(weval(W"Resolve"(has_compact_locus_expr(p), W"Reals")))

has_compact_locus(p::DiophantinePolynomial{N}, radius::Int) where {N} =
    wolfram_bool(weval(W"Resolve"(has_compact_locus_expr(p, radius), W"Reals")))

################################################################################

export has_compact_projection

function has_compact_projection_expr(p::DiophantinePolynomial{N}) where {N}
    vars = wolfram_variables(Val{N}())
    clauses = ntuple(
        i -> W"LessEqual"(WOLFRAM_NEGATIVE_RADIUS, vars[i], WOLFRAM_RADIUS),
        Val{N}()
    )
    return W"Exists"(WOLFRAM_RADIUS, W"ForAll"(W"List"(vars...),
        W"Implies"(W"Equal"(wolfram_polynomial(p, vars), 0), W"Or"(clauses...))
    ))
end

function has_compact_projection_expr(
    p::DiophantinePolynomial{N}, radius::Int
) where {N}
    vars = wolfram_variables(Val{N}())
    clauses = ntuple(
        i -> W"LessEqual"(-radius, vars[i], radius),
        Val{N}()
    )
    return W"ForAll"(W"List"(vars...),
        W"Implies"(W"Equal"(wolfram_polynomial(p, vars), 0), W"Or"(clauses...))
    )
end

has_compact_projection(p::DiophantinePolynomial{N}) where {N} =
    wolfram_bool(weval(W"Resolve"(has_compact_projection_expr(p), W"Reals")))

has_compact_projection(p::DiophantinePolynomial{N}, radius::Int) where {N} =
    wolfram_bool(weval(
        W"Resolve"(has_compact_projection_expr(p, radius), W"Reals")
    ))

################################################################################

end # module SymbolicAnalysis
