module SymbolicAnalysis

using MathLink: @W_str, WSymbol, WExpr, weval
using DiophantinePolynomials: DiophantinePolynomial

###################################################################### CONSTANTS

const IntExpr = Union{Int,WSymbol,WExpr}

const WOLFRAM_ALPHABET = [
    W"a", W"b", W"c", W"d", W"e", W"f", W"g", W"h", W"i",
    W"j", W"k", W"l", W"m", W"n", W"o", W"p", W"q", W"r",
    W"s", W"t", W"u", W"v", W"w", W"x", W"y", W"z"
]

const WOLFRAM_RADIUS = W"R"
const WOLFRAM_NEGATIVE_RADIUS = W"Times"(-1, WOLFRAM_RADIUS)

############################################################## UTILITY FUNCTIONS

delete(xs::NTuple{N,T}, i::Int) where {N,T} = (xs[1:i-1]..., xs[i+1:end]...)

function wolfram_variables(::Val{N}) where {N}
    @assert 1 <= N <= 26
    if 1 <= N <= 3
        return ntuple(i -> (@inbounds WOLFRAM_ALPHABET[23+i]), Val{N}())
    else
        return ntuple(i -> (@inbounds WOLFRAM_ALPHABET[i]), Val{N}())
    end
end

function parse_bool(s::WSymbol)
    if s.name == "True"
        return true
    else
        @assert s.name == "False"
        return false
    end
end

function wolfram_or(clauses::Vector{WExpr})
    if isempty(clauses)
        return W"False"
    elseif isone(length(clauses))
        return only(clauses)
    else
        return W"Or"(clauses...)
    end
end

function wolfram_or(clauses::NTuple{N,WExpr}) where {N}
    if iszero(N)
        return W"False"
    elseif isone(N)
        return only(clauses)
    else
        return W"Or"(clauses...)
    end
end

function wolfram_and(clauses::Vector{WExpr})
    if isempty(clauses)
        return W"True"
    elseif isone(length(clauses))
        return only(clauses)
    else
        return W"And"(clauses...)
    end
end

function wolfram_and(clauses::NTuple{N,WExpr}) where {N}
    if iszero(N)
        return W"True"
    elseif isone(N)
        return only(clauses)
    else
        return W"And"(clauses...)
    end
end

function wolfram_sum(factors::Vector{IntExpr})
    if isempty(factors)
        return 0
    elseif length(factors) == 1
        return only(factors)
    else
        return W"Plus"(factors...)
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

wolfram_exists(vars::NTuple{N,WSymbol}, predicate::WExpr) where {N} =
    W"Exists"(W"List"(vars...), predicate)

wolfram_all(vars::NTuple{N,WSymbol}, predicate::WExpr) where {N} =
    W"ForAll"(W"List"(vars...), predicate)

wolfram_resolve(stmt::WExpr) = parse_bool(weval(W"Resolve"(stmt, W"Reals")))

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
    return wolfram_sum(terms)
end

##################################################################### REAL ROOTS

export has_real_roots

function has_real_roots_expr(p::DiophantinePolynomial{N}) where {N}
    vars = wolfram_variables(Val{N}())
    return wolfram_exists(vars, W"Equal"(wolfram_polynomial(p, vars), 0))
end

has_real_roots(p::DiophantinePolynomial{N}) where {N} =
    wolfram_resolve(has_real_roots_expr(p))

################################################################## COMPACT ROOTS

export has_compact_roots

function has_compact_roots_expr(p::DiophantinePolynomial{N}) where {N}
    vars = wolfram_variables(Val{N}())
    clauses = ntuple(
        i -> W"LessEqual"(WOLFRAM_NEGATIVE_RADIUS, vars[i], WOLFRAM_RADIUS),
        Val{N}()
    )
    return W"Exists"(WOLFRAM_RADIUS, wolfram_all(vars, W"Implies"(
        W"Equal"(wolfram_polynomial(p, vars), 0),
        wolfram_and(clauses)
    )))
end

function has_compact_roots_expr(
    p::DiophantinePolynomial{N}, radius::Int
) where {N}
    vars = wolfram_variables(Val{N}())
    clauses = ntuple(
        i -> W"LessEqual"(-radius, vars[i], radius),
        Val{N}()
    )
    return wolfram_all(vars, W"Implies"(
        W"Equal"(wolfram_polynomial(p, vars), 0),
        wolfram_and(clauses)
    ))
end

has_compact_roots(p::DiophantinePolynomial{N}) where {N} =
    wolfram_resolve(has_compact_roots_expr(p))

has_compact_roots(p::DiophantinePolynomial{N}, radius::Int) where {N} =
    wolfram_resolve(has_compact_roots_expr(p, radius))

################################################################################

export has_compact_univariate_projection

function has_compact_univariate_projection_expr(
    p::DiophantinePolynomial{N}
) where {N}
    vars = wolfram_variables(Val{N}())
    clauses = ntuple(
        i -> wolfram_and([
            W"LessEqual"(WOLFRAM_NEGATIVE_RADIUS, v, WOLFRAM_RADIUS)
            for v in delete(vars, i)
        ]),
        Val{N}()
    )
    return W"Exists"(WOLFRAM_RADIUS, wolfram_all(vars, W"Implies"(
        W"Equal"(wolfram_polynomial(p, vars), 0),
        wolfram_or(clauses)
    )))
end

function has_compact_univariate_projection_expr(
    p::DiophantinePolynomial{N}, radius::Int
) where {N}
    vars = wolfram_variables(Val{N}())
    clauses = ntuple(
        i -> wolfram_and([
            W"LessEqual"(-radius, v, radius)
            for v in delete(vars, i)
        ]),
        Val{N}()
    )
    return wolfram_all(vars, W"Implies"(
        W"Equal"(wolfram_polynomial(p, vars), 0),
        wolfram_or(clauses)
    ))
end

has_compact_univariate_projection(p::DiophantinePolynomial{N}) where {N} =
    wolfram_resolve(has_compact_univariate_projection_expr(p))

has_compact_univariate_projection(
    p::DiophantinePolynomial{N}, radius::Int
) where {N} =
    wolfram_resolve(has_compact_univariate_projection_expr(p, radius))

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
    parse_bool(weval(W"Resolve"(has_compact_projection_expr(p), W"Reals")))

has_compact_projection(p::DiophantinePolynomial{N}, radius::Int) where {N} =
    parse_bool(weval(
        W"Resolve"(has_compact_projection_expr(p, radius), W"Reals")
    ))

################################################################################

end # module SymbolicAnalysis
