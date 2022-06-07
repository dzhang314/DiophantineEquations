module DZPolynomialAnalysis

export to_wolfram, find_height_reducing_transformation,
    has_real_root, is_positive_definite,
    has_unbounded_projection, has_unbounded_vieta_projection

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

function compute_height(expr, rules)
    monomials = weval(W"MonomialList"(expr))
    weights = weval(W"ReplaceAll"(monomials, rules))
    @assert weights.head == W"List"
    @assert all(w isa Int for w in weights.args)
    return sum([abs(w) for w in weights.args])
end

function candidate_transformations(num_vars::Int, radius::Int)
    vars = WOLFRAM_VARIABLES[num_vars]
    result = MathLink.WExpr[]
    for k = 1 : radius
        for i = 1 : num_vars
            push!(result, W"Rule"(vars[i], W"Plus"(vars[i], k)))
            push!(result, W"Rule"(vars[i], W"Subtract"(vars[i], k)))
        end
        for i = 1 : num_vars
            for j = 1 : num_vars
                if i != j
                    push!(result, W"Rule"(vars[i],
                        W"Plus"(vars[i], W"Times"(k, vars[j]))
                    ))
                    push!(result, W"Rule"(vars[i],
                        W"Subtract"(vars[i], W"Times"(k, vars[j]))
                    ))
                end
            end
        end
    end
    return result
end

function find_height_reducing_transformation(p::Polynomial{T, N, I},
                                             radius::Int) where {T, N, I}
    wp = to_wolfram(p)
    rules = W"List"([W"Rule"(var, 2) for var in WOLFRAM_VARIABLES[N]]...)
    height = compute_height(wp, rules)
    for transformation in candidate_transformations(N, radius)
        wpt = weval(W"ReplaceAll"(wp, transformation))
        if compute_height(wpt, rules) < height
            return transformation
        end
    end
    return nothing
end

################################################################################

function parse_bool(expr)
    if expr == W"True"
        return true
    elseif expr == W"False"
        return false
    else
        error()
    end
end

function has_real_root(p::Polynomial{T, N, I}) where {T, N, I}
    stmt = W"Exists"(WOLFRAM_VARIABLES[N], W"Equal"(to_wolfram(p), 0))
    return parse_bool(weval(W"Resolve"(stmt, W"Reals")))
end

function is_positive_definite(p::Polynomial{T, N, I}) where {T, N, I}
    stmt = W"ForAll"(WOLFRAM_VARIABLES[N], W"Greater"(to_wolfram(p), 0))
    return parse_bool(weval(W"Resolve"(stmt, W"Reals")))
end

function has_unbounded_projection(p::Polynomial{T, N, I}) where {T, N, I}
    vars = WOLFRAM_VARIABLES[N]
    stmt = W"ForAll"(W"T", W"Exists"(vars, W"And"(
        W"Equal"(to_wolfram(p), 0),
        [W"Greater"(W"Power"(var, 2), W"T") for var in vars]...
    )))
    return parse_bool(weval(W"Resolve"(stmt, W"Reals")))
end

function vieta_constraints(p::Polynomial{T, N, I}) where {T, N, I}
    wp = to_wolfram(p)
    result = MathLink.WExpr[]
    for var in WOLFRAM_VARIABLES[N]
        coeffs = weval(W"CoefficientList"(wp, var))
        @assert coeffs.head == W"List"
        if length(coeffs.args) == 3
            if coeffs.args[3] == 1
                push!(result, W"GreaterEqual"(
                    W"Power"(W"Plus"(coeffs.args[2], var), 2),
                    W"Power"(var, 2)
                ))
            elseif coeffs.args[3] == -1
                push!(result, W"GreaterEqual"(
                    W"Power"(W"Subtract"(coeffs.args[2], var), 2),
                    W"Power"(var, 2)
                ))
            end
        end
    end
    return result
end

function has_unbounded_vieta_projection(p::Polynomial{T, N, I}) where {T, N, I}
    vars = WOLFRAM_VARIABLES[N]
    stmt = W"ForAll"(W"T", W"Exists"(vars, W"And"(
        W"Equal"(to_wolfram(p), 0),
        vieta_constraints(p)...,
        [W"Greater"(W"Power"(var, 2), W"T") for var in vars]...
    )))
    return parse_bool(weval(W"Resolve"(stmt, W"Reals")))
end

# function is_integer_disjunction(expr, var::MathLink.WSymbol)
#     if expr == W"False"
#         return true
#     elseif (expr.head == W"Equal" &&
#             length(expr.args) == 2 &&
#             expr.args[1] == var)
#         return true
#     elseif expr.head == W"Or" && all(term.head == W"Equal" &&
#                                      length(term.args) == 2 &&
#                                      term.args[1] == var
#                                      for term in expr.args)
#         return true
#     else
#         return false
#     end
# end

# function parse_integer_disjunction(expr, var::MathLink.WSymbol)
#     if expr == W"False"
#         return Int[]
#     elseif (expr.head == W"Equal" &&
#             length(expr.args) == 2 &&
#             expr.args[1] == var)
#         return Int[expr.args[2]]
#     elseif expr.head == W"Or"
#         @assert all(term.head == W"Equal" &&
#                     length(term.args) == 2 &&
#                     term.args[1] == var
#                     for term in expr.args)
#         return Int[term.args[2] for term in expr.args]
#     else
#         error()
#     end
# end

# function integer_projection(p::Polynomial{T, N, I}, i::Int) where {T, N, I}
#     vars = WOLFRAM_VARIABLES[N]
#     result = weval(W"Reduce"(
#         W"Resolve"(
#             W"Exists"(deleteat!(copy(vars), i), W"Equal"(to_wolfram(p), 0)),
#             W"Reals"
#         ),
#         vars[i],
#         W"Integers"
#     ))
#     return parse_integer_disjunction(result, vars[i])
# end

# function is_unsolvable_by_projection(p::Polynomial{T, 2, I},
#                                      i::Int) where {T, I}
#     if has_unbounded_projection(p, i)
#         return false
#     end
#     vars = WOLFRAM_VARIABLES[2]
#     for n in integer_projection(p, i)
#         projection = weval(W"ReplaceAll"(
#             to_wolfram(p),
#             W"Rule"(vars[i], n)
#         ))
#         solutions = weval(W"SolveValues"(
#             W"Equal"(projection, 0),
#             vars[3 - i], # TODO: generalize to N > 2
#             W"Integers"
#         ))
#         @assert solutions.head == W"List"
#         if !isempty(solutions.args)
#             return false
#         end
#     end
#     return true
# end

# function is_unsolvable_by_projection(p::Polynomial{T, N, I}) where {T, N, I}
#     for i = 1 : N
#         if is_unsolvable_by_projection(p, i)
#             return true
#         end
#     end
#     return false
# end

# is_integral(::Int) = true
# is_integral(::MathLink.WSymbol) = true

# function is_integral(x::MathLink.WExpr)
#     if x.head == W"Rational" || x.head == W"Complex"
#         return false
#     elseif (x.head == W"Plus") || (x.head == W"Times")
#         return all(is_integral(arg) for arg in x.args)
#     elseif x.head == W"Power"
#         @assert length(x.args) == 2
#         return is_integral(x.args[1]) && (x.args[2] isa Int) && (x.args[2] >= 0)
#     else
#         println("unhandled case in is_integral: ", x)
#         error()
#     end
# end

# function is_unsolvable_by_asymptotic(p::Polynomial{T, 2, I},
#                                      x::MathLink.WSymbol,
#                                      y::MathLink.WSymbol) where {T, I}
#     branches = weval(W"SolveValues"(W"Equal"(to_wolfram(p), 0), y))
#     @assert branches.head == W"List"
#     for branch in branches.args
#         range = weval(W"FunctionRange"(branch, x, y))
#         integer_range = weval(W"Reduce"(range, y, W"Integers"))
#         if is_integer_disjunction(integer_range, y)
#             for n in parse_integer_disjunction(integer_range, y)
#                 equation = W"Equal"(branch, n)
#                 solutions = weval(W"SolveValues"(equation, x, W"Integers"))
#                 @assert solutions.head == W"List"
#                 if !isempty(solutions.args)
#                     return false
#                 end
#             end
#         else
#             asymptote = weval(W"Asymptotic"(branch, W"Rule"(x, W"Infinity")))
#             if !is_integral(asymptote)
#                 return false
#             end
#             range = weval(
#                 W"FunctionRange"(W"Subtract"(branch, asymptote), x, y)
#             )
#             integer_range = weval(W"Reduce"(range, y, W"Integers"))
#             if !is_integer_disjunction(integer_range, y)
#                 return false
#             end
#             for n in parse_integer_disjunction(integer_range, y)
#                 equation = W"Equal"(W"Subtract"(branch, asymptote), n)
#                 solutions = weval(W"SolveValues"(equation, x, W"Integers"))
#                 @assert solutions.head == W"List"
#                 if !isempty(solutions.args)
#                     return false
#                 end
#             end
#         end
#     end
#     return true
# end

# function is_unsolvable_by_asymptotic(p::Polynomial{T, 2, I}) where {T, I}
#     return (is_unsolvable_by_asymptotic(p, W"x", W"y") ||
#             is_unsolvable_by_asymptotic(p, W"y", W"x"))
# end

################################################################################

end # module DZPolynomialAnalysis
