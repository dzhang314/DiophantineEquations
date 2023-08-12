module DiophantinePolynomials

################################################################################

export Term, Polynomial

const Term{N} = Tuple{Int,NTuple{N,Int}}
const Polynomial{N} = Vector{Term{N}}

################################################################################

export has_constant_term, has_coprime_terms, has_linear_variable,
    is_positive_semidefinite, is_negative_semidefinite

function has_constant_term(p::Polynomial{N}) where {N}
    return any(all(iszero.(m)) && !iszero(c) for (c, m) in p)
end

function term_gcd(p::Polynomial{N}) where {N}
    coefficient_gcd = 0
    exponent_gcd = ntuple(_ -> typemax(Int), Val{N}())
    for (c, m) in p
        coefficient_gcd = gcd(coefficient_gcd, c)
        exponent_gcd = min.(exponent_gcd, m)
    end
    return (coefficient_gcd, exponent_gcd)
end

function has_coprime_terms(p::Polynomial{N}) where {N}
    (c, m) = term_gcd(p)
    return isone(c) && all(iszero.(m))
end

function has_linear_variable(p::Polynomial{N}, i::Int) where {N}
    @inbounds (_, m) = p[i]
    return all(
        all(iszero.(min.(m, n))) || (i == j)
        for (j, (_, n)) in enumerate(p)
    )
end

function has_linear_variable(p::Polynomial{N}) where {N}
    return any(
        any(isone.(m)) && has_linear_variable(p, i)
        for (i, (_, m)) in enumerate(p)
    )
end

function is_positive_semidefinite(p::Polynomial{N}) where {N}
    return all((c >= 0) && all(iseven, m) for (c, m) in p)
end

function is_negative_semidefinite(p::Polynomial{N}) where {N}
    return all((c <= 0) && all(iseven, m) for (c, m) in p)
end

precompile(has_constant_term, (Polynomial{1},))
precompile(has_constant_term, (Polynomial{2},))
precompile(has_constant_term, (Polynomial{3},))
precompile(has_constant_term, (Polynomial{4},))
precompile(has_constant_term, (Polynomial{5},))
precompile(has_coprime_terms, (Polynomial{1},))
precompile(has_coprime_terms, (Polynomial{2},))
precompile(has_coprime_terms, (Polynomial{3},))
precompile(has_coprime_terms, (Polynomial{4},))
precompile(has_coprime_terms, (Polynomial{5},))
precompile(has_linear_variable, (Polynomial{1},))
precompile(has_linear_variable, (Polynomial{2},))
precompile(has_linear_variable, (Polynomial{3},))
precompile(has_linear_variable, (Polynomial{4},))
precompile(has_linear_variable, (Polynomial{5},))
precompile(is_positive_semidefinite, (Polynomial{1},))
precompile(is_positive_semidefinite, (Polynomial{2},))
precompile(is_positive_semidefinite, (Polynomial{3},))
precompile(is_positive_semidefinite, (Polynomial{4},))
precompile(is_positive_semidefinite, (Polynomial{5},))
precompile(is_negative_semidefinite, (Polynomial{1},))
precompile(is_negative_semidefinite, (Polynomial{2},))
precompile(is_negative_semidefinite, (Polynomial{3},))
precompile(is_negative_semidefinite, (Polynomial{4},))
precompile(is_negative_semidefinite, (Polynomial{5},))

################################################################################

export load_polynomials

@inline is_digit(char::UInt8) = (UInt8('0') <= char <= UInt8('9'))
@inline is_letter(char::UInt8) = (UInt8('a') <= char <= UInt8('z'))
@inline is_sign(char::UInt8) = (char == UInt8('+')) | (char == UInt8('-'))
@inline is_space(char::UInt8) = (char == UInt8(' ')) | (0x09 <= char <= 0x0D)

function parse_integer(str::Array{UInt8}, i::Int, j::Int)
    result = 0
    @simd for k = i:j
        @inbounds result = 10 * result + Int(str[k] - UInt8('0'))
    end
    return result
end

function parse_coefficient(poly_str::Array{UInt8}, i::Int)
    n = length(poly_str)
    j = i
    while (1 <= j <= n) && is_digit(@inbounds poly_str[j])
        j += 1
    end
    if i == j
        return (j, 1)
    else
        return (j, parse_integer(poly_str, i, j - 1))
    end
end

function parse_exponent(poly_str::Array{UInt8}, i::Int)
    n = length(poly_str)
    j = i
    while (1 <= j <= n) && is_digit(@inbounds poly_str[j])
        j += 1
    end
    @assert i < j
    return (j, parse_integer(poly_str, i, j - 1))
end

function parse_power(::Val{N}, poly_str::Array{UInt8}, i::Int) where {N}
    @assert 1 <= N <= 26
    n = length(poly_str)
    @assert 1 <= i <= n
    @inbounds var = poly_str[i]
    if N <= 3
        @assert UInt8('x') <= var <= UInt8('x') + UInt8(N - 1)
    else
        @assert UInt8('a') <= var <= UInt8('a') + UInt8(N - 1)
    end
    var_index = Int(var - UInt8((N <= 3) ? 'x' : 'a')) + 1
    if 1 <= i + 1 <= n
        @inbounds caret = poly_str[i+1]
        if caret == UInt8('^')
            (j, exponent) = parse_exponent(poly_str, i + 2)
            return (j, var_index, exponent)
        end
    end
    return (i + 1, var_index, 1)
end

function parse_term(::Val{N}, poly_str::Array{UInt8}, i::Int) where {N}
    n = length(poly_str)
    (i, coefficient) = parse_coefficient(poly_str, i)
    exponents = ntuple(_ -> 0, Val{N}())
    while 1 <= i <= n && is_letter(@inbounds poly_str[i])
        (i, index, exponent) = parse_power(Val{N}(), poly_str, i)
        @inbounds exponents = Base.setindex(
            exponents,
            exponents[index] + exponent,
            index
        )
    end
    return (i, coefficient, exponents)
end

function parse_polynomial(::Val{N}, poly_str::Array{UInt8}, i::Int) where {N}
    n = length(poly_str)
    term_count = 0
    for c in poly_str
        if is_sign(c)
            term_count += 1
        end
    end
    if 1 <= i <= n
        @inbounds first_char = poly_str[i]
        if !is_sign(first_char)
            term_count += 1
        end
    end
    result = Polynomial{N}(undef, term_count)
    k = 0
    while 1 <= i <= n
        @inbounds next_char = poly_str[i]
        if next_char == UInt8('-')
            @assert 1 <= i + 1 <= n
            (i, coefficient, exponents) = parse_term(Val{N}(), poly_str, i + 1)
            result[k+=1] = (-coefficient, exponents)
        elseif next_char == UInt8('+')
            @assert 1 <= i + 1 <= n
            (i, coefficient, exponents) = parse_term(Val{N}(), poly_str, i + 1)
            result[k+=1] = (+coefficient, exponents)
        else
            @assert is_digit(next_char) || is_letter(next_char)
            (i, coefficient, exponents) = parse_term(Val{N}(), poly_str, i)
            result[k+=1] = (coefficient, exponents)
        end
    end
    return result
end

function parse_polynomial(::Val{N}, str::String) where {N}
    poly_str = Array{UInt8}(str)
    deleteat!(poly_str, is_space.(poly_str))
    return parse_polynomial(Val{N}(), poly_str, 1)
end

function load_polynomials(::Val{N}, path::String) where {N}
    result = Polynomial{N}[]
    for line in eachline(path)
        push!(result, parse_polynomial(Val{N}(), line))
    end
    return result
end

function load_polynomials(::Val{N}, paths::Vector{String}) where {N}
    result = Polynomial{N}[]
    for path in paths
        for line in eachline(path)
            push!(result, parse_polynomial(Val{N}(), line))
        end
    end
    return result
end

precompile(load_polynomials, (Val{1}, String))
precompile(load_polynomials, (Val{2}, String))
precompile(load_polynomials, (Val{3}, String))
precompile(load_polynomials, (Val{4}, String))
precompile(load_polynomials, (Val{5}, String))
precompile(load_polynomials, (Val{1}, Vector{String}))
precompile(load_polynomials, (Val{2}, Vector{String}))
precompile(load_polynomials, (Val{3}, Vector{String}))
precompile(load_polynomials, (Val{4}, Vector{String}))
precompile(load_polynomials, (Val{5}, Vector{String}))

################################################################################

import LaTeXStrings: LaTeXString

const CANONICAL_VARIABLES = Dict{Int,Vector{String}}(
    0 => [],
    1 => ["x"],
    2 => ["x", "y"],
    3 => ["x", "y", "z"],
    4 => ["a", "b", "c", "d"],
    5 => ["a", "b", "c", "d", "e"],
    6 => ["a", "b", "c", "d", "e", "f"],
    7 => ["a", "b", "c", "d", "e", "f", "g"],
    8 => ["a", "b", "c", "d", "e", "f", "g", "h"],
    9 => ["a", "b", "c", "d", "e", "f", "g", "h", "i"],
    10 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"],
    11 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k"],
    12 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l"],
    13 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m"],
    14 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n"],
    15 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o"],
    16 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p"],
    17 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q"],
    18 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r"],
    19 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s"],
    20 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t"],
    21 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u"],
    22 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v"],
    23 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w"],
    24 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x"],
    25 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y"],
    26 => ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l", "m", "n", "o", "p", "q", "r", "s", "t", "u", "v", "w", "x", "y", "z"]
)

function to_latex(c::Int, m::NTuple{N,Int}) where {N}
    if all(iszero.(m))
        return string(c)
    end
    vars = CANONICAL_VARIABLES[N]
    result = String[]
    if isone(c)
        # do nothing
    elseif isone(-c)
        push!(result, "-")
    else
        push!(result, string(c))
    end
    for (i, n) in enumerate(m)
        if isone(n)
            push!(result, vars[i])
        elseif !iszero(n)
            push!(result, vars[i])
            push!(result, "^")
            if 0 <= n <= 9
                push!(result, string(n))
            else
                push!(result, "{")
                push!(result, string(n))
                push!(result, "}")
            end
        end
    end
    return join(result)
end

function to_latex(p::Polynomial{N}) where {N}
    result = ["\$"]
    for (c, m) in p
        if !iszero(c)
            if length(result) == 1
                push!(result, to_latex(c, m))
            else
                if signbit(c)
                    push!(result, " - ")
                    push!(result, to_latex(-c, m))
                else
                    push!(result, " + ")
                    push!(result, to_latex(+c, m))
                end
            end
        end
    end
    if length(result) == 1
        push!(result, "0")
    end
    push!(result, "\$")
    return join(result)
end

function LaTeXString(p::Polynomial{N}) where {N}
    return LaTeXString(to_latex(p))
end

precompile(LaTeXString, (Polynomial{1},))
precompile(LaTeXString, (Polynomial{2},))
precompile(LaTeXString, (Polynomial{3},))
precompile(LaTeXString, (Polynomial{4},))
precompile(LaTeXString, (Polynomial{5},))

################################################################################

export evaluate

@inline function evaluate(p::Polynomial{N}, x::NTuple{N,T}) where {N,T}
    result = zero(T)
    for (c, m) in p
        result += *(T(c), Base.power_by_squaring.(x, m)...)
    end
    return result
end

################################################################################

export has_small_root

@inline function evaluate_small((c, m)::Term{N}, x::NTuple{N,Int8}) where {N}
    result = c
    for i = 1:N
        if iszero(x[i]) && !iszero(m[i])
            return 0
        end
        if signbit(x[i]) && isodd(m[i])
            result = -result
        end
        if !iszero(x[i]) && !isone(x[i]) && !isone(-x[i])
            result <<= m[i]
        end
    end
    return result
end

@inline function evaluate_small(p::Polynomial{N}, x::NTuple{N,Int8}) where {N}
    result = 0
    for term in p
        result += evaluate_small(term, x)
    end
    return result
end

function candidate_small_roots(::Val{N}) where {N}
    range = Int8(-2):Int8(+2)
    product = Iterators.product(ntuple(_ -> range, Val{N}())...)
    result = reshape(collect(product), :)
    return sort!(result; by=(x -> sum(abs.(x))))
end

function small_root_test(x::NTuple{N,Int8}) where {N}
    args = Expr(:tuple, [Expr(:call, :Int8, i) for i in x]...)
    test = Expr(:call, :iszero, Expr(:call, :evaluate_small, :p, args))
    return Expr(:if, test, Expr(:return, true))
end

@generated function has_small_root(p::Polynomial{N}) where {N}
    return Expr(:block,
        small_root_test.(candidate_small_roots(Val{N}()))...,
        Expr(:return, false)
    )
end

precompile(has_small_root, (Polynomial{1},))
precompile(has_small_root, (Polynomial{2},))
precompile(has_small_root, (Polynomial{3},))
precompile(has_small_root, (Polynomial{4},))
precompile(has_small_root, (Polynomial{5},))

################################################################################

export has_root_modulo

struct ModInt{T,W,N} <: Number
    value::T
end

@inline function Base.:+(x::ModInt{T,W,N}, y::ModInt{T,W,N}) where {T,W,N}
    @assert T(N) + T(N) < typemax(T)
    result = x.value + y.value
    return ModInt{T,W,N}(ifelse(result >= T(N), result - T(N), result))
end

@inline function Base.:-(x::ModInt{T,W,N}, y::ModInt{T,W,N}) where {T,W,N}
    @assert signed(T) == T
    result = x.value - y.value
    return ModInt{T,W,N}(ifelse(signbit(result), result + T(N), result))
end

@inline function Base.:*(x::ModInt{T,W,N}, y::ModInt{T,W,N}) where {T,W,N}
    result = (W(x.value) * W(y.value)) % W(N)
    return ModInt{T,W,N}(T(result))
end

@inline function Base.zero(::Type{ModInt{T,W,N}}) where {T,W,N}
    return ModInt{T,W,N}(zero(T))
end

@inline function Base.iszero(x::ModInt{T,W,N}) where {T,W,N}
    return iszero(x.value)
end

function has_root_modulo(p::Polynomial{N}, ::Val{K}) where {N,K}
    range = Int32(0):Int32(K - 1)
    return any(
        iszero(evaluate(p, ModInt{Int32,Int64,K}.(x)))
        for x in Iterators.product(ntuple(_ -> range, Val{N}())...)
    )
end

precompile(has_root_modulo, (Polynomial{1}, Val{2}))
precompile(has_root_modulo, (Polynomial{2}, Val{2}))
precompile(has_root_modulo, (Polynomial{3}, Val{2}))
precompile(has_root_modulo, (Polynomial{4}, Val{2}))
precompile(has_root_modulo, (Polynomial{5}, Val{2}))
precompile(has_root_modulo, (Polynomial{1}, Val{3}))
precompile(has_root_modulo, (Polynomial{2}, Val{3}))
precompile(has_root_modulo, (Polynomial{3}, Val{3}))
precompile(has_root_modulo, (Polynomial{4}, Val{3}))
precompile(has_root_modulo, (Polynomial{5}, Val{3}))
precompile(has_root_modulo, (Polynomial{1}, Val{4}))
precompile(has_root_modulo, (Polynomial{2}, Val{4}))
precompile(has_root_modulo, (Polynomial{3}, Val{4}))
precompile(has_root_modulo, (Polynomial{4}, Val{4}))
precompile(has_root_modulo, (Polynomial{5}, Val{4}))
precompile(has_root_modulo, (Polynomial{1}, Val{5}))
precompile(has_root_modulo, (Polynomial{2}, Val{5}))
precompile(has_root_modulo, (Polynomial{3}, Val{5}))
precompile(has_root_modulo, (Polynomial{4}, Val{5}))
precompile(has_root_modulo, (Polynomial{5}, Val{5}))

################################################################################

export load_nontrivial_polynomials

function load_nontrivial_polynomials(::Val{N}, path::String) where {N}
    result = Polynomial{N}[]
    for line in eachline(path)
        p = parse_polynomial(Val{N}(), line)
        if (has_constant_term(p) &&
            has_coprime_terms(p) &&
            !has_linear_variable(p) &&
            !is_positive_semidefinite(p) &&
            !is_negative_semidefinite(p) &&
            !has_small_root(p) &&
            has_root_modulo(p, Val{2}()) &&
            has_root_modulo(p, Val{3}()) &&
            has_root_modulo(p, Val{4}()) &&
            has_root_modulo(p, Val{5}()))
            push!(result, p)
        end
    end
    return result
end

function load_nontrivial_polynomials(::Val{N}, paths::Vector{String}) where {N}
    result = Polynomial{N}[]
    for path in paths
        for line in eachline(path)
            p = parse_polynomial(Val{N}(), line)
            if (has_constant_term(p) &&
                has_coprime_terms(p) &&
                !has_linear_variable(p) &&
                !is_positive_semidefinite(p) &&
                !is_negative_semidefinite(p) &&
                !has_small_root(p) &&
                has_root_modulo(p, Val{2}()) &&
                has_root_modulo(p, Val{3}()) &&
                has_root_modulo(p, Val{4}()) &&
                has_root_modulo(p, Val{5}()))
                push!(result, p)
            end
        end
    end
    return result
end

precompile(load_nontrivial_polynomials, (Val{1}, String))
precompile(load_nontrivial_polynomials, (Val{2}, String))
precompile(load_nontrivial_polynomials, (Val{3}, String))
precompile(load_nontrivial_polynomials, (Val{4}, String))
precompile(load_nontrivial_polynomials, (Val{5}, String))
precompile(load_nontrivial_polynomials, (Val{1}, Vector{String}))
precompile(load_nontrivial_polynomials, (Val{2}, Vector{String}))
precompile(load_nontrivial_polynomials, (Val{3}, Vector{String}))
precompile(load_nontrivial_polynomials, (Val{4}, Vector{String}))
precompile(load_nontrivial_polynomials, (Val{5}, Vector{String}))



end # module DiophantinePolynomials
