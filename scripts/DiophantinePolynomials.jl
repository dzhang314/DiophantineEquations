module DiophantinePolynomials

############################################################### TYPE DEFINITIONS

export DiophantinePolynomial

struct DiophantinePolynomial{N}
    terms::Vector{Tuple{Int,NTuple{N,Int}}}
end

##################################################################### EVALUATION

export find_root

@inline function (p::DiophantinePolynomial{N})(x::NTuple{N,T}) where {N,T}
    result = zero(T)
    for (c, m) in p.terms
        result += *(c % T, Base.power_by_squaring.(x, m)...)
    end
    return result
end

function find_root(
    p::DiophantinePolynomial{N},
    points::Vector{NTuple{N,T}}
) where {N,T}
    for x in points
        if iszero(p(x)) && iszero(p(BigInt.(x)))
            return x
        end
    end
    return nothing
end

#################################################### STRUCTURAL PROPERTY TESTING

export has_constant_term, has_coprime_terms, has_linear_variable,
    is_positive_definite, is_negative_definite

function has_constant_term(p::DiophantinePolynomial{N}) where {N}
    return any(all(iszero.(m)) && !iszero(c) for (c, m) in p.terms)
end

precompile(has_constant_term, (DiophantinePolynomial{1},))
precompile(has_constant_term, (DiophantinePolynomial{2},))
precompile(has_constant_term, (DiophantinePolynomial{3},))
precompile(has_constant_term, (DiophantinePolynomial{4},))
precompile(has_constant_term, (DiophantinePolynomial{5},))

@inline function term_gcd(p::DiophantinePolynomial{N}) where {N}
    coefficient_gcd = 0
    exponent_gcd = ntuple(_ -> typemax(Int), Val{N}())
    for (c, m) in p.terms
        coefficient_gcd = gcd(coefficient_gcd, c)
        exponent_gcd = min.(exponent_gcd, m)
    end
    return (coefficient_gcd, exponent_gcd)
end

function has_coprime_terms(p::DiophantinePolynomial{N}) where {N}
    (c, m) = term_gcd(p)
    return isone(c) && all(iszero.(m))
end

precompile(has_coprime_terms, (DiophantinePolynomial{1},))
precompile(has_coprime_terms, (DiophantinePolynomial{2},))
precompile(has_coprime_terms, (DiophantinePolynomial{3},))
precompile(has_coprime_terms, (DiophantinePolynomial{4},))
precompile(has_coprime_terms, (DiophantinePolynomial{5},))

@inline function has_linear_variable(
    p::DiophantinePolynomial{N}, i::Int
) where {N}
    @inbounds (_, m) = p.terms[i]
    return all(
        all(iszero.(min.(m, n))) || (i == j)
        for (j, (_, n)) in enumerate(p.terms)
    )
end

function has_linear_variable(p::DiophantinePolynomial{N}) where {N}
    return any(
        any(isone.(m)) && has_linear_variable(p, i)
        for (i, (_, m)) in enumerate(p.terms)
    )
end

precompile(has_linear_variable, (DiophantinePolynomial{1},))
precompile(has_linear_variable, (DiophantinePolynomial{2},))
precompile(has_linear_variable, (DiophantinePolynomial{3},))
precompile(has_linear_variable, (DiophantinePolynomial{4},))
precompile(has_linear_variable, (DiophantinePolynomial{5},))

@inline function is_positive_semidefinite(
    p::DiophantinePolynomial{N}
) where {N}
    return all((c >= 0) && all(iseven, m) for (c, m) in p.terms)
end

function is_positive_definite(p::DiophantinePolynomial{N}) where {N}
    return is_positive_semidefinite(p) && has_constant_term(p)
end

precompile(is_positive_definite, (DiophantinePolynomial{1},))
precompile(is_positive_definite, (DiophantinePolynomial{2},))
precompile(is_positive_definite, (DiophantinePolynomial{3},))
precompile(is_positive_definite, (DiophantinePolynomial{4},))
precompile(is_positive_definite, (DiophantinePolynomial{5},))

@inline function is_negative_semidefinite(
    p::DiophantinePolynomial{N}
) where {N}
    return all((c <= 0) && all(iseven, m) for (c, m) in p.terms)
end

function is_negative_definite(p::DiophantinePolynomial{N}) where {N}
    return is_negative_semidefinite(p) && has_constant_term(p)
end

precompile(is_negative_definite, (DiophantinePolynomial{1},))
precompile(is_negative_definite, (DiophantinePolynomial{2},))
precompile(is_negative_definite, (DiophantinePolynomial{3},))
precompile(is_negative_definite, (DiophantinePolynomial{4},))
precompile(is_negative_definite, (DiophantinePolynomial{5},))

######################################################################## PARSING

@inline is_ascii_digit(c::UInt8) = (UInt8('0') <= c <= UInt8('9'))
@inline is_ascii_letter(c::UInt8) = (UInt8('a') <= c <= UInt8('z'))
@inline is_ascii_sign(c::UInt8) = (c == UInt8('+')) | (c == UInt8('-'))
@inline is_ascii_space(c::UInt8) = (c == UInt8(' ')) | (0x09 <= c <= 0x0D)
@inline is_ignored(c::UInt8) = is_ascii_space(c) | (c == UInt8('*'))

function parse_integer_unsafe(s::Base.CodeUnits, i::Int, j::Int)
    result = 0
    @simd for k = i:j
        @inbounds result = 10 * result + Int(s[k] - UInt8('0'))
    end
    return result
end

function parse_coefficient(s::Base.CodeUnits, i::Int)
    n = length(s)
    while (i <= n) && is_ignored(@inbounds s[i])
        i += 1
    end
    j = i
    while (j <= n) && is_ascii_digit(@inbounds s[j])
        j += 1
    end
    if i < j
        return (j, parse_integer_unsafe(s, i, j - 1))
    else
        return (j, 1)
    end
end

function parse_exponent(s::Base.CodeUnits, i::Int)
    n = length(s)
    while (i <= n) && is_ignored(@inbounds s[i])
        i += 1
    end
    j = i
    while (j <= n) && is_ascii_digit(@inbounds s[j])
        j += 1
    end
    @assert i < j
    return (j, parse_integer_unsafe(s, i, j - 1))
end

function parse_power(::Val{N}, s::Base.CodeUnits, i::Int) where {N}
    n = length(s)
    @inbounds variable = s[i]
    if 1 <= N <= 3
        @assert UInt8('x') <= variable <= UInt8('x') + UInt8(N - 1)
    else
        @assert 1 <= N <= 26
        @assert UInt8('a') <= variable <= UInt8('a') + UInt8(N - 1)
    end
    variable_index = Int(variable - UInt8((1 <= N <= 3) ? 'x' : 'a')) + 1
    i += 1
    while (i <= n) && is_ignored(@inbounds s[i])
        i += 1
    end
    if i <= n
        @inbounds caret = s[i]
        if caret == UInt8('^')
            (j, exponent) = parse_exponent(s, i + 1)
            return (j, variable_index, exponent)
        end
    end
    return (i, variable_index, 1)
end

function parse_term(::Val{N}, s::Base.CodeUnits, i::Int) where {N}
    n = length(s)
    (i, coefficient) = parse_coefficient(s, i)
    exponents = ntuple(_ -> 0, Val{N}())
    while true
        while (i <= n) && is_ignored(@inbounds s[i])
            i += 1
        end
        if (i > n) || !is_ascii_letter(@inbounds s[i])
            break
        end
        (i, variable_index, exponent) = parse_power(Val{N}(), s, i)
        @inbounds exponents = Base.setindex(
            exponents,
            exponents[variable_index] + exponent,
            variable_index
        )
    end
    return (i, coefficient, exponents)
end

function count_terms(s::Base.CodeUnits)
    term_count = 0
    for c in s
        if is_ascii_sign(c)
            term_count += 1
        end
    end
    n = length(s)
    i = 1
    while (i <= n) && is_ignored(@inbounds s[i])
        i += 1
    end
    if (i <= n) && !is_ascii_sign(@inbounds s[i])
        term_count += 1
    end
    return term_count
end

function DiophantinePolynomial{N}(s::Base.CodeUnits) where {N}
    n = length(s)
    terms = Vector{Tuple{Int,NTuple{N,Int}}}(undef, count_terms(s))
    i = 1
    k = 0
    while true
        while (i <= n) && is_ignored(@inbounds s[i])
            i += 1
        end
        if i > n
            break
        end
        @inbounds next_char = s[i]
        if next_char == UInt8('-')
            @assert 1 <= i + 1 <= n
            (i, coefficient, exponents) = parse_term(Val{N}(), s, i + 1)
            @inbounds terms[k+=1] = (-coefficient, exponents)
        elseif next_char == UInt8('+')
            @assert 1 <= i + 1 <= n
            (i, coefficient, exponents) = parse_term(Val{N}(), s, i + 1)
            @inbounds terms[k+=1] = (+coefficient, exponents)
        else
            @assert k == 0
            @assert is_ascii_digit(next_char) || is_ascii_letter(next_char)
            (i, coefficient, exponents) = parse_term(Val{N}(), s, i)
            @inbounds terms[k+=1] = (coefficient, exponents)
        end
    end
    return DiophantinePolynomial{N}(terms)
end

DiophantinePolynomial{N}(s::AbstractString) where {N} =
    DiophantinePolynomial{N}(codeunits(s))

precompile(DiophantinePolynomial{1}, (String,))
precompile(DiophantinePolynomial{2}, (String,))
precompile(DiophantinePolynomial{3}, (String,))
precompile(DiophantinePolynomial{4}, (String,))
precompile(DiophantinePolynomial{5}, (String,))

####################################################################### PRINTING

function print_variable(io::IO, ::Val{N}, i::Int) where {N}
    if 1 <= N <= 3
        print(io, 'x' + (i - 1))
    else
        @assert 1 <= N <= 26
        print(io, 'a' + (i - 1))
    end
    return nothing
end

function print_term(
    io::IO, coefficient::Int, exponents::NTuple{N,Int};
    stars::Bool
) where {N}
    if all(iszero.(exponents))
        print(io, coefficient)
    else
        needs_star = false
        if isone(-coefficient)
            print(io, '-')
        elseif !isone(coefficient)
            print(io, coefficient)
            needs_star = true
        end
        for (i, exponent) in enumerate(exponents)
            if isone(exponent)
                if stars && needs_star
                    print(io, '*')
                end
                print_variable(io, Val{N}(), i)
                needs_star = true
            elseif !iszero(exponent)
                if stars && needs_star
                    print(io, '*')
                end
                print_variable(io, Val{N}(), i)
                print(io, '^')
                print(io, exponent)
                needs_star = true
            end
        end
    end
    return nothing
end

function Base.print(
    io::IO, p::DiophantinePolynomial{N};
    stars::Bool=false
) where {N}
    first_term = true
    for (c, m) in p.terms
        if !iszero(c)
            if first_term
                print_term(io, c, m; stars=stars)
            else
                if signbit(c)
                    print(io, " - ")
                    print_term(io, -c, m; stars=stars)
                else
                    print(io, " + ")
                    print_term(io, +c, m; stars=stars)
                end
            end
            first_term = false
        end
    end
    if first_term
        print(io, '0')
    end
    return nothing
end

function Base.show(io::IO, p::DiophantinePolynomial{N}) where {N}
    print(io, "DiophantinePolynomial{")
    print(io, N)
    print(io, "}(\"")
    print(io, p; stars=true)
    print(io, "\")")
    return nothing
end

################################################################################

end # module DiophantinePolynomials
