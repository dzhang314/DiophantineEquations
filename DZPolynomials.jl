module DZPolynomials

export Monomial, Polynomial, coefficient_of,
    find_root, has_root_modulo, uses_variable, uses_all_variables,
    has_linear_variable, has_divisible_variable, has_coprime_coefficients,
    is_positive_semidefinite, is_negative_semidefinite,
    is_elliptic_curve, is_weierstrass_elliptic_curve, weierstrass_coefficients,
    to_string, to_latex,
    apply_transposition, apply_cycle, apply_negation, apply_signflip,
    apply_transposition!, apply_cycle!, apply_negation!, apply_signflip!,
    incr_partition!, integer_partitions,
    HomogeneousPolynomialIterator, get_polynomial, incr_polynomial!,
    l1_ball

################################################################################

const Monomial{T,N,I} = Pair{NTuple{N,I},T}

const Polynomial{T,N,I} = Vector{Monomial{T,N,I}}

function coefficient_of(p::Polynomial{T,N,I}, m::NTuple{N,I}) where {T,N,I}
    for (n, c) in p
        if m == n
            return c
        end
    end
    return zero(T)
end

function find_root(p::Polynomial{T,N,I}, xs::Vector{NTuple{N,X}}) where {T,N,I,X}
    for x in xs
        if iszero(p(x))
            return x
        end
    end
    return nothing
end

function has_linear_variable(p::Polynomial{T,N,I}, i::Int) where {T,N,I}
    @inbounds (n, _) = p[i]
    @inbounds for (j, (m, _)) in enumerate(p)
        if i != j && !all(iszero.(min.(m, n)))
            return false
        end
    end
    return true
end

function has_linear_variable(p::Polynomial{T,N,I}) where {T,N,I}
    @inbounds for (i, (m, _)) in enumerate(p)
        if any(isone.(m)) && has_linear_variable(p, i)
            return true
        end
    end
    return false
end

################################################################################

function is_elliptic_curve_1(p::Polynomial{T,2,I}) where {T,I}
    _zero = zero(I)
    _one = one(I)
    _two = _one + _one
    _three = _two + _one
    found_cubic = false
    found_quadratic = false
    for ((i, j), c) in p
        if (i, j) == (_three, _zero)
            if !iszero(c)
                found_cubic = true
            end
        elseif (i, j) == (_zero, _two)
            if !iszero(c)
                found_quadratic = true
            end
        elseif i + j > _two
            return false
        end
    end
    return found_cubic && found_quadratic
end

function is_elliptic_curve_2(p::Polynomial{T,2,I}) where {T,I}
    _zero = zero(I)
    _one = one(I)
    _two = _one + _one
    _three = _two + _one
    found_cubic = false
    found_quadratic = false
    for ((i, j), c) in p
        if (i, j) == (_zero, _three)
            if !iszero(c)
                found_cubic = true
            end
        elseif (i, j) == (_two, _zero)
            if !iszero(c)
                found_quadratic = true
            end
        elseif i + j > _two
            return false
        end
    end
    return found_cubic && found_quadratic
end

is_elliptic_curve(p::Polynomial{T,2,I}) where {T,I} =
    is_elliptic_curve_1(p) || is_elliptic_curve_2(p)
is_elliptic_curve(p::Polynomial{T,N,I}) where {T,N,I} = false

function is_weierstrass_elliptic_curve(p::Polynomial{T,2,I}) where {T,I}
    _zero = zero(I)
    _one = one(I)
    _two = _one + _one
    _three = _two + _one
    found_cubic = false
    found_quadratic = false
    for ((i, j), c) in p
        if (i, j) == (_three, _zero)
            if !isone(c)
                return false
            end
            found_cubic = true
        elseif (i, j) == (_zero, _two)
            if !isone(c) && !isone(-c)
                return false
            end
            found_quadratic = true
        elseif i + j > _two
            return false
        end
    end
    return found_cubic && found_quadratic
end

is_weierstrass_elliptic_curve(p::Polynomial{T,N,I}) where {T,N,I} = false

function weierstrass_coefficients(p::Polynomial{T,2,I}) where {T,I}
    _zero = zero(I)
    _one = one(I)
    _two = _one + _one
    c = coefficient_of(p, (_zero, _two))
    if isone(c)
        return (
            -coefficient_of(p, (_one, _one)),
            -coefficient_of(p, (_two, _zero)),
            coefficient_of(p, (_zero, _one)),
            coefficient_of(p, (_one, _zero)),
            -coefficient_of(p, (_zero, _zero))
        )
    elseif isone(-c)
        return (
            -coefficient_of(p, (_one, _one)),
            coefficient_of(p, (_two, _zero)),
            -coefficient_of(p, (_zero, _one)),
            coefficient_of(p, (_one, _zero)),
            coefficient_of(p, (_zero, _zero))
        )
    else
        error()
    end
end

################################################################################

function to_string((m, c)::Monomial{T,N,I}) where {T,N,I}
    if all(iszero(n) for n in m)
        return string(c)
    end
    vars = CANONICAL_VARIABLES[N]
    result = String[]
    needs_star = false
    if isone(c)
        # do nothing
    elseif isone(-c)
        push!(result, "-")
    else
        push!(result, string(c))
        needs_star = true
    end
    for (i, n) in enumerate(m)
        if isone(n)
            if needs_star
                push!(result, "*")
            end
            push!(result, vars[i])
            needs_star = true
        elseif !iszero(n)
            if needs_star
                push!(result, "*")
            end
            push!(result, vars[i])
            push!(result, "^")
            push!(result, string(n))
            needs_star = true
        end
    end
    return join(result)
end

function to_string(p::Polynomial{T,N,I}) where {T,N,I}
    result = String[]
    for (m, c) in p
        if !iszero(c)
            if isempty(result)
                push!(result, to_string(m => c))
            else
                if signbit(c)
                    push!(result, " - ")
                    push!(result, to_string(m => -c))
                else
                    push!(result, " + ")
                    push!(result, to_string(m => c))
                end
            end
        end
    end
    if isempty(result)
        return string(zero(T))
    else
        return join(result)
    end
end

################################################################################

function incr_partition!(x::Vector{T}) where {T}
    _one = one(T)
    @inbounds begin
        n = length(x)
        if n <= 1
            return false
        end
        xn = x[n]
        xn1 = x[n-1]
        if !iszero(xn1)
            x[n-1] = xn1 - _one
            x[n] = xn + _one
            return true
        end
        i = n - 2
        while !iszero(i)
            xi = x[i]
            if !iszero(xi)
                x[i] = xi - _one
                if iszero(xn)
                    x[i+1] += _one
                else
                    x[i+1] += xn + _one
                    x[n] = zero(T)
                end
                return true
            end
            i -= 1
        end
        return false
    end
end

function integer_partitions(n::T, len::Int) where {T}
    result = Vector{T}[]
    if iszero(n) && iszero(len)
        push!(result, T[])
    elseif !signbit(n) && len >= 1
        p = zeros(T, len)
        @inbounds p[1] = n
        while true
            push!(result, copy(p))
            if !incr_partition!(p)
                break
            end
        end
    end
    return result
end

################################################################################

struct SignedPartitionIterator{T}
    dense_partition::Vector{T}
    sparse_partition::Vector{Pair{Int,T}}
    sign_pattern::Array{UInt,0}
    function SignedPartitionIterator(n::T, len::Int) where {T}
        dense_partition = zeros(T, len)
        if n > 0 && len > 0
            @inbounds dense_partition[1] = n
            sparse_partition = [1 => n]
        else
            sparse_partition = Pair{Int,Int}[]
        end
        sign_pattern = fill(UInt(0))
        return new{T}(dense_partition, sparse_partition, sign_pattern)
    end
end

function incr_partition!(it::SignedPartitionIterator{T}) where {T}
    dense = it.dense_partition
    sparse = it.sparse_partition
    s = it.sign_pattern[] + 1
    if s < (UInt(1) << length(sparse))
        it.sign_pattern[] = s
        return true
    else
        it.sign_pattern[] = UInt(0)
        if !incr_partition!(dense)
            return false
        end
        empty!(sparse)
        for (i, c) in enumerate(dense)
            if !iszero(c)
                push!(sparse, i => c)
            end
        end
        @assert length(sparse) < 8 * sizeof(UInt)
        return true
    end
end

function get_partition(::Val{N}, it::SignedPartitionIterator{T}) where {N,T}
    result = ntuple(_ -> zero(T), Val{N}())
    s = it.sign_pattern[]
    @inbounds for (i, c) in it.sparse_partition
        result = Base.setindex(result, ifelse(iseven(s), c, -c), i)
        s >>= 1
    end
    return result
end

function l1_ball(::Val{N}, radius::T) where {N,T}
    result = NTuple{N,T}[]
    it = SignedPartitionIterator(radius, N)
    while true
        push!(result, get_partition(Val{N}(), it))
        if !incr_partition!(it)
            break
        end
    end
    return result
end

################################################################################

end # module DZPolynomials
